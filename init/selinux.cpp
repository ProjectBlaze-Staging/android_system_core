/*
 * Copyright (C) 2017 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// This file contains the functions that initialize SELinux during boot as well as helper functions
// for SELinux operation for init.

// When the system boots, there is no SEPolicy present and init is running in the kernel domain.
// Init loads the SEPolicy from the file system, restores the context of /system/bin/init based on
// this SEPolicy, and finally exec()'s itself to run in the proper domain.

// The SEPolicy on Android comes in two variants: monolithic and split.

// The monolithic policy variant is for legacy non-treble devices that contain a single SEPolicy
// file located at /sepolicy and is directly loaded into the kernel SELinux subsystem.

// The split policy is for supporting treble devices.  It splits the SEPolicy across files on
// /system/etc/selinux (the 'plat' portion of the policy) and /vendor/etc/selinux (the 'vendor'
// portion of the policy).  This is necessary to allow the system image to be updated independently
// of the vendor image, while maintaining contributions from both partitions in the SEPolicy.  This
// is especially important for VTS testing, where the SEPolicy on the Google System Image may not be
// identical to the system image shipped on a vendor's device.

// The split SEPolicy is loaded as described below:
// 1) There is a precompiled SEPolicy located at either /vendor/etc/selinux/precompiled_sepolicy or
//    /odm/etc/selinux/precompiled_sepolicy if odm parition is present.  Stored along with this file
//    are the sha256 hashes of the parts of the SEPolicy on /system, /system_ext and /product that
//    were used to compile this precompiled policy.  The system partition contains a similar sha256
//    of the parts of the SEPolicy that it currently contains.  Symmetrically, system_ext and
//    product paritition contain sha256 hashes of their SEPolicy.  The init loads this
//    precompiled_sepolicy directly if and only if the hashes along with the precompiled SEPolicy on
//    /vendor or /odm match the hashes for system, system_ext and product SEPolicy, respectively.
// 2) If these hashes do not match, then either /system or /system_ext or /product (or some of them)
//    have been updated out of sync with /vendor (or /odm if it is present) and the init needs to
//    compile the SEPolicy.  /system contains the SEPolicy compiler, secilc, and it is used by the
//    OpenSplitPolicy() function below to compile the SEPolicy to a temp directory and load it.
//    That function contains even more documentation with the specific implementation details of how
//    the SEPolicy is compiled if needed.

#include "selinux.h"

#include <android/api-level.h>
#include <dirent.h>
#include <elf.h>
#include <fcntl.h>
#include <linux/audit.h>
#include <linux/netlink.h>
#include <stdlib.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/xattr.h>
#include <unistd.h>

#include <unordered_map>
#include <unordered_set>

#include <android-base/chrono_utils.h>
#include <android-base/file.h>
#include <android-base/logging.h>
#include <android-base/parseint.h>
#include <android-base/result.h>
#include <android-base/strings.h>
#include <android-base/unique_fd.h>
#include <android/avf_cc_flags.h>
#include <com_android_apex_flags.h>
#include <fs_avb/fs_avb.h>
#include <fs_mgr.h>
#include <fs_mgr_overlayfs.h>
#include <genfslabelsversion.h>
#include <libgsi/libgsi.h>
#include <libsnapshot/snapshot.h>
#include <selinux/android.h>

#include "block_dev_initializer.h"
#include "debug_ramdisk.h"
#include "reboot_utils.h"
#include "second_stage_resources.h"
#include "snapuserd_transition.h"
#include "util.h"
#include "ota_utils.h"

using namespace std::string_literals;

using android::base::ParseInt;
using android::base::Timer;
using android::base::unique_fd;
using android::fs_mgr::AvbHandle;
using android::snapshot::SnapshotManager;

namespace android {
namespace init {

namespace {

enum EnforcingStatus { SELINUX_PERMISSIVE, SELINUX_ENFORCING };

EnforcingStatus StatusFromProperty() {
    std::string value;
    if (android::fs_mgr::GetKernelCmdline("androidboot.selinux", &value) && value == "permissive") {
        return SELINUX_PERMISSIVE;
    }
    if (android::fs_mgr::GetBootconfig("androidboot.selinux", &value) && value == "permissive") {
        return SELINUX_PERMISSIVE;
    }
    return SELINUX_ENFORCING;
}

bool IsEnforcing() {
    if (ALLOW_PERMISSIVE_SELINUX) {
        return StatusFromProperty() == SELINUX_ENFORCING;
    }
    return true;
}

bool ReadFirstLine(const char* file, std::string* line) {
    line->clear();

    std::string contents;
    if (!android::base::ReadFileToString(file, &contents, true /* follow symlinks */)) {
        return false;
    }
    std::istringstream in(contents);
    std::getline(in, *line);
    return true;
}

Result<std::string> FindPrecompiledSplitPolicy() {
    std::string precompiled_sepolicy;
    // If there is an odm partition, precompiled_sepolicy will be in
    // odm/etc/selinux. Otherwise it will be in vendor/etc/selinux.
    static constexpr const char vendor_precompiled_sepolicy[] =
            "/vendor/etc/selinux/precompiled_sepolicy";
    static constexpr const char odm_precompiled_sepolicy[] =
            "/odm/etc/selinux/precompiled_sepolicy";
    if (access(odm_precompiled_sepolicy, R_OK) == 0) {
        precompiled_sepolicy = odm_precompiled_sepolicy;
    } else if (access(vendor_precompiled_sepolicy, R_OK) == 0) {
        precompiled_sepolicy = vendor_precompiled_sepolicy;
    } else {
        return ErrnoError() << "No precompiled sepolicy at " << vendor_precompiled_sepolicy;
    }

    // Use precompiled sepolicy only when all corresponding hashes are equal.
    std::vector<std::pair<std::string, std::string>> sepolicy_hashes{
            {"/system/etc/selinux/plat_sepolicy_and_mapping.sha256",
             precompiled_sepolicy + ".plat_sepolicy_and_mapping.sha256"},
            {"/system_ext/etc/selinux/system_ext_sepolicy_and_mapping.sha256",
             precompiled_sepolicy + ".system_ext_sepolicy_and_mapping.sha256"},
            {"/product/etc/selinux/product_sepolicy_and_mapping.sha256",
             precompiled_sepolicy + ".product_sepolicy_and_mapping.sha256"},
    };

    for (const auto& [actual_id_path, precompiled_id_path] : sepolicy_hashes) {
        // Both of them should exist or both of them shouldn't exist.
        if (access(actual_id_path.c_str(), R_OK) != 0) {
            if (access(precompiled_id_path.c_str(), R_OK) == 0) {
                return Error() << precompiled_id_path << " exists but " << actual_id_path
                               << " doesn't";
            }
            continue;
        }

        std::string actual_id;
        if (!ReadFirstLine(actual_id_path.c_str(), &actual_id)) {
            return ErrnoError() << "Failed to read " << actual_id_path;
        }

        std::string precompiled_id;
        if (!ReadFirstLine(precompiled_id_path.c_str(), &precompiled_id)) {
            return ErrnoError() << "Failed to read " << precompiled_id_path;
        }

        if (actual_id.empty() || actual_id != precompiled_id) {
            return Error() << actual_id_path << " and " << precompiled_id_path << " differ";
        }
    }

    return precompiled_sepolicy;
}

bool GetVendorMappingVersion(std::string* plat_vers) {
    if (!ReadFirstLine("/vendor/etc/selinux/plat_sepolicy_vers.txt", plat_vers)) {
        PLOG(ERROR) << "Failed to read /vendor/etc/selinux/plat_sepolicy_vers.txt";
        return false;
    }
    if (plat_vers->empty()) {
        LOG(ERROR) << "No version present in plat_sepolicy_vers.txt";
        return false;
    }
    return true;
}

constexpr const char plat_policy_cil_file[] = "/system/etc/selinux/plat_sepolicy.cil";

bool IsSplitPolicyDevice() {
    return access(plat_policy_cil_file, R_OK) != -1;
}

std::optional<const char*> GetUserdebugPlatformPolicyFile() {
    // See if we need to load userdebug_plat_sepolicy.cil instead of plat_sepolicy.cil.
    const char* force_debuggable_env = getenv("INIT_FORCE_DEBUGGABLE");
    if (force_debuggable_env && "true"s == force_debuggable_env && AvbHandle::IsDeviceUnlocked()) {
        const std::vector<const char*> debug_policy_candidates = {
#if INSTALL_DEBUG_POLICY_TO_SYSTEM_EXT == 1
            "/system_ext/etc/selinux/userdebug_plat_sepolicy.cil",
#endif
            kDebugRamdiskSEPolicy,
        };
        for (const char* debug_policy : debug_policy_candidates) {
            if (access(debug_policy, F_OK) == 0) {
                return debug_policy;
            }
        }
    }
    return std::nullopt;
}

struct PolicyFile {
    unique_fd fd;
    std::string path;
};

static void CollectCilDefinedTypes(const std::string& path,
                                   std::unordered_set<std::string>* out_types) {
    if (path.empty() || access(path.c_str(), R_OK) != 0) return;
    std::string content;
    if (!android::base::ReadFileToString(path, &content)) return;
    const char* prefixes[] = {"(type ", "(typeattribute "};
    for (const char* prefix : prefixes) {
        size_t plen = strlen(prefix);
        size_t pos = 0;
        while ((pos = content.find(prefix, pos)) != std::string::npos) {
            size_t start = pos + plen;
            while (start < content.size() && (content[start] == ' ' || content[start] == '\t')) {
                ++start;
            }
            size_t end = start;
            while (end < content.size() && content[end] != ')' && content[end] != ' ' &&
                   content[end] != '\t' && content[end] != '\n' && content[end] != '\r') {
                ++end;
            }
            if (end > start) {
                out_types->emplace(content.substr(start, end - start));
            }
            pos = end;
        }
    }
}

static bool SynthesizeLegacyVendorMapping(const std::string& vend_plat_vers,
                                          const std::string& plat_cil,
                                          const std::string& sys_ext_cil,
                                          const std::string& product_cil,
                                          const std::string& vendor_pub_cil,
                                          const std::string& out_mapping_path) {
    std::string pub_content;
    if (!android::base::ReadFileToString(vendor_pub_cil, &pub_content)) {
        return false;
    }

    std::string vers_underscored = android::base::StringReplace(vend_plat_vers, ".", "_", true);
    std::string suffix = "_" + vers_underscored;

    std::unordered_set<std::string> known_types;
    CollectCilDefinedTypes(plat_cil, &known_types);
    CollectCilDefinedTypes(sys_ext_cil, &known_types);
    CollectCilDefinedTypes(product_cil, &known_types);

    // Harvest 31.0 mapping aliases if present (handles types renamed between 30.0/31.0 and ToT)
    std::unordered_map<std::string, std::string> map_31;
    std::string cil_31;
    if (android::base::ReadFileToString("/system/etc/selinux/mapping/31.0.cil", &cil_31)) {
        const std::string kTag = "(typeattributeset ";
        size_t pos = 0;
        while ((pos = cil_31.find(kTag, pos)) != std::string::npos) {
            size_t s1 = pos + kTag.size();
            size_t e1 = cil_31.find(' ', s1);
            if (e1 == std::string::npos) break;
            std::string attr = cil_31.substr(s1, e1 - s1);
            if (android::base::EndsWith(attr, "_31_0")) {
                size_t lp = cil_31.find('(', e1);
                size_t rp = (lp != std::string::npos) ? cil_31.find(')', lp + 1) : std::string::npos;
                if (lp != std::string::npos && rp != std::string::npos && rp > lp + 1) {
                    std::string base = attr.substr(0, attr.size() - 5);
                    std::string target = android::base::Trim(cil_31.substr(lp + 1, rp - lp - 1));
                    if (!target.empty() && target.find(' ') == std::string::npos) {
                        map_31[base] = target;
                    }
                }
            }
            pos = e1;
        }
    }

    std::string out;
    out.reserve(160 * 1024);
    std::unordered_set<std::string> emitted_stubs;

    const std::string kAttrPrefix = "(typeattribute ";
    size_t pos = 0;
    while ((pos = pub_content.find(kAttrPrefix, pos)) != std::string::npos) {
        size_t start = pos + kAttrPrefix.size();
        while (start < pub_content.size() && pub_content[start] == ' ') ++start;
        size_t end = start;
        while (end < pub_content.size() && pub_content[end] != ')' && pub_content[end] != ' ' &&
               pub_content[end] != '\n' && pub_content[end] != '\r') {
            ++end;
        }
        if (end > start) {
            std::string attr = pub_content.substr(start, end - start);
            if (attr.size() > suffix.size() && android::base::EndsWith(attr, suffix)) {
                std::string base = attr.substr(0, attr.size() - suffix.size());
                std::string target = base;
                auto it31 = map_31.find(base);
                if (it31 != map_31.end()) {
                    target = it31->second;
                }
                if (known_types.find(target) == known_types.end() &&
                    emitted_stubs.insert(target).second) {
                    out += "(type " + target + ")\n";
                    out += "(roletype object_r " + target + ")\n";
                }
                out += "(typeattributeset " + attr + " (" + target + "))\n";
            }
        }
        pos = end;
    }

    out += "(allow domain ashmem_libcutils_device (chr_file (open)))\n";
    return android::base::WriteStringToFile(out, out_mapping_path, 0600, 0, 0);
}

bool OpenSplitPolicy(PolicyFile* policy_file) {
    // IMPLEMENTATION NOTE: Split policy consists of three or more CIL files:
    // * platform -- policy needed due to logic contained in the system image,
    // * vendor -- policy needed due to logic contained in the vendor image,
    // * mapping -- mapping policy which helps preserve forward-compatibility of non-platform policy
    //   with newer versions of platform policy.
    // * (optional) policy needed due to logic on product, system_ext, or odm images.
    // secilc is invoked to compile the above three policy files into a single monolithic policy
    // file. This file is then loaded into the kernel.

    const auto userdebug_plat_sepolicy = GetUserdebugPlatformPolicyFile();
    const bool use_userdebug_policy = userdebug_plat_sepolicy.has_value();
    if (use_userdebug_policy) {
        LOG(INFO) << "Using userdebug system sepolicy " << *userdebug_plat_sepolicy;
    }

    // Load precompiled policy from vendor image, if a matching policy is found there. The policy
    // must match the platform policy on the system image.
    // use_userdebug_policy requires compiling sepolicy with userdebug_plat_sepolicy.cil.
    // Thus it cannot use the precompiled policy from vendor image.
    if (!use_userdebug_policy) {
        if (auto res = FindPrecompiledSplitPolicy(); res.ok()) {
            unique_fd fd(open(res->c_str(), O_RDONLY | O_CLOEXEC | O_BINARY));
            if (fd != -1) {
                policy_file->fd = std::move(fd);
                policy_file->path = std::move(*res);
                return true;
            }
        } else {
            LOG(INFO) << res.error();
        }
    }
    // No suitable precompiled policy could be loaded

    LOG(INFO) << "Compiling SELinux policy";

    // We store the output of the compilation on /dev because this is the most convenient tmpfs
    // storage mount available this early in the boot sequence.
    char compiled_sepolicy[] = "/dev/sepolicy.XXXXXX";
    unique_fd compiled_sepolicy_fd(mkostemp(compiled_sepolicy, O_CLOEXEC));
    if (compiled_sepolicy_fd < 0) {
        PLOG(ERROR) << "Failed to create temporary file " << compiled_sepolicy;
        return false;
    }

    // Determine which mapping file to include
    std::string vend_plat_vers;
    if (!GetVendorMappingVersion(&vend_plat_vers)) {
        return false;
    }
    std::string plat_mapping_file("/system/etc/selinux/mapping/" + vend_plat_vers + ".cil");

    std::string plat_compat_cil_file("/system/etc/selinux/mapping/" + vend_plat_vers +
                                     ".compat.cil");
    if (access(plat_compat_cil_file.c_str(), F_OK) == -1) {
        plat_compat_cil_file.clear();
    }

    std::string system_ext_policy_cil_file("/system_ext/etc/selinux/system_ext_sepolicy.cil");
    if (access(system_ext_policy_cil_file.c_str(), F_OK) == -1) {
        system_ext_policy_cil_file.clear();
    }

    std::string system_ext_mapping_file("/system_ext/etc/selinux/mapping/" + vend_plat_vers +
                                        ".cil");
    if (access(system_ext_mapping_file.c_str(), F_OK) == -1) {
        system_ext_mapping_file.clear();
    }

    std::string system_ext_compat_cil_file("/system_ext/etc/selinux/mapping/" + vend_plat_vers +
                                           ".compat.cil");
    if (access(system_ext_compat_cil_file.c_str(), F_OK) == -1) {
        system_ext_compat_cil_file.clear();
    }

    std::string product_policy_cil_file("/product/etc/selinux/product_sepolicy.cil");
    if (access(product_policy_cil_file.c_str(), F_OK) == -1) {
        product_policy_cil_file.clear();
    }

    std::string product_mapping_file("/product/etc/selinux/mapping/" + vend_plat_vers + ".cil");
    if (access(product_mapping_file.c_str(), F_OK) == -1) {
        product_mapping_file.clear();
    }

    std::string vendor_policy_cil_file("/vendor/etc/selinux/vendor_sepolicy.cil");
    if (access(vendor_policy_cil_file.c_str(), F_OK) == -1) {
        LOG(ERROR) << "Missing " << vendor_policy_cil_file;
        return false;
    }

    std::string plat_pub_versioned_cil_file("/vendor/etc/selinux/plat_pub_versioned.cil");
    if (access(plat_pub_versioned_cil_file.c_str(), F_OK) == -1) {
        LOG(ERROR) << "Missing " << plat_pub_versioned_cil_file;
        return false;
    }

    // Legacy Treble vendor fallback (e.g. API 28-30 vendors like Redmi Note 11 'spes' where
    // /system/etc/selinux/mapping/30.0.cil is absent in Android 17). Never runs on 31.0+ / 202404+.
    std::string synthesized_mapping_file;
    if (access(plat_mapping_file.c_str(), F_OK) == -1) {
        synthesized_mapping_file = "/dev/compat_mapping_" + vend_plat_vers + ".cil";
        const std::string effective_plat_cil =
                use_userdebug_policy ? std::string(*userdebug_plat_sepolicy)
                                     : std::string(plat_policy_cil_file);
        if (SynthesizeLegacyVendorMapping(vend_plat_vers, effective_plat_cil,
                                          system_ext_policy_cil_file, product_policy_cil_file,
                                          plat_pub_versioned_cil_file, synthesized_mapping_file)) {
            LOG(INFO) << "Synthesized SELinux compatibility mapping for vendor " << vend_plat_vers;
            plat_mapping_file = synthesized_mapping_file;
        } else {
            synthesized_mapping_file.clear();
        }
    }

    // odm_sepolicy.cil is default but optional.
    std::string odm_policy_cil_file("/odm/etc/selinux/odm_sepolicy.cil");
    if (access(odm_policy_cil_file.c_str(), F_OK) == -1) {
        odm_policy_cil_file.clear();
    }
    const std::string version_as_string = std::to_string(SEPOLICY_VERSION);

    std::vector<std::string> genfs_cil_files;

    int vendor_genfs_version = get_genfs_labels_version();
    std::string genfs_cil_file =
            std::format("/system/etc/selinux/plat_sepolicy_genfs_{}.cil", vendor_genfs_version);
    if (access(genfs_cil_file.c_str(), F_OK) != 0) {
        if (vendor_genfs_version >= 202504) {
            LOG(ERROR) << "Missing " << genfs_cil_file;
            return false;
        }
        LOG(INFO) << "Missing " << genfs_cil_file << "; skipping";
        genfs_cil_file.clear();
    } else {
        LOG(INFO) << "Using " << genfs_cil_file << " for genfs labels";
    }

    // clang-format off
    std::vector<const char*> compile_args {
        "/system/bin/secilc",
        use_userdebug_policy ? *userdebug_plat_sepolicy : plat_policy_cil_file,
        "-m", "-M", "true", "-G", "-N", "-v",
        "-c", version_as_string.c_str(),
        plat_mapping_file.c_str(),
        "-o", compiled_sepolicy,
        // We don't care about file_contexts output by the compiler
        "-f", "/sys/fs/selinux/null",  // /dev/null is not yet available
    };
    // clang-format on

    if (!plat_compat_cil_file.empty()) {
        compile_args.push_back(plat_compat_cil_file.c_str());
    }
    if (!system_ext_policy_cil_file.empty()) {
        compile_args.push_back(system_ext_policy_cil_file.c_str());
    }
    if (!system_ext_mapping_file.empty()) {
        compile_args.push_back(system_ext_mapping_file.c_str());
    }
    if (!system_ext_compat_cil_file.empty()) {
        compile_args.push_back(system_ext_compat_cil_file.c_str());
    }
    if (!product_policy_cil_file.empty()) {
        compile_args.push_back(product_policy_cil_file.c_str());
    }
    if (!product_mapping_file.empty()) {
        compile_args.push_back(product_mapping_file.c_str());
    }
    if (!plat_pub_versioned_cil_file.empty()) {
        compile_args.push_back(plat_pub_versioned_cil_file.c_str());
    }
    if (!vendor_policy_cil_file.empty()) {
        compile_args.push_back(vendor_policy_cil_file.c_str());
    }
    if (!odm_policy_cil_file.empty()) {
        compile_args.push_back(odm_policy_cil_file.c_str());
    }
    if (!genfs_cil_file.empty()) {
        compile_args.push_back(genfs_cil_file.c_str());
    }
    compile_args.push_back(nullptr);

    int secilc_rc = ForkExecveAndWaitForCompletion(compile_args[0], (char**)compile_args.data());
    if (!synthesized_mapping_file.empty()) {
        unlink(synthesized_mapping_file.c_str());
    }
    if (secilc_rc != 0) {
        unlink(compiled_sepolicy);
        return false;
    }
    unlink(compiled_sepolicy);

    policy_file->fd = std::move(compiled_sepolicy_fd);
    policy_file->path = compiled_sepolicy;
    return true;
}

bool OpenMonolithicPolicy(PolicyFile* policy_file) {
    static constexpr char kSepolicyFile[] = "/sepolicy";

    LOG(INFO) << "Opening SELinux policy from monolithic file " << kSepolicyFile;
    policy_file->fd.reset(open(kSepolicyFile, O_RDONLY | O_CLOEXEC | O_NOFOLLOW));
    if (policy_file->fd < 0) {
        PLOG(ERROR) << "Failed to open monolithic SELinux policy";
        return false;
    }
    policy_file->path = kSepolicyFile;
    return true;
}

void ReadPolicy(std::string* policy) {
    PolicyFile policy_file;

    bool ok = IsSplitPolicyDevice() ? OpenSplitPolicy(&policy_file)
                                    : OpenMonolithicPolicy(&policy_file);
    if (!ok) {
        LOG(FATAL) << "Unable to open SELinux policy";
    }

    if (!android::base::ReadFdToString(policy_file.fd, policy)) {
        PLOG(FATAL) << "Failed to read policy file: " << policy_file.path;
    }
}

void SelinuxSetEnforcement() {
    bool kernel_enforcing = (security_getenforce() == 1);
    bool is_enforcing = IsEnforcing();
    if (kernel_enforcing != is_enforcing) {
        if (security_setenforce(is_enforcing)) {
            PLOG(FATAL) << "security_setenforce(" << (is_enforcing ? "true" : "false")
                        << ") failed";
        }
    }
}

constexpr size_t kKlogMessageSize = 1024;

void SelinuxAvcLog(char* buf) {
    struct NetlinkMessage {
        nlmsghdr hdr;
        char buf[kKlogMessageSize];
    } request = {};

    request.hdr.nlmsg_flags = NLM_F_REQUEST;
    request.hdr.nlmsg_type = AUDIT_USER_AVC;
    request.hdr.nlmsg_len = sizeof(request);
    strlcpy(request.buf, buf, sizeof(request.buf));

    auto fd = unique_fd{socket(PF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_AUDIT)};
    if (!fd.ok()) {
        return;
    }

    TEMP_FAILURE_RETRY(send(fd.get(), &request, sizeof(request), 0));
}

int RestoreconIfExists(const char* path, unsigned int flags) {
    if (access(path, F_OK) != 0 && errno == ENOENT) {
        // Avoid error message for path that is expected to not always exist.
        return 0;
    }
    return selinux_android_restorecon(path, flags);
}

}  // namespace

void SelinuxRestoreContext() {
    LOG(INFO) << "Running restorecon...";
    selinux_android_restorecon("/dev", 0);
    selinux_android_restorecon("/dev/console", 0);
    selinux_android_restorecon("/dev/kmsg", 0);
    if constexpr (WORLD_WRITABLE_KMSG) {
        selinux_android_restorecon("/dev/kmsg_debug", 0);
    }
    selinux_android_restorecon("/dev/null", 0);
    selinux_android_restorecon("/dev/ptmx", 0);
    selinux_android_restorecon("/dev/socket", 0);
    selinux_android_restorecon("/dev/random", 0);
    selinux_android_restorecon("/dev/urandom", 0);
    selinux_android_restorecon("/dev/__properties__", 0);

    selinux_android_restorecon("/dev/block", SELINUX_ANDROID_RESTORECON_RECURSE);
    selinux_android_restorecon("/dev/dm-user", SELINUX_ANDROID_RESTORECON_RECURSE);
    selinux_android_restorecon("/dev/device-mapper", 0);

    if constexpr (com::android::apex::flags::mount_before_data()) {
        selinux_android_restorecon("/dev/loop-control", 0);
    }

    selinux_android_restorecon("/apex", 0);
    selinux_android_restorecon("/bootstrap-apex", 0);
    selinux_android_restorecon("/linkerconfig", 0);

    // adb remount, snapshot-based updates, and DSUs all create files during
    // first-stage init.
    RestoreconIfExists(SnapshotManager::GetGlobalRollbackIndicatorPath().c_str(), 0);
    RestoreconIfExists("/metadata/gsi",
                       SELINUX_ANDROID_RESTORECON_RECURSE | SELINUX_ANDROID_RESTORECON_SKIP_SEHASH);
}

int SelinuxKlogCallback(int type, const char* fmt, ...) {
    android::base::LogSeverity severity = android::base::ERROR;
    if (type == SELINUX_WARNING) {
        severity = android::base::WARNING;
    } else if (type == SELINUX_INFO) {
        severity = android::base::INFO;
    }
    char buf[kKlogMessageSize];
    va_list ap;
    va_start(ap, fmt);
    int length_written = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    if (length_written <= 0) {
        return 0;
    }

    // libselinux log messages usually contain a new line character, while
    // Android LOG() does not expect it. Remove it to avoid empty lines in
    // the log buffers.
    size_t str_len = strlen(buf);
    if (buf[str_len - 1] == '\n') {
        buf[str_len - 1] = '\0';
    }

    if (type == SELINUX_AVC) {
        SelinuxAvcLog(buf);
    } else {
        android::base::KernelLogger(android::base::MAIN, severity, "selinux", nullptr, 0, buf);
    }
    return 0;
}

void SelinuxSetupKernelLogging() {
    selinux_callback cb;
    cb.func_log = SelinuxKlogCallback;
    selinux_set_callback(SELINUX_CB_LOG, cb);
}

int SelinuxGetVendorAndroidVersion() {
    if (IsMicrodroid()) {
        // As of now Microdroid doesn't have any vendor code.
        return __ANDROID_API_FUTURE__;
    }
    static int vendor_android_version = [] {
        if (!IsSplitPolicyDevice()) {
            // If this device does not split sepolicy files, it's not a Treble device and therefore,
            // we assume it's always on the latest platform.
            return __ANDROID_API_FUTURE__;
        }

        std::string version;
        if (!GetVendorMappingVersion(&version)) {
            LOG(FATAL) << "Could not read vendor SELinux version";
        }

        int major_version;
        std::string major_version_str(version, 0, version.find('.'));
        if (!ParseInt(major_version_str, &major_version)) {
            PLOG(FATAL) << "Failed to parse the vendor sepolicy major version "
                        << major_version_str;
        }

        return major_version;
    }();
    return vendor_android_version;
}

// This is for R system.img/system_ext.img to work on old vendor.img as system_ext.img
// is introduced in R. We mount system_ext in second stage init because the first-stage
// init in boot.img won't be updated in the system-only OTA scenario.
void MountMissingSystemPartitions() {
    android::fs_mgr::Fstab fstab;
    if (!ReadDefaultFstab(&fstab)) {
        LOG(ERROR) << "Could not read default fstab";
    }

    android::fs_mgr::Fstab mounts;
    if (!ReadFstabFromFile("/proc/mounts", &mounts)) {
        LOG(ERROR) << "Could not read /proc/mounts";
    }

    [[clang::no_destroy]] static const std::vector<std::string> kPartitionNames = {"system_ext",
                                                                                   "product"};

    android::fs_mgr::Fstab extra_fstab;
    for (const auto& name : kPartitionNames) {
        if (GetEntryForMountPoint(&mounts, "/"s + name)) {
            // The partition is already mounted.
            continue;
        }

        auto system_entries = GetEntriesForMountPoint(&fstab, "/system");
        for (auto& system_entry : system_entries) {
            if (!system_entry) {
                LOG(ERROR) << "Could not find mount entry for /system";
                break;
            }
            if (!system_entry->fs_mgr_flags.logical) {
                LOG(INFO) << "Skipping mount of " << name << ", system is not dynamic.";
                break;
            }

            auto entry = *system_entry;
            auto partition_name = name + fs_mgr_get_slot_suffix();
            auto replace_name = "system"s + fs_mgr_get_slot_suffix();

            entry.mount_point = "/"s + name;
            entry.blk_device =
                android::base::StringReplace(entry.blk_device, replace_name, partition_name, false);
            if (!fs_mgr_update_logical_partition(&entry)) {
                LOG(ERROR) << "Could not update logical partition";
                continue;
            }

            extra_fstab.emplace_back(std::move(entry));
        }
    }

    SkipMountingPartitions(&extra_fstab, true /* verbose */);
    if (extra_fstab.empty()) {
        return;
    }

    BlockDevInitializer block_dev_init;
    for (auto& entry : extra_fstab) {
        if (access(entry.blk_device.c_str(), F_OK) != 0) {
            auto block_dev = android::base::Basename(entry.blk_device);
            if (!block_dev_init.InitDmDevice(block_dev)) {
                LOG(ERROR) << "Failed to find device-mapper node: " << block_dev;
                continue;
            }
        }
        if (fs_mgr_do_mount_one(entry)) {
            LOG(ERROR) << "Could not mount " << entry.mount_point;
        }
    }
}

static void LoadSelinuxPolicy(std::string& policy) {
    LOG(INFO) << "Loading SELinux policy";

    set_selinuxmnt("/sys/fs/selinux");
    if (security_load_policy(policy.data(), policy.size()) < 0) {
        PLOG(FATAL) << "SELinux:  Could not load policy";
    }
}

// Encapsulates steps to load SELinux policy in Microdroid.
// So far the process is very straightforward - just load the precompiled policy from /system.
void LoadSelinuxPolicyMicrodroid() {
    constexpr const char kMicrodroidPrecompiledSepolicy[] =
            "/system/etc/selinux/microdroid_precompiled_sepolicy";

    LOG(INFO) << "Opening SELinux policy from " << kMicrodroidPrecompiledSepolicy;
    unique_fd policy_fd(open(kMicrodroidPrecompiledSepolicy, O_RDONLY | O_CLOEXEC | O_NOFOLLOW));
    if (policy_fd < 0) {
        PLOG(FATAL) << "Failed to open " << kMicrodroidPrecompiledSepolicy;
    }

    std::string policy;
    if (!android::base::ReadFdToString(policy_fd, &policy)) {
        PLOG(FATAL) << "Failed to read policy file: " << kMicrodroidPrecompiledSepolicy;
    }

    LoadSelinuxPolicy(policy);
}

// The SELinux setup process is carefully orchestrated around snapuserd. Policy
// must be loaded off dynamic partitions, and during an OTA, those partitions
// cannot be read without snapuserd. But, with kernel-privileged snapuserd
// running, loading the policy will immediately trigger audits.
//
// We use a five-step process to address this:
//  (1) Read the policy into a string, with snapuserd running.
//  (2) Rewrite the snapshot device-mapper tables, to generate new dm-user
//      devices and to flush I/O.
//  (3) Kill snapuserd, which no longer has any dm-user devices to attach to.
//  (4) Load the sepolicy and issue critical restorecons in /dev, carefully
//      avoiding anything that would read from /system.
//  (5) Re-launch snapuserd and attach it to the dm-user devices from step (2).
//
// After this sequence, it is safe to enable enforcing mode and continue booting.
void LoadSelinuxPolicyAndroid() {
    MountMissingSystemPartitions();

    LOG(INFO) << "Opening SELinux policy";

    // Read the policy before potentially killing snapuserd.
    std::string policy;
    ReadPolicy(&policy);

    auto snapuserd_helper = SnapuserdSelinuxHelper::CreateIfNeeded();
    if (snapuserd_helper) {
        // Kill the old snapused to avoid audit messages. After this we cannot read from /system
        // (or other dynamic partitions) until we call FinishTransition().
        snapuserd_helper->StartTransition();
    }

    LoadSelinuxPolicy(policy);

    if (snapuserd_helper) {
        // Before enforcing, finish the pending snapuserd transition.
        snapuserd_helper->FinishTransition();
        snapuserd_helper = nullptr;
    }
}

#ifdef ALLOW_REMOUNT_OVERLAYS
bool EarlySetupOverlays() {
    bool has_overlays = false;
    std::string contents;
    if (!android::base::ReadFileToString("/proc/mounts", &contents, true)) {
        PLOG(ERROR) << "Failed to read /proc/mounts";
        return false;
    }

    auto lines = android::base::Split(contents, "\n");
    for (auto const& line : lines)
        if (android::base::StartsWith(line, "overlay")) {
            has_overlays = true;
            break;
        }

    if (!has_overlays) return false;
    if (mount("tmpfs", kSecondStageRes, "tmpfs", MS_REMOUNT | MS_NOSUID | MS_NODEV,
              "mode=0755,uid=0,gid=0") == -1) {
        PLOG(FATAL) << "Failed to remount tmpfs on " << kSecondStageRes << " to remove NO_EXEC";
    }

    return true;
}

void SetupOverlays() {
    // After adb remount, we mount all r/o volumes with overlayfs to allow writing.
    // However, since overlayfs performs its file operations in the context of the
    // mounting process, this will not work as is - init is in the kernel domain in
    // first stage, which has very limited permissions.

    // In order to fix this, we need to unmount remount all these volumes from a process
    // with sufficient privileges to be able to perform these operations. The
    // overlay_remounter domain has those privileges on debuggable devices.
    // We will call overlay_remounter which will do the unmounts/mounts.
    // But for that to work, the volumes must not be busy, so we need to copy
    // overlay_remounter from system to a ramdisk and run it from there.
    const char* kOverlayRemounter = "overlay_remounter";
    auto or_src = std::filesystem::path("/system/xbin/") / kOverlayRemounter;
    auto or_dest = std::filesystem::path(kSecondStageRes) / kOverlayRemounter;
    std::error_code ec;
    std::filesystem::copy(or_src, or_dest, ec);
    if (ec) {
        LOG(FATAL) << "Failed to copy " << or_src << " to " << or_dest << " " << ec.message();
    }

    if (selinux_android_restorecon(or_dest.c_str(), 0) == -1) {
        PLOG(FATAL) << "restorecon of " << or_dest << " failed";
    }
    auto dest = unique_fd(open(or_dest.c_str(), O_RDONLY | O_CLOEXEC));
    if (dest.get() == -1) {
        PLOG(FATAL) << "Failed to reopen " << or_dest;
    }
    if (unlink(or_dest.c_str()) == -1) {
        PLOG(FATAL) << "Failed to unlink " << or_dest;
    }
    const char* args[] = {or_dest.c_str(), nullptr};
    fexecve(dest.get(), const_cast<char**>(args), environ);

    // execv() only returns if an error happened, in which case we
    // panic and never return from this function.
    PLOG(FATAL) << "execv(\"" << or_dest << "\") failed";
}
#else
bool EarlySetupOverlays() {
    return false;
}
void SetupOverlays() {}
#endif

static void CopySelinuxXattrAndBindMount(const std::string& src_path, const std::string& dst_path) {
    char con[256] = {};
    ssize_t len = lgetxattr(src_path.c_str(), XATTR_NAME_SELINUX, con, sizeof(con) - 1);
    if (len > 0) {
        lsetxattr(dst_path.c_str(), XATTR_NAME_SELINUX, con, len, 0);
    }
    chmod(dst_path.c_str(), 0644);
    if (mount(dst_path.c_str(), src_path.c_str(), nullptr, MS_BIND, nullptr) == 0) {
        LOG(INFO) << "Applied vendor compat bind-mount for " << src_path;
    } else {
        PLOG(WARNING) << "Failed vendor compat bind-mount for " << src_path;
    }
}

static void PatchVendorCompatFiles() {
    constexpr const char* kCompatDir = "/dev/__vendor_compat";
    mkdir(kCompatDir, 0755);

    // 1. Patch restrictive mremap seccomp rules in older vendor C2/media policies
    //    so Android 15+ Bionic mremap(MREMAP_MAYMOVE) does not trigger SIGSYS.
    //    Uses distinct vendor/odm prefixes and replaces the full mremap rule line so
    //    compound expressions (e.g. "mremap: arg3 == 3 || ...") never become invalid syntax.
    struct SeccompDirSpec {
        const char* dir_path;
        const char* out_prefix;
    };
    static constexpr SeccompDirSpec kSeccompDirs[] = {
        {"/vendor/etc/seccomp_policy", "vendor_seccomp_"},
        {"/odm/etc/seccomp_policy", "odm_seccomp_"},
    };
    for (const auto& spec : kSeccompDirs) {
        std::unique_ptr<DIR, decltype(&closedir)> dir(opendir(spec.dir_path), closedir);
        if (!dir) continue;
        while (struct dirent* de = readdir(dir.get())) {
            if (de->d_name[0] == '.') continue;
            std::string src_path = std::string(spec.dir_path) + "/" + de->d_name;
            std::string content;
            if (!android::base::ReadFileToString(src_path, &content)) continue;
            if (content.find("mremap:") == std::string::npos) continue;

            bool modified = false;
            std::vector<std::string> lines = android::base::Split(content, "\n");
            for (std::string& line : lines) {
                std::string trimmed = android::base::Trim(line);
                if (android::base::StartsWith(trimmed, "mremap:") && trimmed != "mremap: 1") {
                    line = "mremap: 1";
                    modified = true;
                }
            }
            if (!modified) continue;

            std::string patched = android::base::Join(lines, '\n');
            std::string dst_path = std::string(kCompatDir) + "/" + spec.out_prefix + de->d_name;
            if (android::base::WriteStringToFile(patched, dst_path, 0644, 0, 0)) {
                CopySelinuxXattrAndBindMount(src_path, dst_path);
            }
        }
    }

    // 2. Patch Samsung Exynos NPU libeden_osal.so eden_mem_free() uninitialized munmap size bug:
    //    Under Scudo, [x19, #0x10] (mem->alloc_size) is uninitialized on NPU buffer close,
    //    causing munmap(user_ptr, garbage) to unmap camera.provider@4.0-service_64's own VMAs.
    //    Strictly gated on exact ELF64 AArch64 + unique 8-byte instruction sequence + bl call.
    const std::string eden_src = "/vendor/lib64/libeden_osal.so";
    std::string eden_data;
    if (android::base::ReadFileToString(eden_src, &eden_data) &&
        eden_data.size() >= sizeof(Elf64_Ehdr) &&
        memcmp(eden_data.data(), ELFMAG, SELFMAG) == 0) {
        const auto* ehdr = reinterpret_cast<const Elf64_Ehdr*>(eden_data.data());
        if (ehdr->e_ident[EI_CLASS] == ELFCLASS64 && ehdr->e_machine == EM_AARCH64) {
            // ldr x0, [x19, #0x20] (60 12 40 f9); ldr x1, [x19, #0x10] (61 0a 40 f9)
            static constexpr uint8_t kEdenMunmapSeq[8] = {
                0x60, 0x12, 0x40, 0xf9, 0x61, 0x0a, 0x40, 0xf9,
            };
            void* first_hit = memmem(eden_data.data(), eden_data.size(),
                                     kEdenMunmapSeq, sizeof(kEdenMunmapSeq));
            if (first_hit != nullptr) {
                size_t hit_off = static_cast<const uint8_t*>(first_hit) -
                                 reinterpret_cast<const uint8_t*>(eden_data.data());
                // Ensure the sequence is unique in the binary and immediately followed by `bl`
                bool unique_hit =
                        (hit_off + 12 <= eden_data.size()) &&
                        (memmem(eden_data.data() + hit_off + 1, eden_data.size() - hit_off - 1,
                                kEdenMunmapSeq, sizeof(kEdenMunmapSeq)) == nullptr);
                uint8_t bl_top = (hit_off + 12 <= eden_data.size())
                                         ? static_cast<uint8_t>(eden_data[hit_off + 11])
                                         : 0;
                if (unique_hit && (bl_top & 0xfc) == 0x94) {
                    // Rewrite ldr x1, [x19, #0x10] -> ldr x1, [x19, #0x8] (mem->size)
                    eden_data[hit_off + 5] = static_cast<char>(0x06);
                    std::string eden_dst = std::string(kCompatDir) + "/vendor_lib64_libeden_osal.so";
                    if (android::base::WriteStringToFile(eden_data, eden_dst, 0644, 0, 0)) {
                        CopySelinuxXattrAndBindMount(eden_src, eden_dst);
                    }
                }
            }
        }
    }

    // 3. Patch Samsung Exynos Audio HAL (audio.primary.*.so) get_device_id_from_input()
    //    so AUDIO_DEVICE_IN_BACK_MIC (0x1f) calls check_device_builtin_mic() and routes
    //    camcorder-multi-mic instead of single-mic camcorder-2nd-mic during 3-mic RecordAlive.
    //    Uses separate 32-bit/64-bit output prefixes so 64-bit never overwrites 32-bit!
    struct AudioHalDirSpec {
        const char* dir_path;
        const char* out_prefix;
    };
    static constexpr AudioHalDirSpec kAudioHalDirs[] = {
        {"/vendor/lib/hw", "vendor_lib32_"},
        {"/vendor/lib64/hw", "vendor_lib64_"},
    };
    const uint8_t kAudioInTbbOrig[20] = {
        0xdf, 0xe8, 0x01, 0xf0, 0x06, 0x05, 0x10, 0x05, 0x16, 0x05,
        0x05, 0x05, 0x05, 0x1b, 0xdf, 0xe7, 0x40, 0x46, 0x1e, 0x21,
    };
    const uint8_t kAudioInTbbPatch[20] = {
        0xdf, 0xe8, 0x01, 0xf0, 0x06, 0x06, 0x10, 0x05, 0x16, 0x05,
        0x05, 0x05, 0x05, 0x1b, 0xdf, 0xe7, 0x01, 0x46, 0x40, 0x46,
    };
    for (const auto& spec : kAudioHalDirs) {
        std::unique_ptr<DIR, decltype(&closedir)> dir(opendir(spec.dir_path), closedir);
        if (!dir) continue;
        while (struct dirent* de = readdir(dir.get())) {
            if (!android::base::StartsWith(de->d_name, "audio.primary.") ||
                !android::base::EndsWith(de->d_name, ".so")) {
                continue;
            }
            std::string src_path = std::string(spec.dir_path) + "/" + de->d_name;
            std::string hal_data;
            if (!android::base::ReadFileToString(src_path, &hal_data)) continue;
            void* match = memmem(hal_data.data(), hal_data.size(),
                                 kAudioInTbbOrig, sizeof(kAudioInTbbOrig));
            if (!match) continue;
            memcpy(match, kAudioInTbbPatch, sizeof(kAudioInTbbPatch));
            std::string dst_path = std::string(kCompatDir) + "/" + spec.out_prefix + de->d_name;
            if (android::base::WriteStringToFile(hal_data, dst_path, 0644, 0, 0)) {
                CopySelinuxXattrAndBindMount(src_path, dst_path);
            }
        }
    }
}

int SetupSelinux(char** argv) {
    SetStdioToDevNull(argv);
    InitKernelLogging(argv);

    if (REBOOT_BOOTLOADER_ON_PANIC && !AttemptingToBootNewSlot()) {
        InstallRebootSignalHandlers();
    }

    boot_clock::time_point start_time = boot_clock::now();

    SelinuxSetupKernelLogging();

    // Test to see if we should use overlays, and if so remount tmpfs before selinux will block
    bool use_overlays = EarlySetupOverlays();

    // TODO(b/287206497): refactor into different headers to only include what we need.
    if (IsMicrodroid()) {
        LoadSelinuxPolicyMicrodroid();
    } else {
        LoadSelinuxPolicyAndroid();
        PatchVendorCompatFiles();
    }

    SelinuxSetEnforcement();

    if (IsMicrodroid() && android::virtualization::IsOpenDiceChangesFlagEnabled()) {
        // We run restorecon of /microdroid_resources while we are still in kernel context to avoid
        // granting init `tmpfs:file relabelfrom` capability.
        const int flags = SELINUX_ANDROID_RESTORECON_RECURSE;
        if (selinux_android_restorecon("/microdroid_resources", flags) == -1) {
            PLOG(FATAL) << "restorecon of /microdroid_resources failed";
        }
    }

    // We're in the kernel domain and want to transition to the init domain.  File systems that
    // store SELabels in their xattrs, such as ext4 do not need an explicit restorecon here,
    // but other file systems do.  In particular, this is needed for ramdisks such as the
    // recovery image for A/B devices.
    if (selinux_android_restorecon("/system/bin/init", 0) == -1) {
        PLOG(FATAL) << "restorecon failed of /system/bin/init failed";
    }

    setenv(kEnvSelinuxStartedAt, std::to_string(start_time.time_since_epoch().count()).c_str(), 1);

    // SetupOverlays does not return if overlays exist, instead it execs overlay_remounter
    // which then execs second stage init
    if (use_overlays) SetupOverlays();

    const char* path = "/system/bin/init";
    const char* args[] = {path, "second_stage", nullptr};
    execv(path, const_cast<char**>(args));

    // execv() only returns if an error happened, in which case we
    // panic and never return from this function.
    PLOG(FATAL) << "execv(\"" << path << "\") failed";

    return 1;
}

}  // namespace init
}  // namespace android
