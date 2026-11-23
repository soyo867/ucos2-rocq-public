#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
    printf 'Usage: bash %s UPSTREAM_GIT OUTPUT_DIRECTORY\n' "$0" >&2
    exit 2
fi
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
profile=$(mktemp -d /tmp/ucos2-del-revalidate-profile.XXXXXXXX)
trap 'rm -rf -- "$profile"' EXIT

# Materialize existing patch assets, not another independently maintained copy.
cp -- "$here/profile.json" "$profile/profile.json"
for name in app-cfg-freestanding port-extern-declarations timer-old-features; do
    cp -- "$root/uC-OS2_verify/config/timer-v2.93.01/$name.patch" "$profile/$name.patch"
done
cp -- "$here/../mutex-nested-priority/os_mutex.patch" "$profile/mutex-nested-priority.patch"
cp -- "$here/os_mutex.patch" "$profile/mutex-del-revalidate.patch"
python3 "$root/uC-OS2_verify/tools/prepare_source_input.py" \
    --upstream "$1" --profile "$profile/profile.json" --output "$2"
