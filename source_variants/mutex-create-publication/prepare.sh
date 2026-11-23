#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
    printf 'Usage: bash %s UPSTREAM_GIT OUTPUT_DIRECTORY [selected|full]\n' "$0" >&2
    exit 2
fi
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
profile=$(mktemp -d /tmp/ucos2-create-publication-profile.XXXXXXXX)
trap 'rm -rf -- "$profile"' EXIT
case ${3:-selected} in
    selected)
        cp -- "$here/profile.json" "$profile/profile.json"
        cp -- "$root/uC-OS2_verify/config/timer-v2.93.01/timer-old-features.patch" "$profile/"
        ;;
    full) cp -- "$here/full-profile.json" "$profile/profile.json" ;;
    *) printf 'Unknown profile: %s\n' "$3" >&2; exit 2 ;;
esac
for name in app-cfg-freestanding port-extern-declarations; do
    cp -- "$root/uC-OS2_verify/config/timer-v2.93.01/$name.patch" "$profile/$name.patch"
done
cp -- "$here/../mutex-nested-priority/os_mutex.patch" "$profile/mutex-nested-priority.patch"
cp -- "$here/../mutex-del-revalidate/os_mutex.patch" "$profile/mutex-del-revalidate.patch"
cp -- "$here/os_mutex.patch" "$profile/mutex-create-publication.patch"
python3 "$root/uC-OS2_verify/tools/prepare_source_input.py" \
    --upstream "$1" --profile "$profile/profile.json" --output "$2"
