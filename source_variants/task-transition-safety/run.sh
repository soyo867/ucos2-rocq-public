#!/usr/bin/env bash
set -euo pipefail
if [[ $# != 2 ]]; then
    printf 'Usage: bash %s UPSTREAM_GIT NEW_OUTPUT_DIRECTORY\n' "$0" >&2
    exit 2
fi
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
upstream=$1
output=$2
[[ ! -e $output && ! -L $output ]] || { printf 'Refusing existing output: %s\n' "$output" >&2; exit 2; }
mkdir -p -- "$output"
output=$(cd -- "$output" && pwd)
for variant in original repaired; do
    prepared="$output/$variant"
    python3 "$root/uC-OS2_verify/tools/prepare_source_input.py" \
      --upstream "$upstream" \
      --profile "$root/uC-OS2_verify/config/timer-v2.93.01/profile.json" \
      --output "$prepared"
    # The preparation manifest describes the common profile.  These two
    # additional selected implementation patches are explicit in this recipe.
    for selected_patch in \
      "$root/uC-OS2_verify/source_variants/task-idle-protection/os_task.patch" \
      "$root/uC-OS2_verify/source_variants/mutex-nested-priority/os_mutex.patch"; do
        patch --batch --fuzz=0 --forward --no-backup-if-mismatch -p1 \
          -d "$prepared" -i "$selected_patch"
    done
    repaired=0
    if [[ $variant == repaired ]]; then
        repaired=1
        patch --batch --fuzz=0 --forward --no-backup-if-mismatch -p1 \
          -d "$prepared" -i "$here/os_task.patch"
    fi
    "${CC:-cc}" -std=c11 -O1 -g -ffunction-sections -fdata-sections \
      -Wno-pointer-to-int-cast -Wno-int-to-pointer-cast \
      -fsanitize=undefined -fno-sanitize-recover=all \
      -DQCP_TASK_TRANSITION_REPAIRED="$repaired" \
      -DQCP_CORE_SOURCE="\"$prepared/Source/os_core.c\"" \
      -DQCP_TASK_SOURCE="\"$prepared/Source/os_task.c\"" \
      -DQCP_MUTEX_SOURCE="\"$prepared/Source/os_mutex.c\"" \
      -I "$prepared/Cfg/Template" -I "$prepared/Source" \
      -I "$prepared/Ports/ARM-Cortex-A/ARMv7-A/GNU" \
      "$here/transition_paths.c" "$root/uC-OS2_verify/config/task-idle-v2.93.01/idle_hook.c" \
      -Wl,--gc-sections -o "$output/$variant-test"
    for argument in '' --self --effective --idle; do
        printf 'case: %s %s\n' "$variant" "$argument"
        if [[ -n $argument ]]; then timeout 20s "$output/$variant-test" "$argument";
        else timeout 20s "$output/$variant-test"; fi
    done
    "${CC:-cc}" -m32 -std=c11 -ffreestanding -fsyntax-only \
      -Werror=implicit-function-declaration -I "$prepared/Cfg/Template" \
      -I "$prepared/Source" -I "$prepared/Ports/ARM-Cortex-A/ARMv7-A/GNU" \
      "$prepared/Source/os_task.c"
done
python3 - "$root" "$output" <<'PY'
import importlib.util
import sys
from pathlib import Path
root, output = map(Path, sys.argv[1:])
spec = importlib.util.spec_from_file_location('projection', root / 'uC-OS2_verify/tools/project_source_functions.py')
projection = importlib.util.module_from_spec(spec)
spec.loader.exec_module(projection)
trees = [output / variant for variant in ('original', 'repaired')]
files = [{p.relative_to(tree) for p in tree.rglob('*') if p.is_file() and 'verification-input' not in p.relative_to(tree).parts} for tree in trees]
assert files[0] == files[1]
changed = [p.as_posix() for p in sorted(files[0]) if (trees[0] / p).read_bytes() != (trees[1] / p).read_bytes()]
assert changed == ['Source/os_task.c'], changed
bodies = []
for tree in trees:
    text = (tree / 'Source/os_task.c').read_text()
    bodies.append({e['name']: text[e['start']:e['end']] for e in projection.definitions(text)})
assert bodies[0].keys() == bodies[1].keys()
changed = sorted(name for name in bodies[0] if bodies[0][name] != bodies[1][name])
assert changed == ['OSTaskChangePrio', 'OSTaskSuspend'], changed
print('passed: only two Task bodies changed; other 14 bodies and remaining native source/header files unchanged')
PY
set +e
timeout 20s "$output/original-test" --idle-tick >"$output/original-tick.stdout" 2>"$output/original-tick.stderr"
status=$?
set -e
[[ $status == 1 ]] || { printf 'Unexpected original Tick status: %s\n' "$status" >&2; exit 1; }
rg -q 'member access within null pointer of type .struct OS_TCB.' "$output/original-tick.stderr"
printf 'reproduced: original real Tick UBSan NULL-TCB access, status=%s\n' "$status"
timeout 20s "$output/repaired-test" --idle-tick
printf '%s\n' 'passed: selected source comparison, all targeted scenarios and ILP32 syntax; not formal acceptance'
