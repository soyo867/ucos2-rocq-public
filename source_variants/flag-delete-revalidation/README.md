# Flag Delete critical-section type revalidation

This is a partial, evidence-backed source repair for V2.93.01 commit
`bfc6120f20cb27a927a9fc5dd667f9e455495777` with the selected
`timer-v2.93.01` configuration. It is not a completed OSFlagDel verification.
Apply `os_flag.patch` to a fresh copy of the pinned prepared tree; the original
source and previously accepted functions remain unchanged.

## Reproduced fault

OSFlagDel checks the group type before masking interrupts. A second task can
delete that same group between the check and Save. The first Delete then
uses a free-group image as though it were still a live Flag group:

- With no previous free slot, either NO_PEND or ALWAYS inserts the group a
  second time. Its successor becomes itself, and two later Create calls
  return the same live slot.
- With a free successor, NO_PEND reports that free group as a waiting task.
- With a free successor, ALWAYS interprets it as an OS_FLAG_NODE. The host
  regression reaches OS_FlagTaskRdy with a null TCB, and UBSan reports
  `member access within null pointer` at the real source's line 1218.

These are actual C executions of the pinned Flag implementation. The fixture
injects a task action immediately before masking, corresponding to the
preemption window between the original type check and Save. This is a host
C regression with explicit CPU/scheduler fixtures, not an ARM/BSP proof.

## Minimal change

For valid NO_PEND and ALWAYS options, re-read OSFlagType immediately after
OS_ENTER_CRITICAL and before reading or following the wait list. If the group
is no longer live, restore the saved interrupt state, write OS_ERR_EVENT_TYPE,
emit the existing exit trace and return the original pointer. No group,
free-list, waiter or scheduler state is changed on this new rejection path.

The early NULL, ISR and type checks remain. Invalid options retain the
original OS_ERR_INVALID_OPT path, including after the injected deletion.
The public signature, configuration, record layout and normal deletion /
ALWAYS waiter-abort paths are unchanged.

The user authorized minimal source repairs after confirming genuine source
defects with reproducible evidence. This patch follows that evidence; a
failed verification condition was not used as implementation evidence.

## Checks and remaining scope

Run from the repository root, with SOURCE set to the recorded prepared tree
and OUTPUT to a new directory:

```sh
python3 uC-OS2_verify/tests/flag_delete_revalidation/run.py \
  --source-input "$SOURCE" --output "$OUTPUT" \
  --patch uC-OS2_verify/source_variants/flag-delete-revalidation/os_flag.patch
```

The 2026-10-28 run confirms all 22 expected observations (11 original and
11 patched), including the original negative cases, repaired rejection
paths, invalid options, normal deletion, NO_PEND refusal with a waiter and
ALWAYS abort/ready updates. The raw receipt is
`reports/wsl-verification-20261027/flag-delete-revalidated-20261028/run.json`.
The earlier original-only receipt is at
`reports/wsl-verification-20261027/flag-delete-original-20261028/run.json`.
Commands, fixture, original and patched implementations are retained there.

The Delete/Create reuse scenario still deletes a newly created group at the
same address. Its expected observation is explicitly a **known lifecycle
gap**, not a successful repair assertion. Type revalidation cannot supply a
generation check or a lease. The independent Pend double-unlink and Post
free-group-as-node variants also remain separate. No formal source decision,
same-X safeExec refinement, canonical VC proof or controller acceptance is
claimed for this candidate.
