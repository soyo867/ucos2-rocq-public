# Protected Task register lookup

Applies to the pinned uC/OS-II V2.93.01 source
`bfc6120f20cb27a927a9fc5dd667f9e455495777` and the selected profile at
`../../config/timer-v2.93.01/profile.json`.

`OSTaskRegGet` / `OSTaskRegSet` validate scalar priority and register ID before
entering the critical region. Their original protected lookup then dereferences
`OSTCBCur` or `OSTCBPrioTbl[prio]` without rejecting NULL or the reserved sentinel.
Even an explicit-priority target present at call entry can be deleted while the
caller is preempted before Save. A successful MutexCreate can then reserve the
same priority. Under the ordinary concurrent Task API scope, entry-time
existence alone cannot justify the original access.

The patch adds a NULL/reserved guard after the existing protected lookup in both
functions. This branch restores the saved CPU word exactly once, reports the
existing `OS_ERR_TASK_NOT_EXIST` (67), and returns zero (Get) or void (Set),
without accessing a register. The public error comments are updated. Scalar
guard ordering, successful paths, API types, headers and macros are retained.
This is an implementation repair, not annotation or frontend lowering.

The existing priority API still observes the task associated with the acquired
lookup. The guard does not promise stale-handle identity across deletion/reuse,
or solve ABA. Get observes a value inside the critical region; Set records a
store there. Neither promises that task/value survives all later interference.
No new task-only/ISR prohibition, preallocated-ID condition or global lifetime
lock is introduced. Valid initialized critical resources and a separate writable
error cell remain necessary.

Reproduce the bounded source regression with:

```sh
bash uC-OS2_verify/tests/task_register_lookup/run.sh "$UPSTREAM" "$NEW_OUTPUT"
```

The script prepares both versions from the fixed Git object and original
headers, verifies the exact patch boundary, builds actual kernel C with UBSan,
and exercises normal/error paths plus deterministic pre-Save deletion and
reservation interleavings. Port Save/Restore/context-switch boundaries are host
stubs; concrete ARM execution and complete function correctness are not claimed.
The patch must be included in subsequent source projection, annotation and
canonical VC generation for these APIs. This source regression alone is not
a completed C-level proof.

Recorded regression (2026-10-17): original 96 and repaired 112 ordinary source
cases passed, including exact scalar-error ordering, SELF/explicit access,
register values, ISR context and all four interrupt-mask combinations. Four
additional real-C interleavings (Get/Set × deleted/reserved) reproduced original
UBSan failures at the register dereferences; all four repaired executions
returned error 67 with balanced Save/Restore and no register access. Source
comparison confirmed that only the two guards and error comments changed.
Evidence is under
`reports/kernel-model-20260927/source-input/task-api-20261016/task-register-lookup-repair/permanent-run-2/`.
