# Flag Pend protected type revalidation

This source repair targets V2.93.01 commit
`bfc6120f20cb27a927a9fc5dd667f9e455495777` and the selected
`timer-v2.93.01` configuration. It is an input to the pending Flag API
verification; it does not establish QCP/Rocq or controller acceptance.

## Reproduced source defect

`OSFlagPend` checks `OSFlagType` before `OS_ENTER_CRITICAL`. Another task can
delete the group in that interval. With SET_ANY on an unsatisfied flag,
the original Pend then calls the actual `OS_FlagBlock` on the freed group.
The helper interprets `OSFlagWaitList`, which now holds the free-list
successor, as a waiter pointer. It publishes Pend's local stack node into
the free-group chain and, when a successor exists, writes through that
misinterpreted node.

The regression invokes the real selected `OSFlagDel`, `OSFlagPend` and
`OS_FlagBlock` bodies. The CPU fixture runs a different task's legal
NO_PEND deletion immediately before the first Save masks interrupts,
then resumes the original caller. It observes the corrupted prefix at
the scheduler call while Pend's local node is still alive; it does not
invent a continuation after that corrupted state.

Both an empty previous free list and a previous free successor reproduce
the publication. Baseline exit code zero means that the expected defect
was observed, not that the original implementation is correct.

## Change and preserved behavior

The patch rechecks the group type immediately after the first Save,
before the mode switch and any waiter/task update. For an enabled valid
wait mode and a group that is now free, it restores the saved interrupt
state, writes `OS_ERR_EVENT_TYPE`, emits the existing trace and returns
zero. The test is applied after the original consume-bit decoding.

Invalid modes keep the original `OS_ERR_FLAG_WAIT_TYPE` precedence.
The CLR cases remain conditional on `OS_FLAG_WAIT_CLR_EN`; the public
signature, configuration, normal flag results and consume operations
are unchanged. The patch changes only this guard. The independent
double-unlink repair for an aborted Pend is preserved separately in
`../flag-abort-cleanup/os_flag.patch`.

Type revalidation observes the current slot. It does not add object
generations or prevent deletion and recreation at the same address.
The formal API model must describe that current-slot behavior and its
caller/resource protocol rather than assuming that the entry image
survives every acquisition.

## Recorded validation

Evidence and reproducible scripts are in
`reports/wsl-verification-20261027/flag-pend-revalidated-20261029/`:

- `baseline-run.json`: two observations of the original bad prefix.
- `revalidated-run.json`: 28 observations, comprising 16 deletion
  interleavings (four modes, consume on/off, both free-list shapes),
  eight normal immediate/consume cases and four invalid-mode cases.
- `interleaving.c` and `run-regression.py`: actual-source host regression
  using AddressSanitizer and UndefinedBehaviorSanitizer.
- `prepare-repair.py`: the exact isolated insertion, with a reverse
  byte comparison to the original source.

The host fixture has explicit CPU/scheduler assumptions. Its pointer
layout is the host layout; the source reasoning above also identifies
the erroneous pointer use in the selected ARM32 layout. The regression
does not replace formal ARM32 memory-layout, scheduler or API proofs.

The combined source under
`reports/wsl-verification-20261027/source-input/flag-api-revalidated/`
applies this repair together with the existing Pend abort cleanup and
Del/Post protected rechecks. Its separate eight-observation integration
receipt checks that actual combined input. Existing successful receipts
are retained and are not overwritten or rerun for documentation.
