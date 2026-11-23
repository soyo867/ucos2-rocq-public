# Preserve the caller's saturated scheduler lock in OSTaskDel

The user authorized minimal fixes for confirmed implementation errors on
2026-10-16. This patch changes executable C, not just annotations. It leaves
the pinned original V2.93.01 sources and historical proofs available.

## Defect and correction

At the temporary unlock window, original `OSTaskDel` increments
`OSLockNesting` only when it is below 255, but subsequently decrements whenever
the counter is positive. Entry value 255 therefore becomes 254 even with no
interference. The existing public `OSSchedLock` can establish value 255.
Deleting another ordinary live task then consumes one of the caller's locks;
254 subsequent Unlock calls permit a switch while its final lock is outstanding.

[os_task.patch](os_task.patch) records the actual increment in a local
`BOOLEAN lock_added` and decrements only when this invocation added a layer.
The existing positive-counter guard remains. The API, original errors and
their order, cleanup, hook and scheduler calls are unchanged. Normal 0/1/254
entry cases remain paired, and 255 is retained. No new global/ghost field,
public handle change or platform assumption is introduced.

This is not a promise that arbitrary code which directly corrupts the counter
will have its changes undone. In the admitted interrupt window, the real
`OSIntEnter`/`OSIntExit` nesting causes public `OSSchedLock`/`OSSchedUnlock` to
leave the counter unchanged, while Tick may change time and other ready tasks.
The full C proof must establish its actual environment protocol; counter
stability must not be enlarged to whole-kernel stability.

## Reproduce the source regression

```sh
bash uC-OS2_verify/tests/task_delete_saturated_lock/run.sh \
  UPSTREAM_GIT NEW_OUTPUT_DIRECTORY
```

The runner reads pinned Git object
`bfc6120f20cb27a927a9fc5dd667f9e455495777`, uses the existing selected
`timer-v2.93.01` profile, and applies this patch only to the repaired input.
Its byte audit checks the unchanged declarations, other 15 Task functions,
headers, configuration and other source files. Both original and repaired
executables use the real kernel C and UBSan, with explicit host port stubs.
The original-side checks intentionally reproduce the wrong 255→254 result;
they do not certify the original implementation as correct.

The reviewed experiment recorded 85 scenarios per version, including 17
actual C ISR/Tick windows, four saved CPU masks, head/middle deletion, and five
early errors. Detailed results and the initial source audit are retained in
`reports/kernel-model-20260927/source-input/task-api-20261016/task-del-lock-repair/`.

The host test is not an ARM32 layout, BSP, invocation-resumption or complete
TaskDel correctness proof. Its context-switch stub observes the real C choice;
it does not establish self-delete return behavior. No old proof was recompiled.

## Adoption boundary

The patch is available for the pending complete `OSTaskDel` C verification.
Include it explicitly in that source-preparation recipe and regenerate its
canonical goals before claiming a repaired-function proof. Do not change the
meaning of the original `task_delete_unlock_after_lock_count_eq` theorem:
it correctly describes the original arithmetic. Unchanged APIs retain their
existing evidence; a patch/test delivery alone is not TaskDel completion.
Compose this with the other approved Task/Mutex source variants when building
the final combined kernel; this isolated test does not remove those variants.
