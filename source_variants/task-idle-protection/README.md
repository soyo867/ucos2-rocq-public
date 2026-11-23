# Idle protection after resolving SELF

The user authorized the recommended implementation safeguard and official empty
Idle hook on 2026-10-13. This additive patch keeps the original source and its
proofs intact. It is an implementation change, not an annotation-only change.

## Executable change

The original `OSTaskSuspend` rejects a literal `OS_TASK_IDLE_PRIO` before Save,
then resolves `OS_PRIO_SELF` from `OSTCBCur->OSTCBPrio` inside the critical
section. There is no repeated Idle check or ISR rejection in that function.
Thus SELF can select the interrupted Idle task and clear its readiness bits.
This is a source-level path; no deployed handler is asserted to use it.

[os_task.patch](os_task.patch) checks the resolved priority before the table
lookup or any TCB/ready-bit write. The new Idle branch restores the saved CPU
status and returns the existing `OS_ERR_TASK_SUSPEND_IDLE`. The original early
checks, ordinary-task effects, SELF scheduling decision and other errors remain.
The protection is unconditional inside the critical section, independent of
the optional early argument checks. The supplied two profiles enable those
checks; other configurations are not claimed verified.

The concrete Idle hook selection is separately recorded in
[hook-source-binding.json](../../config/task-idle-v2.93.01/hook-source-binding.json).
Only `App_TaskIdleHook` is selected here. Existing creation-hook selections
and other application hooks are unchanged. An empty direct body does not
exclude interrupts during the surrounding call.

## Reproduce and check

```sh
bash uC-OS2_verify/source_variants/task-idle-protection/prepare.sh \
  UPSTREAM_GIT NEW_OUTPUT_DIRECTORY selected
bash uC-OS2_verify/tests/task_idle_protection/run.sh UPSTREAM_GIT
```

`prepare.sh` reads pinned Git objects, preserves headers/macros and records
the exact patch assets. `full` instead enables Multi/Names/Profile together.
These isolated profiles test this patch; they do not replace the combined
Task/Mutex source selections or silently apply/remove their earlier patches.
The regression compiles actual pinned `os_task.c` and `os_core.c`, the official
port wrapper and the selected application hook. Host Save/Restore/context-switch
stubs make the tested cuts deterministic; they do not prove ARM/BSP execution.

## Proof scope

The original `task_suspend_spec.v` retains its original-source meaning. The
guarded model is separate, so frozen callers cannot acquire changed semantics
under the same import. Its normal arm reuses the original critical operation;
its new error arm must preserve task/scheduler storage before Restore.

The patch alone does not establish global perpetual Idle readiness. Source-bound
callers, Delay/Pend/Delete/priority operations, callbacks and registered IRQs
still need their actual preservation arguments. No `IdleReady` assumption is
added to SemPend admission. No arbitrary application/ISR implementation, SMP
port, complete Suspend API or complete SemPend proof is claimed by these assets.
Generated targets and historical acceptance are untouched; any new annotated
Suspend input must generate and prove its own canonical targets.
