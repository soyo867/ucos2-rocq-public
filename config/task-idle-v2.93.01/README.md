# Selected Idle hook

On 2026-10-13 the user authorized the recommended concrete empty Idle hook and
the resolved-SELF Suspend guard. [idle_hook.c](idle_hook.c) uses the executable
tokens of the official V2.93.01 `App_TaskIdleHook` template.

The actual chain is `OS_TaskIdle -> OSTaskIdleHook -> App_TaskIdleHook` with
both hook switches enabled. The Idle loop increments `OSIdleCtr` inside its
critical section and calls the hook after restoring the saved status. Selecting
an empty hook prevents that direct body from blocking/deleting Idle; it does
not remove interrupt interference or authorize treating the whole interval as
state identity. The separate [Suspend patch](../../source_variants/task-idle-protection/README.md)
protects the resolved Idle target even when SELF is requested by an ISR.

[hook-source-binding.json](hook-source-binding.json) is a new selection record.
It does not rewrite the earlier creation-hook binding, select every application
hook, or assert deployment on a user's board. Run the source and host diagnostic:

```sh
bash uC-OS2_verify/tests/task_idle_protection/run.sh UPSTREAM_GIT
```

A custom Idle hook remains possible: bind its source and prove the required
resource preservation, valid return and Idle-readiness properties. A low-power
instruction that leaves Idle logically ready differs from a blocking kernel API
that removes its ready bit. Platform-specific effects still require the existing
explicit platform boundary; this selection supplies no new Coq axiom.
