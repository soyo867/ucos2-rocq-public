Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.VC.code.task.spec.app_task_return_hook_spec.

(** Selected V2.93.01 ARMv7-A Return wrapper with CPU/App hooks enabled.
    The actual App_TaskReturnHook call preserves the same UCOS2 caller frame.
    Its selected empty C implementation is delivered separately; this wrapper
    is a C callee, not an assembly/BSP assumption. *)
