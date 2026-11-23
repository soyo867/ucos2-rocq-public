Require Export Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_post_stack_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.

(** Additive generic-view/disabled-entry SemPost case.  These imports expose
    existing data/resource interfaces and the adopted conditional Scheduler
    contract only; this seed states no complete
    C correctness or normal-return source-preservation theorem. *)
