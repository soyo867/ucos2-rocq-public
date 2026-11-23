Require Export Ucos2Verify.VC.code.task.spec.app_task_stat_hook_spec.

(** The enabled port statistics hook calls the delivered application hook
    with the same arbitrary caller assertion frame and returns that frame.
    This internal resource contract is composed by the statistics-task caller. *)
