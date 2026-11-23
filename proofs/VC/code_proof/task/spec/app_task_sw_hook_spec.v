Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.

(** The selected, pinned Template App_TaskSwHook has no statements.  Its
    actual C contract preserves the caller's arbitrary owned frame and
    exposes this exact own-operation state relation. Custom hooks do not
    use this source instance. *)
Definition app_task_sw_hook_step (_ : StableGlobVars)
  (before after : UCOS2_Verify_State) : Prop := after = before.

Lemma app_task_sw_hook_step_refl : forall sg state,
  app_task_sw_hook_step sg state state.
Proof. intros; reflexivity. Qed.
