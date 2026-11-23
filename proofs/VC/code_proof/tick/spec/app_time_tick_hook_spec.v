Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.

(** The pinned Template App_TimeTickHook body is empty. This instance is
    independent of App_TaskSwHook and says nothing about custom callbacks. *)
Definition app_time_tick_hook_step (_ : StableGlobVars)
  (before after : UCOS2_Verify_State) : Prop := after = before.

Lemma app_time_tick_hook_step_refl : forall sg state,
  app_time_tick_hook_step sg state state.
Proof. intros; reflexivity. Qed.

