(**
  Structural interface audit for the UC/OS-II abstract state machine.

  This file intentionally contains only [Check] commands.  It does not add
  an invariant, an axiom, or a function specification.  The purpose is to
  keep the state-machine boundary executable: every top-level state component
  has a replacement operation, every physical owner is selectable through
  [UCOS2Module], and the invariant exposes the corresponding split/merge
  interfaces used by module proofs.  This structural audit does not prove
  semantic coverage or invariant preservation of every source operation.
*)
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_state_machine.
Require Import Ucos2Verify.lib.kernel_start.
Require Import Ucos2Verify.lib.time.

Check UCOS2_Verify_State.
Check Glob_InterruptAbstractState.
Check Glob_TaskAbstractState.
Check SchedAbstractState.
Check Glob_EventAbstractState.
Check TickAbstractState.
Check GlobFlagState.
Check GlobMemoryState.
Check GlobTimerState.
Check StatisticsState.
Check KernelControlState.
Check NameResourceState.

Check replace_IntrS.
Check replace_TskS.
Check replace_SchedS.
Check replace_EventS.
Check replace_TickS.
Check replace_FlagS.
Check replace_MemoryS.
Check replace_TimerS.
Check replace_StatsS.
Check replace_ControlS.
Check replace_NameS.

(* Every component has the same put-back, last-write and frame interface.
   Listing these checks prevents a newly added top-level component from
   silently having only a constructor but no reusable transition laws. *)
Check replace_IntrS_put_back.
Check replace_TickS_put_back.
Check replace_TskS_put_back.
Check replace_SchedS_put_back.
Check replace_EventS_put_back.
Check replace_FlagS_put_back.
Check replace_MemoryS_put_back.
Check replace_TimerS_put_back.
Check replace_StatsS_put_back.
Check replace_ControlS_put_back.
Check replace_NameS_put_back.
Check replace_IntrS_last_write.
Check replace_TickS_last_write.
Check replace_TskS_last_write.
Check replace_SchedS_last_write.
Check replace_EventS_last_write.
Check replace_FlagS_last_write.
Check replace_MemoryS_last_write.
Check replace_TimerS_last_write.
Check replace_StatsS_last_write.
Check replace_ControlS_last_write.
Check replace_NameS_last_write.
Check replace_IntrS_frame.
Check replace_TickS_frame.
Check replace_TskS_frame.
Check replace_SchedS_frame.
Check replace_EventS_frame.
Check replace_FlagS_frame.
Check replace_MemoryS_frame.
Check replace_TimerS_frame.
Check replace_StatsS_frame.
Check replace_ControlS_frame.
Check replace_NameS_frame.

(* Independent component updates commute. *)
Check replace_IntrS_TickS_commute.
Check replace_IntrS_TskS_commute.
Check replace_IntrS_SchedS_commute.
Check replace_IntrS_EventS_commute.
Check replace_IntrS_FlagS_commute.
Check replace_IntrS_MemoryS_commute.
Check replace_IntrS_TimerS_commute.
Check replace_IntrS_StatsS_commute.
Check replace_IntrS_ControlS_commute.
Check replace_IntrS_NameS_commute.
Check replace_TickS_TskS_commute.
Check replace_TickS_SchedS_commute.
Check replace_TickS_EventS_commute.
Check replace_TickS_FlagS_commute.
Check replace_TickS_MemoryS_commute.
Check replace_TickS_TimerS_commute.
Check replace_TickS_StatsS_commute.
Check replace_TickS_ControlS_commute.
Check replace_TickS_NameS_commute.
Check replace_TskS_SchedS_commute.
Check replace_TskS_EventS_commute.
Check replace_TskS_FlagS_commute.
Check replace_TskS_MemoryS_commute.
Check replace_TskS_TimerS_commute.
Check replace_TskS_StatsS_commute.
Check replace_TskS_ControlS_commute.
Check replace_TskS_NameS_commute.
Check replace_SchedS_EventS_commute.
Check replace_SchedS_FlagS_commute.
Check replace_SchedS_MemoryS_commute.
Check replace_SchedS_TimerS_commute.
Check replace_SchedS_StatsS_commute.
Check replace_SchedS_ControlS_commute.
Check replace_SchedS_NameS_commute.
Check replace_EventS_FlagS_commute.
Check replace_EventS_MemoryS_commute.
Check replace_EventS_TimerS_commute.
Check replace_EventS_StatsS_commute.
Check replace_EventS_ControlS_commute.
Check replace_EventS_NameS_commute.
Check replace_FlagS_MemoryS_commute.
Check replace_FlagS_TimerS_commute.
Check replace_FlagS_StatsS_commute.
Check replace_FlagS_ControlS_commute.
Check replace_FlagS_NameS_commute.
Check replace_MemoryS_TimerS_commute.
Check replace_MemoryS_StatsS_commute.
Check replace_MemoryS_ControlS_commute.
Check replace_MemoryS_NameS_commute.
Check replace_TimerS_StatsS_commute.
Check replace_TimerS_ControlS_commute.
Check replace_TimerS_NameS_commute.
Check replace_StatsS_ControlS_commute.
Check replace_StatsS_NameS_commute.
Check replace_ControlS_NameS_commute.

Check UCOS2Module.
Check UCOS2_module_rep.
Check UCOS2_raw_rep.
Check UCOS2_selected_rep.
Check UCOS2_selected_rep_split_module.
Check UCOS2_selected_rep_frame.
Check UCOS2_raw_rep_split_module.
Check UCOS2_raw_rep_missing_module_split_module.
Check UCOS2_raw_rep_split_two.
Check UCOS2_raw_rep_missing_module_frame.
Check UCOS2_raw_rep_missing_two_frame.
Check UCOS2_raw_rep_merge_updated_module.
Check UCOS2_raw_rep_merge_updated_two.

Check UCOS2_state_inv.
Check UCOS2_inv.
Check UCOS2_inv_split_module.
Check UCOS2_inv_split_two.
Check UCOS2_inv_merge_updated_module.
Check UCOS2_inv_merge_updated_two.
Check UCOS2_inv_split_task_sched.
Check UCOS2_inv_split_event_queue.
Check UCOS2_inv_merge_updated_event_queue.
Check UCOS2_inv_split_flag.
Check UCOS2_inv_split_memory.
Check UCOS2_inv_split_timer.
Check UCOS2_inv_split_statistics.
Check UCOS2_inv_split_control.
Check UCOS2_inv_split_names.
Check UCOS2_inv_merge_updated_flag.
Check UCOS2_inv_merge_updated_memory.
Check UCOS2_inv_merge_updated_timer.
Check ucos2_state_components.
Check ucos2_module_owners.
Check ucos2_owner_component.
Check ucos2_state_replacement_laws.
Check ucos2_state_machine_coverage.
Check UCOS2OwnerTransition.
Check ucos2_owner_transition_composes.
Check UCOS2_raw_rep_split_selected.
Check UCOS2_inv_split_selected.
Check UCOS2_selected_rep_mono.
Check UCOS2_raw_rep_merge_updated_selected.
Check UCOS2_inv_merge_updated_selected.
Check UCOS2SelectedTransition.
Check ucos2_selected_transition_composes.
Check ucos2_selected_transition_sequence.
Check task_sched_event_queue_module_frame.
Check task_suspend_selected_transition.
Check task_suspend_selected_resources_merge.
Check memory_get_selected_transition.
Check memory_put_selected_transition.
Check task_resume_selected_transition.
Check event_pend_selected_transition.
Check event_wake_selected_transition.
Check UCOS2_boot_validity.
Check kernel_start_selection.
Check kernel_start_selection_empty.
Check kernel_start_ready_selection.
Check kernel_start_ready_preserves_validity.
Check kernel_running_store_preserves_validity.
Check kernel_start_running_task_boundary.
Check kernel_start_running_preserves_validity.
Check kernel_start_running_resources_merge.
Check task_set_delay_layout_image_eq.
Check task_expire_delay_layout_image_eq.
Check task_expire_delay_eq_last_tick.
Check task_expire_delay_preserves_linked_phase.
Check task_expire_delay_preserves_suspension.
Check time_dly_current_blocked_before_schedule.
Check time_dly_preserves_validity.
Check time_dly_resume_preserves_validity.
Check time_dly_selected_transition.
Check time_dly_resume_selected_transition.
Check time_set_selected_transition.
Check time_get_after_set.
Check time_hmsm_ticks_defined.
Check time_hmsm_ticks_in_range.
Check time_dly_resume_resources_merge.
