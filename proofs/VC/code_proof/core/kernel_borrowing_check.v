(** Compilation entry for the model-level borrowing scenario. The claims
    are the proved spatial/global lemmas in these libraries, not the Check
    commands. No whole-API or platform implementation claim is made here. *)
Require Import Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.lib.memory_execution.
Require Import Ucos2Verify.lib.name_execution.
Require Import Ucos2Verify.lib.critical_region_loan.

Check flag_block_preserves_global_validity.
Check flag_block_merge_global_resources.
Check flag_wake_returns_stack_and_global_resources.
Check flag_timeout_returns_stack_and_global_resources.
Check memory_get_resources_merge.
Check memory_put_resources_merge.
Check name_register_reader_preserves_global_resources.
Check name_read_character_split.
Check name_read_terminator_split.
Check UCOS2_inv_merge_name_byte.
Check name_active_reader_excludes_write.
Check name_active_reader_excludes_source_release.
Check name_release_reader_preserves_global_resources.
Check critical_region_full_share.
Check critical_region_share_join.
Check critical_region_step_resources.
Check critical_region_shared_rep_closed.
Check critical_region_observation_cannot_duplicate_running.
