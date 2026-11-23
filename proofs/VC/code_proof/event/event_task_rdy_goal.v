Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
Local Open Scope sac.

(*----- Function OS_EventTaskRdy -----*)

Definition OS_EventTaskRdy_safety_wit_1 := 
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) )) ”
) \/
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) )) ”
).

Definition OS_EventTaskRdy_safety_wit_1_split_goal_1 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) ) <= INT_MAX) ”
.

Definition OS_EventTaskRdy_safety_wit_1_split_goal_2 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) )) ”
.

Definition OS_EventTaskRdy_safety_wit_2 := 
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((signed_last_nbits (((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * (2^3) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits (((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * (2^3) )) (32))) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
) \/
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((signed_last_nbits (((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * (2^3) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits (((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * (2^3) )) (32))) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
).

Definition OS_EventTaskRdy_safety_wit_2_split_goal_1 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((signed_last_nbits (((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * (2^3) )) (32)) <= INT_MAX) ”
.

Definition OS_EventTaskRdy_safety_wit_2_split_goal_2 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((INT_MIN) <= (signed_last_nbits (((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * (2^3) )) (32))) ”
.

Definition OS_EventTaskRdy_safety_wit_2_split_goal_3 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (3 <= 31) ”
.

Definition OS_EventTaskRdy_safety_wit_2_split_goal_4 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (0 <= 3) ”
.

Definition OS_EventTaskRdy_entail_wit_1 := 
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |-> (unsigned_last_nbits (((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) )) (8)))
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((tcb_y_of_prio ((curPrio (t)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((curPrio (t)) = (curPrio (t))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
) \/
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) )) (8)) = (curPrio (t))) ”
  &&  emp
).

Definition OS_EventTaskRdy_entail_wit_1_split_goal_1 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH7 : (0 <= msk_pre)) (PreH8 : (msk_pre < 256)) (PreH9 : (0 <= pend_stat_pre)) (PreH10 : (pend_stat_pre < 256)) (PreH11 : ((Zlength (rows)) = 8)) (PreH12 : (0 <= (curPrio (t)))) (PreH13 : ((curPrio (t)) < 64)) (PreH14 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH15 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH16 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH20 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH24 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH25 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH26 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((unsigned_last_nbits (((signed_last_nbits ((Z.shiftl (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) 3)) (32)) + (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) )) (8)) = (curPrio (t)))
.

Definition OS_EventTaskRdy_entail_wit_2 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH6 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH7 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH8 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH9 : (0 <= msk_pre)) (PreH10 : (msk_pre < 256)) (PreH11 : (0 <= pend_stat_pre)) (PreH12 : (pend_stat_pre < 256)) (PreH13 : ((Zlength (rows)) = 8)) (PreH14 : (0 <= (curPrio (t)))) (PreH15 : ((curPrio (t)) < 64)) (PreH16 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH17 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH18 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH19 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH20 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH21 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH22 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH23 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH24 : (pevent_pre = (event_addr (sg) (eid)))) (PreH25 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH26 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH27 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH28 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
.

Definition OS_EventTaskRdy_entail_wit_3 := 
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH4 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH5 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH6 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH7 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH8 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH9 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH10 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH11 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH12 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH13 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH14 : (0 <= msk_pre)) (PreH15 : (msk_pre < 256)) (PreH16 : (0 <= pend_stat_pre)) (PreH17 : (pend_stat_pre < 256)) (PreH18 : ((Zlength (rows)) = 8)) (PreH19 : (0 <= (curPrio (t)))) (PreH20 : ((curPrio (t)) < 64)) (PreH21 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH22 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH23 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH24 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH25 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH26 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH27 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH28 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH29 : (pevent_pre = (event_addr (sg) (eid)))) (PreH30 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH31 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH32 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH33 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (t)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((msg (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0))) ” 
  &&  “ ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256) ” 
  &&  “ ((dly (t)) <= UINT_MAX) ” 
  &&  “ ((dly (t)) >= 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (t)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((msg (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
) \/
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((dly (t)) <= UINT_MAX)) (PreH2 : ((dly (t)) >= 0)) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH6 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH7 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH8 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH11 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH12 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH13 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH16 : (0 <= msk_pre)) (PreH17 : (msk_pre < 256)) (PreH18 : (0 <= pend_stat_pre)) (PreH19 : (pend_stat_pre < 256)) (PreH20 : ((Zlength (rows)) = 8)) (PreH21 : (0 <= (curPrio (t)))) (PreH22 : ((curPrio (t)) < 64)) (PreH23 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH24 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH25 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH26 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH27 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH28 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH29 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH30 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH31 : (pevent_pre = (event_addr (sg) (eid)))) (PreH32 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH33 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH34 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH35 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  TT && emp 
|--
  “ ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256) ” 
  &&  “ (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0))) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= group) ”
  &&  emp
).

Definition OS_EventTaskRdy_entail_wit_3_split_goal_1 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((dly (t)) <= UINT_MAX)) (PreH2 : ((dly (t)) >= 0)) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH6 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH7 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH8 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH11 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH12 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH13 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH16 : (0 <= msk_pre)) (PreH17 : (msk_pre < 256)) (PreH18 : (0 <= pend_stat_pre)) (PreH19 : (pend_stat_pre < 256)) (PreH20 : ((Zlength (rows)) = 8)) (PreH21 : (0 <= (curPrio (t)))) (PreH22 : ((curPrio (t)) < 64)) (PreH23 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH24 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH25 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH26 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH27 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH28 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH29 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH30 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH31 : (pevent_pre = (event_addr (sg) (eid)))) (PreH32 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH33 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH34 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH35 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)
.

Definition OS_EventTaskRdy_entail_wit_3_split_goal_2 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((dly (t)) <= UINT_MAX)) (PreH2 : ((dly (t)) >= 0)) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH6 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH7 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH8 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH11 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH12 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH13 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH16 : (0 <= msk_pre)) (PreH17 : (msk_pre < 256)) (PreH18 : (0 <= pend_stat_pre)) (PreH19 : (pend_stat_pre < 256)) (PreH20 : ((Zlength (rows)) = 8)) (PreH21 : (0 <= (curPrio (t)))) (PreH22 : ((curPrio (t)) < 64)) (PreH23 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH24 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH25 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH26 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH27 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH28 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH29 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH30 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH31 : (pevent_pre = (event_addr (sg) (eid)))) (PreH32 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH33 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH34 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH35 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
.

Definition OS_EventTaskRdy_entail_wit_3_split_goal_3 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((dly (t)) <= UINT_MAX)) (PreH2 : ((dly (t)) >= 0)) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH6 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH7 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH8 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH11 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH12 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH13 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH16 : (0 <= msk_pre)) (PreH17 : (msk_pre < 256)) (PreH18 : (0 <= pend_stat_pre)) (PreH19 : (pend_stat_pre < 256)) (PreH20 : ((Zlength (rows)) = 8)) (PreH21 : (0 <= (curPrio (t)))) (PreH22 : ((curPrio (t)) < 64)) (PreH23 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH24 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH25 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH26 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH27 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH28 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH29 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH30 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH31 : (pevent_pre = (event_addr (sg) (eid)))) (PreH32 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH33 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH34 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH35 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (group < 256)
.

Definition OS_EventTaskRdy_entail_wit_3_split_goal_4 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((dly (t)) <= UINT_MAX)) (PreH2 : ((dly (t)) >= 0)) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH6 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH7 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH8 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH11 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH12 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH13 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH16 : (0 <= msk_pre)) (PreH17 : (msk_pre < 256)) (PreH18 : (0 <= pend_stat_pre)) (PreH19 : (pend_stat_pre < 256)) (PreH20 : ((Zlength (rows)) = 8)) (PreH21 : (0 <= (curPrio (t)))) (PreH22 : ((curPrio (t)) < 64)) (PreH23 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH24 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH25 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH26 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH27 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH28 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH29 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH30 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH31 : (pevent_pre = (event_addr (sg) (eid)))) (PreH32 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH33 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH34 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH35 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (0 <= group)
.

Definition OS_EventTaskRdy_entail_wit_4_1 := 
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH2 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH3 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0)) (PreH4 : (0 <= group)) (PreH5 : (group < 256)) (PreH6 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH7 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH8 : ((dly (t)) <= UINT_MAX)) (PreH9 : ((dly (t)) >= 0)) (PreH10 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH11 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH12 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH16 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH22 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH23 : (0 <= msk_pre)) (PreH24 : (msk_pre < 256)) (PreH25 : (0 <= pend_stat_pre)) (PreH26 : (pend_stat_pre < 256)) (PreH27 : ((Zlength (rows)) = 8)) (PreH28 : (0 <= (curPrio (t)))) (PreH29 : ((curPrio (t)) < 64)) (PreH30 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH31 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH32 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH34 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH36 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH37 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH38 : (pevent_pre = (event_addr (sg) (eid)))) (PreH39 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH40 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH41 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH42 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
|--
  (event_task_rdy_post sg tasks eid e tid t pmsg_pre msk_pre pend_stat_pre group rows (curPrio (t)) )
) \/
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH5 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0)) (PreH6 : (0 <= group)) (PreH7 : (group < 256)) (PreH8 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH9 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH10 : ((dly (t)) <= UINT_MAX)) (PreH11 : ((dly (t)) >= 0)) (PreH12 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH13 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH14 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH15 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH16 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH17 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH18 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH19 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH22 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH23 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH24 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH25 : (0 <= msk_pre)) (PreH26 : (msk_pre < 256)) (PreH27 : (0 <= pend_stat_pre)) (PreH28 : (pend_stat_pre < 256)) (PreH29 : ((Zlength (rows)) = 8)) (PreH30 : (0 <= (curPrio (t)))) (PreH31 : ((curPrio (t)) < 64)) (PreH32 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH33 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH34 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH35 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH36 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH37 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH38 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH39 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH40 : (pevent_pre = (event_addr (sg) (eid)))) (PreH41 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH42 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH43 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH44 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
|--
  (event_task_rdy_post sg tasks eid e tid t pmsg_pre msk_pre pend_stat_pre group rows (curPrio (t)) )
).

Definition OS_EventTaskRdy_entail_wit_4_1_split_goal_spatial := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH5 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0)) (PreH6 : (0 <= group)) (PreH7 : (group < 256)) (PreH8 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH9 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH10 : ((dly (t)) <= UINT_MAX)) (PreH11 : ((dly (t)) >= 0)) (PreH12 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH13 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH14 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH15 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH16 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH17 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH18 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH19 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH22 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH23 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH24 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH25 : (0 <= msk_pre)) (PreH26 : (msk_pre < 256)) (PreH27 : (0 <= pend_stat_pre)) (PreH28 : (pend_stat_pre < 256)) (PreH29 : ((Zlength (rows)) = 8)) (PreH30 : (0 <= (curPrio (t)))) (PreH31 : ((curPrio (t)) < 64)) (PreH32 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH33 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH34 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH35 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH36 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH37 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH38 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH39 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH40 : (pevent_pre = (event_addr (sg) (eid)))) (PreH41 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH42 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH43 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH44 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
|--
  (event_task_rdy_post sg tasks eid e tid t pmsg_pre msk_pre pend_stat_pre group rows (curPrio (t)) )
.

Definition OS_EventTaskRdy_entail_wit_4_2 := 
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH2 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH3 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0)) (PreH4 : (0 <= group)) (PreH5 : (group < 256)) (PreH6 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH7 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH8 : ((dly (t)) <= UINT_MAX)) (PreH9 : ((dly (t)) >= 0)) (PreH10 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH11 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH12 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH16 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH22 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH23 : (0 <= msk_pre)) (PreH24 : (msk_pre < 256)) (PreH25 : (0 <= pend_stat_pre)) (PreH26 : (pend_stat_pre < 256)) (PreH27 : ((Zlength (rows)) = 8)) (PreH28 : (0 <= (curPrio (t)))) (PreH29 : ((curPrio (t)) < 64)) (PreH30 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH31 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH32 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH34 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH36 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH37 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH38 : (pevent_pre = (event_addr (sg) (eid)))) (PreH39 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH40 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH41 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH42 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
|--
  (event_task_rdy_post sg tasks eid e tid t pmsg_pre msk_pre pend_stat_pre group rows (curPrio (t)) )
) \/
(
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH5 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0)) (PreH6 : (0 <= group)) (PreH7 : (group < 256)) (PreH8 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH9 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH10 : ((dly (t)) <= UINT_MAX)) (PreH11 : ((dly (t)) >= 0)) (PreH12 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH13 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH14 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH15 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH16 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH17 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH18 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH19 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH22 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH23 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH24 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH25 : (0 <= msk_pre)) (PreH26 : (msk_pre < 256)) (PreH27 : (0 <= pend_stat_pre)) (PreH28 : (pend_stat_pre < 256)) (PreH29 : ((Zlength (rows)) = 8)) (PreH30 : (0 <= (curPrio (t)))) (PreH31 : ((curPrio (t)) < 64)) (PreH32 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH33 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH34 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH35 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH36 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH37 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH38 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH39 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH40 : (pevent_pre = (event_addr (sg) (eid)))) (PreH41 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH42 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH43 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH44 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
|--
  (event_task_rdy_post sg tasks eid e tid t pmsg_pre msk_pre pend_stat_pre group rows (curPrio (t)) )
).

Definition OS_EventTaskRdy_entail_wit_4_2_split_goal_spatial := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH5 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0)) (PreH6 : (0 <= group)) (PreH7 : (group < 256)) (PreH8 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH9 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH10 : ((dly (t)) <= UINT_MAX)) (PreH11 : ((dly (t)) >= 0)) (PreH12 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH13 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH14 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH15 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH16 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH17 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH18 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH19 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH22 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH23 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH24 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH25 : (0 <= msk_pre)) (PreH26 : (msk_pre < 256)) (PreH27 : (0 <= pend_stat_pre)) (PreH28 : (pend_stat_pre < 256)) (PreH29 : ((Zlength (rows)) = 8)) (PreH30 : (0 <= (curPrio (t)))) (PreH31 : ((curPrio (t)) < 64)) (PreH32 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH33 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH34 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH35 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH36 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH37 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH38 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH39 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH40 : (pevent_pre = (event_addr (sg) (eid)))) (PreH41 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH42 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH43 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH44 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
|--
  (event_task_rdy_post sg tasks eid e tid t pmsg_pre msk_pre pend_stat_pre group rows (curPrio (t)) )
.

Definition OS_EventTaskRdy_return_wit_1 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) ,
  (event_task_rdy_post sg tasks eid e tid t pmsg_pre msk_pre pend_stat_pre group rows (curPrio (t)) )
|--
  (event_task_rdy_post sg tasks eid e tid t pmsg_pre msk_pre pend_stat_pre group rows (curPrio (t)) )
.

Definition OS_EventTaskRdy_partial_solve_wit_1_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (pevent_pre = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_pre sg tasks eid e tid t msk_pre pend_stat_pre group rows )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_1_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (pevent_pre = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (event_task_rdy_pre sg tasks eid e tid t msk_pre pend_stat_pre group rows )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (event_task_rdy_pre sg tasks eid e tid t msk_pre pend_stat_pre group rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_1 := OS_EventTaskRdy_partial_solve_wit_1_pure -> OS_EventTaskRdy_partial_solve_wit_1_aux.

Definition OS_EventTaskRdy_partial_solve_wit_2_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH4 : (0 <= msk_pre)) (PreH5 : (msk_pre < 256)) (PreH6 : (0 <= pend_stat_pre)) (PreH7 : (pend_stat_pre < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= (curPrio (t)))) (PreH10 : ((curPrio (t)) < 64)) (PreH11 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH12 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH13 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH14 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH15 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH16 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH17 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH19 : (pevent_pre = (event_addr (sg) (eid)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH22 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH23 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (unmap_table_rep sg )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_2_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH4 : (0 <= msk_pre)) (PreH5 : (msk_pre < 256)) (PreH6 : (0 <= pend_stat_pre)) (PreH7 : (pend_stat_pre < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= (curPrio (t)))) (PreH10 : ((curPrio (t)) < 64)) (PreH11 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH12 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH13 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH14 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH15 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH16 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH17 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH19 : (pevent_pre = (event_addr (sg) (eid)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH22 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH23 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (unmap_table_rep sg )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (unmap_table_rep sg )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_2 := OS_EventTaskRdy_partial_solve_wit_2_pure -> OS_EventTaskRdy_partial_solve_wit_2_aux.

Definition OS_EventTaskRdy_partial_solve_wit_3_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH4 : (0 <= msk_pre)) (PreH5 : (msk_pre < 256)) (PreH6 : (0 <= pend_stat_pre)) (PreH7 : (pend_stat_pre < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= (curPrio (t)))) (PreH10 : ((curPrio (t)) < 64)) (PreH11 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH12 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH13 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH14 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH15 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH16 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH17 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH19 : (pevent_pre = (event_addr (sg) (eid)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH22 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH23 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_3_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH4 : (0 <= msk_pre)) (PreH5 : (msk_pre < 256)) (PreH6 : (0 <= pend_stat_pre)) (PreH7 : (pend_stat_pre < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= (curPrio (t)))) (PreH10 : ((curPrio (t)) < 64)) (PreH11 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH12 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH13 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH14 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH15 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH16 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH17 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH18 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH19 : (pevent_pre = (event_addr (sg) (eid)))) (PreH20 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH21 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH22 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH23 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_3 := OS_EventTaskRdy_partial_solve_wit_3_pure -> OS_EventTaskRdy_partial_solve_wit_3_aux.

Definition OS_EventTaskRdy_partial_solve_wit_4_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH4 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH5 : (0 <= msk_pre)) (PreH6 : (msk_pre < 256)) (PreH7 : (0 <= pend_stat_pre)) (PreH8 : (pend_stat_pre < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : (0 <= (curPrio (t)))) (PreH11 : ((curPrio (t)) < 64)) (PreH12 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH13 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH14 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH15 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH16 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH18 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH20 : (pevent_pre = (event_addr (sg) (eid)))) (PreH21 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH22 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH23 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH24 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_4_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH4 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH5 : (0 <= msk_pre)) (PreH6 : (msk_pre < 256)) (PreH7 : (0 <= pend_stat_pre)) (PreH8 : (pend_stat_pre < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : (0 <= (curPrio (t)))) (PreH11 : ((curPrio (t)) < 64)) (PreH12 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH13 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH14 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH15 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH16 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH17 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH18 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH19 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH20 : (pevent_pre = (event_addr (sg) (eid)))) (PreH21 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH22 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH23 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH24 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_4 := OS_EventTaskRdy_partial_solve_wit_4_pure -> OS_EventTaskRdy_partial_solve_wit_4_aux.

Definition OS_EventTaskRdy_partial_solve_wit_5 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH6 : (0 <= msk_pre)) (PreH7 : (msk_pre < 256)) (PreH8 : (0 <= pend_stat_pre)) (PreH9 : (pend_stat_pre < 256)) (PreH10 : ((Zlength (rows)) = 8)) (PreH11 : (0 <= (curPrio (t)))) (PreH12 : ((curPrio (t)) < 64)) (PreH13 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH14 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH15 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH16 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH17 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH18 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH19 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH20 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH21 : (pevent_pre = (event_addr (sg) (eid)))) (PreH22 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH23 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH24 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH25 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_6_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH6 : (0 <= msk_pre)) (PreH7 : (msk_pre < 256)) (PreH8 : (0 <= pend_stat_pre)) (PreH9 : (pend_stat_pre < 256)) (PreH10 : ((Zlength (rows)) = 8)) (PreH11 : (0 <= (curPrio (t)))) (PreH12 : ((curPrio (t)) < 64)) (PreH13 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH14 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH15 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH16 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH17 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH18 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH19 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH20 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH21 : (pevent_pre = (event_addr (sg) (eid)))) (PreH22 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH23 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH24 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH25 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  ((( &( "y" ) )) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_6_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH2 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH3 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH6 : (0 <= msk_pre)) (PreH7 : (msk_pre < 256)) (PreH8 : (0 <= pend_stat_pre)) (PreH9 : (pend_stat_pre < 256)) (PreH10 : ((Zlength (rows)) = 8)) (PreH11 : (0 <= (curPrio (t)))) (PreH12 : ((curPrio (t)) < 64)) (PreH13 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH14 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH15 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH16 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH17 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH18 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH19 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH20 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH21 : (pevent_pre = (event_addr (sg) (eid)))) (PreH22 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH23 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH24 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH25 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_6 := OS_EventTaskRdy_partial_solve_wit_6_pure -> OS_EventTaskRdy_partial_solve_wit_6_aux.

Definition OS_EventTaskRdy_partial_solve_wit_7_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((tcb_y_of_prio ((curPrio (t)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH2 : ((tcb_x_of_prio ((curPrio (t)))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH3 : ((curPrio (t)) = (curPrio (t)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH6 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH7 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (0 <= msk_pre)) (PreH11 : (msk_pre < 256)) (PreH12 : (0 <= pend_stat_pre)) (PreH13 : (pend_stat_pre < 256)) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (0 <= (curPrio (t)))) (PreH16 : ((curPrio (t)) < 64)) (PreH17 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH18 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH19 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH20 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH22 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH23 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH24 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH25 : (pevent_pre = (event_addr (sg) (eid)))) (PreH26 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH27 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH28 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH29 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_7_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((tcb_y_of_prio ((curPrio (t)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH2 : ((tcb_x_of_prio ((curPrio (t)))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH3 : ((curPrio (t)) = (curPrio (t)))) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH6 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH7 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (0 <= msk_pre)) (PreH11 : (msk_pre < 256)) (PreH12 : (0 <= pend_stat_pre)) (PreH13 : (pend_stat_pre < 256)) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (0 <= (curPrio (t)))) (PreH16 : ((curPrio (t)) < 64)) (PreH17 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH18 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH19 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH20 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH22 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH23 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH24 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH25 : (pevent_pre = (event_addr (sg) (eid)))) (PreH26 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH27 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH28 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH29 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_7 := OS_EventTaskRdy_partial_solve_wit_7_pure -> OS_EventTaskRdy_partial_solve_wit_7_aux.

Definition OS_EventTaskRdy_partial_solve_wit_8_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH2 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH3 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH6 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH7 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (0 <= msk_pre)) (PreH11 : (msk_pre < 256)) (PreH12 : (0 <= pend_stat_pre)) (PreH13 : (pend_stat_pre < 256)) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (0 <= (curPrio (t)))) (PreH16 : ((curPrio (t)) < 64)) (PreH17 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH18 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH19 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH20 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH22 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH23 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH24 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH25 : (pevent_pre = (event_addr (sg) (eid)))) (PreH26 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH27 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH28 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH29 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_8_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid)))) (PreH2 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH3 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH4 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH5 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH6 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH7 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH10 : (0 <= msk_pre)) (PreH11 : (msk_pre < 256)) (PreH12 : (0 <= pend_stat_pre)) (PreH13 : (pend_stat_pre < 256)) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (0 <= (curPrio (t)))) (PreH16 : ((curPrio (t)) < 64)) (PreH17 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH18 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH19 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH20 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH21 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH22 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH23 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH24 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH25 : (pevent_pre = (event_addr (sg) (eid)))) (PreH26 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH27 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH28 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH29 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_8 := OS_EventTaskRdy_partial_solve_wit_8_pure -> OS_EventTaskRdy_partial_solve_wit_8_aux.

Definition OS_EventTaskRdy_partial_solve_wit_9 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH3 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH4 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH5 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH6 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH7 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH8 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH10 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH11 : (0 <= msk_pre)) (PreH12 : (msk_pre < 256)) (PreH13 : (0 <= pend_stat_pre)) (PreH14 : (pend_stat_pre < 256)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (0 <= (curPrio (t)))) (PreH17 : ((curPrio (t)) < 64)) (PreH18 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH19 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH20 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH21 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH22 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH23 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH24 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH25 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH26 : (pevent_pre = (event_addr (sg) (eid)))) (PreH27 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH28 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH29 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH30 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_partial_solve_wit_10_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH3 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH4 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH5 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH6 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH7 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH8 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH10 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH11 : (0 <= msk_pre)) (PreH12 : (msk_pre < 256)) (PreH13 : (0 <= pend_stat_pre)) (PreH14 : (pend_stat_pre < 256)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (0 <= (curPrio (t)))) (PreH17 : ((curPrio (t)) < 64)) (PreH18 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH19 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH20 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH21 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH22 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH23 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH24 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH25 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH26 : (pevent_pre = (event_addr (sg) (eid)))) (PreH27 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH28 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH29 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH30 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (t)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((msg (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_10_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH3 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH4 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH5 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH6 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH7 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH8 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH10 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH11 : (0 <= msk_pre)) (PreH12 : (msk_pre < 256)) (PreH13 : (0 <= pend_stat_pre)) (PreH14 : (pend_stat_pre < 256)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (0 <= (curPrio (t)))) (PreH17 : ((curPrio (t)) < 64)) (PreH18 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH19 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH20 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH21 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH22 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH23 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH24 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH25 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH26 : (pevent_pre = (event_addr (sg) (eid)))) (PreH27 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH28 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH29 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH30 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (t)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((msg (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (t)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((msg (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
.

Definition OS_EventTaskRdy_partial_solve_wit_10 := OS_EventTaskRdy_partial_solve_wit_10_pure -> OS_EventTaskRdy_partial_solve_wit_10_aux.

Definition OS_EventTaskRdy_partial_solve_wit_11_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH5 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH6 : ((dly (t)) <= UINT_MAX)) (PreH7 : ((dly (t)) >= 0)) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH11 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH12 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH16 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH20 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH21 : (0 <= msk_pre)) (PreH22 : (msk_pre < 256)) (PreH23 : (0 <= pend_stat_pre)) (PreH24 : (pend_stat_pre < 256)) (PreH25 : ((Zlength (rows)) = 8)) (PreH26 : (0 <= (curPrio (t)))) (PreH27 : ((curPrio (t)) < 64)) (PreH28 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH29 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH30 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH31 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH32 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH34 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH36 : (pevent_pre = (event_addr (sg) (eid)))) (PreH37 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH38 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH39 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH40 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_11_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH5 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH6 : ((dly (t)) <= UINT_MAX)) (PreH7 : ((dly (t)) >= 0)) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH11 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH12 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH16 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH20 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH21 : (0 <= msk_pre)) (PreH22 : (msk_pre < 256)) (PreH23 : (0 <= pend_stat_pre)) (PreH24 : (pend_stat_pre < 256)) (PreH25 : ((Zlength (rows)) = 8)) (PreH26 : (0 <= (curPrio (t)))) (PreH27 : ((curPrio (t)) < 64)) (PreH28 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH29 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH30 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH31 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH32 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH34 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH36 : (pevent_pre = (event_addr (sg) (eid)))) (PreH37 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH38 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH39 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH40 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0))) ” 
  &&  “ ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256) ” 
  &&  “ ((dly (t)) <= UINT_MAX) ” 
  &&  “ ((dly (t)) >= 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
.

Definition OS_EventTaskRdy_partial_solve_wit_11 := OS_EventTaskRdy_partial_solve_wit_11_pure -> OS_EventTaskRdy_partial_solve_wit_11_aux.

Definition OS_EventTaskRdy_partial_solve_wit_12_pure := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH5 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH6 : ((dly (t)) <= UINT_MAX)) (PreH7 : ((dly (t)) >= 0)) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH11 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH12 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH16 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH20 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH21 : (0 <= msk_pre)) (PreH22 : (msk_pre < 256)) (PreH23 : (0 <= pend_stat_pre)) (PreH24 : (pend_stat_pre < 256)) (PreH25 : ((Zlength (rows)) = 8)) (PreH26 : (0 <= (curPrio (t)))) (PreH27 : ((curPrio (t)) < 64)) (PreH28 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH29 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH30 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH31 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH32 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH34 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH36 : (pevent_pre = (event_addr (sg) (eid)))) (PreH37 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH38 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH39 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH40 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((( &( "x" ) )) # UChar  |-> (tcb_x_of_prio ((curPrio (t)))))
  **  ((( &( "prio" ) )) # UChar  |-> (curPrio (t)))
  **  (unmap_table_rep sg )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  ((( &( "msk" ) )) # UChar  |-> msk_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ”
.

Definition OS_EventTaskRdy_partial_solve_wit_12_aux := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH5 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH6 : ((dly (t)) <= UINT_MAX)) (PreH7 : ((dly (t)) >= 0)) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH11 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH12 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH16 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH20 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH21 : (0 <= msk_pre)) (PreH22 : (msk_pre < 256)) (PreH23 : (0 <= pend_stat_pre)) (PreH24 : (pend_stat_pre < 256)) (PreH25 : ((Zlength (rows)) = 8)) (PreH26 : (0 <= (curPrio (t)))) (PreH27 : ((curPrio (t)) < 64)) (PreH28 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH29 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH30 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH31 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH32 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH34 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH36 : (pevent_pre = (event_addr (sg) (eid)))) (PreH37 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH38 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH39 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH40 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0))) ” 
  &&  “ ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256) ” 
  &&  “ ((dly (t)) <= UINT_MAX) ” 
  &&  “ ((dly (t)) >= 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
.

Definition OS_EventTaskRdy_partial_solve_wit_12 := OS_EventTaskRdy_partial_solve_wit_12_pure -> OS_EventTaskRdy_partial_solve_wit_12_aux.

Definition OS_EventTaskRdy_partial_solve_wit_13 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH5 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH6 : ((dly (t)) <= UINT_MAX)) (PreH7 : ((dly (t)) >= 0)) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH11 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH12 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH16 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH20 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH21 : (0 <= msk_pre)) (PreH22 : (msk_pre < 256)) (PreH23 : (0 <= pend_stat_pre)) (PreH24 : (pend_stat_pre < 256)) (PreH25 : ((Zlength (rows)) = 8)) (PreH26 : (0 <= (curPrio (t)))) (PreH27 : ((curPrio (t)) < 64)) (PreH28 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH29 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH30 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH31 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH32 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH34 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH36 : (pevent_pre = (event_addr (sg) (eid)))) (PreH37 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH38 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH39 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH40 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (event_task_remove_pre (task_slot_addr (sg) (tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
|--
  “ ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0))) ” 
  &&  “ ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256) ” 
  &&  “ ((dly (t)) <= UINT_MAX) ” 
  &&  “ ((dly (t)) >= 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (event_task_remove_pre (task_slot_addr (sg) (tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
.

Definition OS_EventTaskRdy_partial_solve_wit_14 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH5 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH6 : ((dly (t)) <= UINT_MAX)) (PreH7 : ((dly (t)) >= 0)) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH11 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH12 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH16 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH20 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH21 : (0 <= msk_pre)) (PreH22 : (msk_pre < 256)) (PreH23 : (0 <= pend_stat_pre)) (PreH24 : (pend_stat_pre < 256)) (PreH25 : ((Zlength (rows)) = 8)) (PreH26 : (0 <= (curPrio (t)))) (PreH27 : ((curPrio (t)) < 64)) (PreH28 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH29 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH30 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH31 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH32 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH34 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH36 : (pevent_pre = (event_addr (sg) (eid)))) (PreH37 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH38 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH39 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH40 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (event_task_remove_pre (task_slot_addr (sg) (tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
|--
  “ ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0))) ” 
  &&  “ ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256) ” 
  &&  “ ((dly (t)) <= UINT_MAX) ” 
  &&  “ ((dly (t)) >= 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (event_task_remove_pre (task_slot_addr (sg) (tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
.

Definition OS_EventTaskRdy_partial_solve_wit_15 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH5 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH6 : ((dly (t)) <= UINT_MAX)) (PreH7 : ((dly (t)) >= 0)) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH11 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH12 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH16 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH20 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH21 : (0 <= msk_pre)) (PreH22 : (msk_pre < 256)) (PreH23 : (0 <= pend_stat_pre)) (PreH24 : (pend_stat_pre < 256)) (PreH25 : ((Zlength (rows)) = 8)) (PreH26 : (0 <= (curPrio (t)))) (PreH27 : ((curPrio (t)) < 64)) (PreH28 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH29 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH30 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH31 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH32 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH34 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH36 : (pevent_pre = (event_addr (sg) (eid)))) (PreH37 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH38 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH39 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH40 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (event_task_remove_post (task_slot_addr (sg) (tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
|--
  “ ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) <> 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0))) ” 
  &&  “ ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256) ” 
  &&  “ ((dly (t)) <= UINT_MAX) ” 
  &&  “ ((dly (t)) >= 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (event_task_remove_post (task_slot_addr (sg) (tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
.

Definition OS_EventTaskRdy_partial_solve_wit_16 := 
forall (pend_stat_pre: Z) (msk_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))) (PreH5 : ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256)) (PreH6 : ((dly (t)) <= UINT_MAX)) (PreH7 : ((dly (t)) >= 0)) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH10 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH11 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH12 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH13 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH14 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH15 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH16 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH17 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH18 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH19 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH20 : (event_task_rdy_entry sg tasks eid e tid t )) (PreH21 : (0 <= msk_pre)) (PreH22 : (msk_pre < 256)) (PreH23 : (0 <= pend_stat_pre)) (PreH24 : (pend_stat_pre < 256)) (PreH25 : ((Zlength (rows)) = 8)) (PreH26 : (0 <= (curPrio (t)))) (PreH27 : ((curPrio (t)) < 64)) (PreH28 : ((event_wait_priority (tasks) (e)) = (curPrio (t)))) (PreH29 : ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid)))) (PreH30 : ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t)))))) (PreH31 : ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t)))))) (PreH32 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH33 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) (PreH34 : (0 <= (tcb_x_of_prio ((curPrio (t)))))) (PreH35 : ((tcb_x_of_prio ((curPrio (t)))) < 8)) (PreH36 : (pevent_pre = (event_addr (sg) (eid)))) (PreH37 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) (PreH38 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH39 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH40 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (event_task_remove_post (task_slot_addr (sg) (tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
|--
  “ ((Z.land (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))) 8) = 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0))) ” 
  &&  “ ((Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) < 256) ” 
  &&  “ ((dly (t)) <= UINT_MAX) ” 
  &&  “ ((dly (t)) >= 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk_pre) ” 
  &&  “ (msk_pre < 256) ” 
  &&  “ (0 <= pend_stat_pre) ” 
  &&  “ (pend_stat_pre < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (event_task_remove_post (task_slot_addr (sg) (tid)) &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp") &(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (t))))) (8))))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> pmsg_pre)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (t)))) (unsigned_last_nbits ((Z.lnot msk_pre)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  (event_task_rdy_tcb_frame (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  (unmap_table_rep sg )
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor group (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (t))))) (8))))
.

Definition OS_EventTaskRdy_which_implies_wit_1 := 
(
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ” 
  &&  “ (0 <= msk) ” 
  &&  “ (msk < 256) ” 
  &&  “ (0 <= pend_stat) ” 
  &&  “ (pend_stat < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ”
  &&  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (unmap_table_rep sg )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
) \/
(
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ” 
  &&  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ” 
  &&  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ” 
  &&  “ ((curPrio (t)) < 64) ” 
  &&  “ (0 <= (curPrio (t))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pend_stat < 256) ” 
  &&  “ (0 <= pend_stat) ” 
  &&  “ (msk < 256) ” 
  &&  “ (0 <= msk) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ”
  &&  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (unmap_table_rep sg )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
).

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_1 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((tcb_x_of_prio ((curPrio (t)))) < 8) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_2 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (0 <= (tcb_x_of_prio ((curPrio (t))))) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_3 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_4 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_5 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))) = (tcb_x_of_prio ((curPrio (t))))) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_6 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))) = (tcb_y_of_prio ((curPrio (t))))) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_7 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((prioTbl (tasks) ((curPrio (t)))) = (PTTask (tid))) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_8 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((event_wait_priority (tasks) (e)) = (curPrio (t))) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_9 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((curPrio (t)) < 64) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_10 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (0 <= (curPrio (t))) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_11 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ ((Zlength (rows)) = 8) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_12 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (pend_stat < 256) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_13 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (0 <= pend_stat) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_14 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (msk < 256) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_15 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (0 <= msk) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_16 := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  “ (event_task_rdy_entry sg tasks eid e tid t ) ”
.

Definition OS_EventTaskRdy_which_implies_wit_1_split_goal_spatial := 
forall (rows: (@list Z)) (group: Z) (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pend_stat: Z) (msk: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (event_task_rdy_pre sg tasks eid e tid t msk pend_stat group rows )
|--
  (tcb64_storage_rep (task_slot_addr (sg) (tid)) (task_tcb64_image (sg) (t)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
  **  (event_task_remove_ecb_frame (cfgEventNames ((osKernelConfig (sg)))) (event_addr (sg) (eid)) (event_image (sg) (tasks) (e)) (tcb_y_of_prio ((curPrio (t)))) )
  **  (unmap_table_rep sg )
  **  (store_prio_tbl sg (prioTbl (tasks)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
.

Definition OS_EventTaskRdy_which_implies_wit_2 := 
(
forall (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (unmap_table_rep sg )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
  &&  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
) \/
(
forall (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (unmap_table_rep sg )
|--
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
).

Definition OS_EventTaskRdy_which_implies_wit_2_split_goal_spatial := 
forall (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (unmap_table_rep sg )
|--
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
.

Definition OS_EventTaskRdy_which_implies_wit_3 := 
(
forall (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
  &&  (unmap_table_rep sg )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
) \/
(
forall (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
|--
  (unmap_table_rep sg )
).

Definition OS_EventTaskRdy_which_implies_wit_3_split_goal_spatial := 
forall (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_grp ((waitList (e))) (tasks)) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_grp ((waitList (e))) (tasks)))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_grp ((waitList (e))) (tasks)) 0 256 unmap_table )
|--
  (unmap_table_rep sg )
.

Definition OS_EventTaskRdy_which_implies_wit_4 := 
(
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (unmap_table_rep sg )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
  &&  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
) \/
(
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (unmap_table_rep sg )
|--
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
).

Definition OS_EventTaskRdy_which_implies_wit_4_split_goal_spatial := 
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (unmap_table_rep sg )
|--
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
.

Definition OS_EventTaskRdy_which_implies_wit_5 := 
(
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
  &&  (unmap_table_rep sg )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
) \/
(
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
|--
  (unmap_table_rep sg )
).

Definition OS_EventTaskRdy_which_implies_wit_5_split_goal_spatial := 
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg)))) ,
  (((( &( "OSUnMapTbl" ) ) + ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) * sizeof(UCHAR)))) # UChar  |-> (unmap_value ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))))
  **  (UCharArray.missing_i (g_OSUnMapTbl (sg)) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) 0 256 unmap_table )
|--
  (unmap_table_rep sg )
.

Definition OS_EventTaskRdy_which_implies_wit_6 := 
(
forall (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) ,
  (store_prio_tbl sg (prioTbl (tasks)) )
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
) \/
(
forall (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) ,
  (store_prio_tbl sg (prioTbl (tasks)) )
|--
  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
).

Definition OS_EventTaskRdy_which_implies_wit_6_split_goal_spatial := 
forall (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) ,
  (store_prio_tbl sg (prioTbl (tasks)) )
|--
  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
.

Definition OS_EventTaskRdy_which_implies_wit_7 := 
(
forall (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (event_task_rdy_entry sg tasks eid e tid t ) ”
  &&  (store_prio_tbl sg (prioTbl (tasks)) )
) \/
(
forall (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
|--
  (store_prio_tbl sg (prioTbl (tasks)) )
).

Definition OS_EventTaskRdy_which_implies_wit_7_split_goal_spatial := 
forall (t: TaskAbstractState) (tid: Z) (e: OSEventAbstractState) (eid: Z) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg)))) (PreH2 : (event_task_rdy_entry sg tasks eid e tid t )) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((curPrio (t)) * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (event_task_rdy_prio_frame sg tasks (curPrio (t)) )
|--
  (store_prio_tbl sg (prioTbl (tasks)) )
.

Definition OS_EventTaskRdy_which_implies_wit_8 := 
(
forall (t: TaskAbstractState) (sg: StableGlobVars) (ptcb: Z) ,
  (tcb64_storage_rep ptcb (task_tcb64_image (sg) (t)) )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (t)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((msg (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame ptcb (task_tcb64_image (sg) (t)) )
) \/
(
forall (t: TaskAbstractState) (sg: StableGlobVars) (ptcb: Z) ,
  (tcb64_storage_rep ptcb (task_tcb64_image (sg) (t)) )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (t)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((msg (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame ptcb (task_tcb64_image (sg) (t)) )
).

Definition OS_EventTaskRdy_which_implies_wit_8_split_goal_spatial := 
forall (t: TaskAbstractState) (sg: StableGlobVars) (ptcb: Z) ,
  (tcb64_storage_rep ptcb (task_tcb64_image (sg) (t)) )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (t)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBMsg")) # Ptr  |-> (encode_msg ((msg (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  (event_task_rdy_tcb_frame ptcb (task_tcb64_image (sg) (t)) )
.

Definition OS_EventTaskRdy_which_implies_wit_9 := 
(
forall (rows: (@list Z)) (t: TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) ,
  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
) \/
(
forall (rows: (@list Z)) (t: TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) ,
  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
).

Definition OS_EventTaskRdy_which_implies_wit_9_split_goal_spatial := 
forall (rows: (@list Z)) (t: TaskAbstractState) (sg: StableGlobVars) (PreH1 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) ,
  (UCharArray.full (g_OSRdyTbl (sg)) 8 rows )
|--
  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((tcb_y_of_prio ((curPrio (t))))) (rows) (0)))
  **  (UCharArray.missing_i (g_OSRdyTbl (sg)) (tcb_y_of_prio ((curPrio (t)))) 0 8 rows )
.

Definition OS_EventTaskRdy_which_implies_wit_10 := 
(
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (ptcb: Z) (pevent: Z) (PreH1 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH2 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
|--
  (event_task_remove_pre ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
) \/
(
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (ptcb: Z) (pevent: Z) (PreH1 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH2 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
|--
  (event_task_remove_pre ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
).

Definition OS_EventTaskRdy_which_implies_wit_10_split_goal_spatial := 
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (ptcb: Z) (pevent: Z) (PreH1 : (0 <= (tcb_y_of_prio ((curPrio (t)))))) (PreH2 : ((tcb_y_of_prio ((curPrio (t)))) < 8)) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((eventPtr (t)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (e))) (tasks)))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))))
|--
  (event_task_remove_pre ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
.

Definition OS_EventTaskRdy_which_implies_wit_11 := 
(
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (pevent: Z) (ptcb: Z) ,
  (event_task_remove_post ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
) \/
(
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (pevent: Z) (ptcb: Z) ,
  (event_task_remove_post ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
|--
  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
).

Definition OS_EventTaskRdy_which_implies_wit_11_split_goal_1 := 
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (pevent: Z) (ptcb: Z) ,
  (event_task_remove_post ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
|--
  “ ((tcb_y_of_prio ((curPrio (t)))) < 8) ”
.

Definition OS_EventTaskRdy_which_implies_wit_11_split_goal_2 := 
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (pevent: Z) (ptcb: Z) ,
  (event_task_remove_post ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (t))))) ”
.

Definition OS_EventTaskRdy_which_implies_wit_11_split_goal_spatial := 
forall (t: TaskAbstractState) (e: OSEventAbstractState) (tasks: Glob_TaskAbstractState) (pevent: Z) (ptcb: Z) ,
  (event_task_remove_post ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") (tcb_y_of_prio ((curPrio (t)))) (tcb_bit_x_of_prio ((curPrio (t)))) (tcb_bit_y_of_prio ((curPrio (t)))) (encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t)))))) (encode_event_wait_grp ((waitList (e))) (tasks)) )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (t)))))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((encode_event_wait_grp ((waitList (e))) (tasks))) ((tcb_bit_x_of_prio ((curPrio (t))))) ((tcb_bit_y_of_prio ((curPrio (t)))))))
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((curPrio (t)))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((waitList (e))) (tasks) ((tcb_y_of_prio ((curPrio (t))))))) ((tcb_bit_x_of_prio ((curPrio (t)))))))
.

Module Type VC_Correct.


Axiom proof_of_OS_EventTaskRdy_safety_wit_1 : OS_EventTaskRdy_safety_wit_1.
Axiom proof_of_OS_EventTaskRdy_safety_wit_2 : OS_EventTaskRdy_safety_wit_2.
Axiom proof_of_OS_EventTaskRdy_entail_wit_1 : OS_EventTaskRdy_entail_wit_1.
Axiom proof_of_OS_EventTaskRdy_entail_wit_2 : OS_EventTaskRdy_entail_wit_2.
Axiom proof_of_OS_EventTaskRdy_entail_wit_3 : OS_EventTaskRdy_entail_wit_3.
Axiom proof_of_OS_EventTaskRdy_entail_wit_4_1 : OS_EventTaskRdy_entail_wit_4_1.
Axiom proof_of_OS_EventTaskRdy_entail_wit_4_2 : OS_EventTaskRdy_entail_wit_4_2.
Axiom proof_of_OS_EventTaskRdy_return_wit_1 : OS_EventTaskRdy_return_wit_1.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_1_pure : OS_EventTaskRdy_partial_solve_wit_1_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_1 : OS_EventTaskRdy_partial_solve_wit_1.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_2_pure : OS_EventTaskRdy_partial_solve_wit_2_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_2 : OS_EventTaskRdy_partial_solve_wit_2.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_3_pure : OS_EventTaskRdy_partial_solve_wit_3_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_3 : OS_EventTaskRdy_partial_solve_wit_3.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_4_pure : OS_EventTaskRdy_partial_solve_wit_4_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_4 : OS_EventTaskRdy_partial_solve_wit_4.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_5 : OS_EventTaskRdy_partial_solve_wit_5.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_6_pure : OS_EventTaskRdy_partial_solve_wit_6_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_6 : OS_EventTaskRdy_partial_solve_wit_6.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_7_pure : OS_EventTaskRdy_partial_solve_wit_7_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_7 : OS_EventTaskRdy_partial_solve_wit_7.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_8_pure : OS_EventTaskRdy_partial_solve_wit_8_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_8 : OS_EventTaskRdy_partial_solve_wit_8.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_9 : OS_EventTaskRdy_partial_solve_wit_9.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_10_pure : OS_EventTaskRdy_partial_solve_wit_10_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_10 : OS_EventTaskRdy_partial_solve_wit_10.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_11_pure : OS_EventTaskRdy_partial_solve_wit_11_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_11 : OS_EventTaskRdy_partial_solve_wit_11.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_12_pure : OS_EventTaskRdy_partial_solve_wit_12_pure.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_12 : OS_EventTaskRdy_partial_solve_wit_12.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_13 : OS_EventTaskRdy_partial_solve_wit_13.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_14 : OS_EventTaskRdy_partial_solve_wit_14.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_15 : OS_EventTaskRdy_partial_solve_wit_15.
Axiom proof_of_OS_EventTaskRdy_partial_solve_wit_16 : OS_EventTaskRdy_partial_solve_wit_16.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_1 : OS_EventTaskRdy_which_implies_wit_1.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_2 : OS_EventTaskRdy_which_implies_wit_2.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_3 : OS_EventTaskRdy_which_implies_wit_3.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_4 : OS_EventTaskRdy_which_implies_wit_4.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_5 : OS_EventTaskRdy_which_implies_wit_5.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_6 : OS_EventTaskRdy_which_implies_wit_6.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_7 : OS_EventTaskRdy_which_implies_wit_7.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_8 : OS_EventTaskRdy_which_implies_wit_8.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_9 : OS_EventTaskRdy_which_implies_wit_9.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_10 : OS_EventTaskRdy_which_implies_wit_10.
Axiom proof_of_OS_EventTaskRdy_which_implies_wit_11 : OS_EventTaskRdy_which_implies_wit_11.

End VC_Correct.
