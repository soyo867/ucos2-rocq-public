#include <ucos_ii.h>
#include "verification_stdlib.h"
/*@ Extern Coq (StableGlobVars :: *) */
/*@ Extern Coq (osMaxEvents : StableGlobVars -> Z) */
/*@ Extern Coq (g_OSEventTbl : StableGlobVars -> Z) */
/*@ Extern Coq (g_OSEventFreeList : StableGlobVars -> Z) */
/*@ Extern Coq (init_event_list_named_table_layout : StableGlobVars -> Prop)
 (full_features_kernel_profile : StableGlobVars -> Prop) */
/*@ Extern Coq (mem_clr_pre : Z -> Z -> Assertion) */
/*@ Extern Coq (mem_clr_post : Z -> Z -> Assertion) */
/*@ Extern Coq (init_event_list_named_pre : StableGlobVars -> Assertion) */
/*@ Extern Coq (init_event_list_named_post : StableGlobVars -> Z -> Assertion) */
/*@ Extern Coq (init_event_list_named_prefix : StableGlobVars -> Z -> Z -> Assertion) */
/*@ Extern Coq (init_event_list_named_loop_state : StableGlobVars -> Z -> Z -> Assertion) */
/*@ Extern Coq (init_event_list_named_loop_residual : StableGlobVars -> Z -> Z -> Assertion) */
/*@ Extern Coq (GlobalStrings : (String -> Z) -> Assertion) */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.event */
/*@ Import Coq Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.event.spec.init_event_list_names_spec */
/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */
static  void  OS_InitEventList (void)
/*@ With (sg : StableGlobVars) (LitMap : String -> Z) (frame : Assertion)
    Require
      osMaxEvents(sg) == 10 &&
      g_OSEventTbl(sg) == OSEventTbl &&
      g_OSEventFreeList(sg) == &OSEventFreeList &&
      sizeof(struct os_event) == 24 &&
      sizeof(struct os_event[10]) == 240 &&
      0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
      g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
      init_event_list_named_pre(sg) * GlobalStrings(LitMap) * frame
    Ensure
      osMaxEvents(sg) == 10 &&
      g_OSEventTbl(sg) == OSEventTbl &&
      g_OSEventFreeList(sg) == &OSEventFreeList &&
      sizeof(struct os_event) == 24 &&
      0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
      g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
      init_event_list_named_post(sg, LitMap("?")) * GlobalStrings(LitMap) * frame
*/
{
#if (OS_EVENT_EN) && (OS_MAX_EVENTS > 0u)
#if (OS_MAX_EVENTS > 1u)
    INT16U     ix;
    INT16U     ix_next;
    OS_EVENT  *pevent1;
    OS_EVENT  *pevent2;


    
/*@ osMaxEvents(sg) == 10 && full_features_kernel_profile(sg) &&
        g_OSEventTbl(sg) == OSEventTbl &&
        sizeof(struct os_event[10]) == 240 && init_event_list_named_pre(sg)
        which implies
        osMaxEvents(sg) == 10 && full_features_kernel_profile(sg) &&
        g_OSEventTbl(sg) == OSEventTbl &&
        sizeof(struct os_event[10]) == 240 &&
        mem_clr_pre(pointer_offset(OSEventTbl, 0, struct os_event),
                    sizeof(struct os_event[10])) *
        undef_data_at(g_OSEventFreeList(sg), OS_EVENT *)
    */
OS_MemClr((INT8U *)&OSEventTbl[0], sizeof(OSEventTbl)); /* Clear the event table                   */
    
/*@ Inv Assert
          osMaxEvents(sg) == 10 &&
          g_OSEventTbl(sg) == OSEventTbl &&
          g_OSEventFreeList(sg) == &OSEventFreeList &&
          sizeof(struct os_event) == 24 &&
          0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
          g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
          0 <= ix && ix <= 9 &&
          init_event_list_named_loop_state(sg, LitMap("?"), ix) *
          GlobalStrings(LitMap) * frame *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pevent1, OS_EVENT *) *
          undef_data_at(&pevent2, OS_EVENT *)
    */
for (ix = 0u; ix < (OS_MAX_EVENTS - 1u); ix++) {        /* Init. list of free EVENT control blocks */
        ix_next = ix + 1u;
        pevent1 = &OSEventTbl[ix];
        pevent2 = &OSEventTbl[ix_next];
        
/*@
              osMaxEvents(sg) == 10 &&
              g_OSEventTbl(sg) == OSEventTbl &&
              g_OSEventFreeList(sg) == &OSEventFreeList &&
              sizeof(struct os_event) == 24 &&
              0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
              g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
              0 <= ix && ix < 9 && ix_next == ix + 1 &&
              pevent1 == pointer_offset(OSEventTbl, ix, OS_EVENT) &&
              pevent2 == pointer_offset(OSEventTbl, ix_next, OS_EVENT) &&
              init_event_list_named_loop_state(sg, LitMap("?"), ix)
            which implies
              osMaxEvents(sg) == 10 &&
              g_OSEventTbl(sg) == OSEventTbl &&
              g_OSEventFreeList(sg) == &OSEventFreeList &&
              sizeof(struct os_event) == 24 &&
              0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
              g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
              0 <= ix && ix < 9 && ix_next == ix + 1 &&
              pevent1 == g_OSEventTbl(sg) + ix * 24 &&
              pevent2 == g_OSEventTbl(sg) + (ix + 1) * 24 &&
              data_at(&(pevent1->OSEventType), unsigned char, 0) *
              data_at(&(pevent1->OSEventPtr), void *, 0) *
              data_at(&(pevent1->OSEventName), unsigned char *, 0) *
              init_event_list_named_loop_residual(sg, LitMap("?"), ix)
        */
pevent1->OSEventType    = OS_EVENT_TYPE_UNUSED;
        pevent1->OSEventPtr     = pevent2;
#if OS_EVENT_NAME_EN > 0u
        pevent1->OSEventName    = (INT8U *)(void *)"?";     /* Unknown name                            */
#endif
    
/*@ Assert
              osMaxEvents(sg) == 10 &&
              g_OSEventTbl(sg) == OSEventTbl &&
              g_OSEventFreeList(sg) == &OSEventFreeList &&
              sizeof(struct os_event) == 24 &&
              0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
              g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
              0 <= ix && ix < 9 &&
              init_event_list_named_loop_state(sg, LitMap("?"), ix + 1) *
              GlobalStrings(LitMap) * frame *
              undef_data_at(&ix_next, unsigned short) *
              undef_data_at(&pevent1, OS_EVENT *) *
              undef_data_at(&pevent2, OS_EVENT *)
        */
}
    pevent1                         = &OSEventTbl[ix];
    
/*@
          osMaxEvents(sg) == 10 &&
          g_OSEventTbl(sg) == OSEventTbl &&
          g_OSEventFreeList(sg) == &OSEventFreeList &&
          sizeof(struct os_event) == 24 &&
          0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
          g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
          0 <= ix && ix <= 9 && ix >= 9 &&
          pevent1 == pointer_offset(OSEventTbl, ix, OS_EVENT) &&
          init_event_list_named_loop_state(sg, LitMap("?"), ix)
        which implies
          osMaxEvents(sg) == 10 &&
          g_OSEventTbl(sg) == OSEventTbl &&
          g_OSEventFreeList(sg) == &OSEventFreeList &&
          sizeof(struct os_event) == 24 &&
          0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
          g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
          ix == 9 && pevent1 == g_OSEventTbl(sg) + 216 &&
          data_at(&(pevent1->OSEventType), unsigned char, 0) *
          data_at(&(pevent1->OSEventPtr), void *, 0) *
          data_at(&(pevent1->OSEventName), unsigned char *, 0) *
          init_event_list_named_loop_residual(sg, LitMap("?"), 9)
    */
pevent1->OSEventType            = OS_EVENT_TYPE_UNUSED;
    pevent1->OSEventPtr             = (OS_EVENT *)0;
#if OS_EVENT_NAME_EN > 0u
    pevent1->OSEventName            = (INT8U *)(void *)"?"; /* Unknown name                            */
#endif
    
/*@ Assert
          osMaxEvents(sg) == 10 &&
          g_OSEventTbl(sg) == OSEventTbl &&
          g_OSEventFreeList(sg) == &OSEventFreeList &&
          sizeof(struct os_event) == 24 &&
          0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 240 <= 4294967295 &&
          g_OSEventTbl(sg) % 4 == 0 && init_event_list_named_table_layout(sg) && full_features_kernel_profile(sg) &&
          undef_data_at(&OSEventFreeList, OS_EVENT *) *
          init_event_list_named_prefix(sg, LitMap("?"), 10) *
          GlobalStrings(LitMap) * frame *
          undef_data_at(&ix, unsigned short) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pevent1, OS_EVENT *) *
          undef_data_at(&pevent2, OS_EVENT *)
    */
OSEventFreeList                 = &OSEventTbl[0];
#else
    OSEventFreeList                 = &OSEventTbl[0];       /* Only have ONE event control block       */
    OSEventFreeList->OSEventType    = OS_EVENT_TYPE_UNUSED;
    OSEventFreeList->OSEventPtr     = (OS_EVENT *)0;
#if OS_EVENT_NAME_EN > 0u
    OSEventFreeList->OSEventName    = (INT8U *)"?";         /* Unknown name                            */
#endif
#endif
#endif
}
