/*
 * uC/OS-II V2.93.01, Source/os_core.c: OS_InitEventList.
 * Bound upstream checkout: /tmp/ucos2-official-audit-20260802/Source/
 * Standalone selected-profile slice; the complete conditional function body
 * and write order are retained. OS_EVENT_NAME_EN = 0, OS_MAX_EVENTS = 10,
 * OS_LOWEST_PRIO = 63, ILP32/little-endian. See
 * config/core-initializers-v2.93.01.md for the MemClr/layout call boundary.
 */

/*@ Extern Coq (StableGlobVars :: *) */
/*@ Extern Coq (osMaxEvents : StableGlobVars -> Z) */
/*@ Extern Coq (g_OSEventTbl : StableGlobVars -> Z) */
/*@ Extern Coq (g_OSEventFreeList : StableGlobVars -> Z) */
/*@ Extern Coq (event_table_layout_prop : StableGlobVars -> Prop) */
/*@ Extern Coq (init_event_list_profile : StableGlobVars -> Prop) */
/*@ Extern Coq (mem_clr_pre : Z -> Z -> Assertion) */
/*@ Extern Coq (mem_clr_post : Z -> Z -> Assertion) */
/*@ Extern Coq (init_event_list_pre : StableGlobVars -> Assertion) */
/*@ Extern Coq (init_event_list_post : StableGlobVars -> Assertion) */
/*@ Extern Coq (init_event_list_prefix : StableGlobVars -> Z -> Assertion) */
/*@ Extern Coq (init_event_list_loop_state : StableGlobVars -> Z -> Assertion) */
/*@ Extern Coq (init_event_list_loop_residual : StableGlobVars -> Z -> Assertion) */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.event */
/*@ Import Coq Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.event.spec.init_event_list_spec */
/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */

typedef unsigned char INT8U;
typedef unsigned short INT16U;
typedef unsigned char OS_PRIO;

#define OS_EVENT_EN 1u
#define OS_MAX_EVENTS 10u
#define OS_EVENT_NAME_EN 0u
#define OS_EVENT_TBL_SIZE 8u
#define OS_EVENT_TYPE_UNUSED 0u

typedef struct os_event {
    INT8U OSEventType;
    void *OSEventPtr;
    INT16U OSEventCnt;
    OS_PRIO OSEventGrp;
    OS_PRIO OSEventTbl[OS_EVENT_TBL_SIZE];
} OS_EVENT;

extern OS_EVENT OSEventTbl[OS_MAX_EVENTS];
extern OS_EVENT *OSEventFreeList;

/* Exact generic byte contract of the verified OS_MemClr implementation. */
void OS_MemClr(INT8U *pdest, INT16U size)
/*@ Require
      0 <= size && size <= 65535 &&
      0 <= pdest && pdest + size <= 4294967295 &&
      mem_clr_pre(pdest, size)
    Ensure mem_clr_post(pdest, size)
*/;

static void OS_InitEventList (void)
/*@ With (sg : StableGlobVars)
    Require
      osMaxEvents(sg) == 10 &&
      g_OSEventTbl(sg) == OSEventTbl &&
      g_OSEventFreeList(sg) == &OSEventFreeList &&
      sizeof(struct os_event) == 20 &&
      sizeof(struct os_event[10]) == 200 &&
      0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
      g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
      init_event_list_profile(sg) &&
      init_event_list_pre(sg)
    Ensure
      osMaxEvents(sg) == 10 &&
      g_OSEventTbl(sg) == OSEventTbl &&
      g_OSEventFreeList(sg) == &OSEventFreeList &&
      sizeof(struct os_event) == 20 &&
      0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
      g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
      init_event_list_profile(sg) &&
      init_event_list_post(sg)
*/
{
#if (OS_EVENT_EN) && (OS_MAX_EVENTS > 0u)
#if (OS_MAX_EVENTS > 1u)
    INT16U ix;
    INT16U ix_next;
    OS_EVENT *pevent1;
    OS_EVENT *pevent2;

    /*@ g_OSEventTbl(sg) == OSEventTbl &&
        sizeof(struct os_event[10]) == 200 && init_event_list_pre(sg)
        which implies
        g_OSEventTbl(sg) == OSEventTbl &&
        sizeof(struct os_event[10]) == 200 &&
        mem_clr_pre(pointer_offset(OSEventTbl, 0, struct os_event),
                    sizeof(struct os_event[10])) *
        undef_data_at(g_OSEventFreeList(sg), OS_EVENT *)
    */
    OS_MemClr((INT8U *)&OSEventTbl[0], sizeof(OSEventTbl));
    /*@ Inv Assert
          osMaxEvents(sg) == 10 &&
          g_OSEventTbl(sg) == OSEventTbl &&
          g_OSEventFreeList(sg) == &OSEventFreeList &&
          sizeof(struct os_event) == 20 &&
          0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
          g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
          init_event_list_profile(sg) &&
          0 <= ix && ix <= 9 &&
          init_event_list_loop_state(sg, ix) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pevent1, OS_EVENT *) *
          undef_data_at(&pevent2, OS_EVENT *)
    */
    for (ix = 0u; ix < (OS_MAX_EVENTS - 1u); ix++) {
        ix_next = ix + 1u;
        pevent1 = &OSEventTbl[ix];
        pevent2 = &OSEventTbl[ix_next];
        /*@
              osMaxEvents(sg) == 10 &&
              g_OSEventTbl(sg) == OSEventTbl &&
              g_OSEventFreeList(sg) == &OSEventFreeList &&
              sizeof(struct os_event) == 20 &&
              0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
              g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
              init_event_list_profile(sg) &&
              0 <= ix && ix < 9 && ix_next == ix + 1 &&
              pevent1 == pointer_offset(OSEventTbl, ix, OS_EVENT) &&
              pevent2 == pointer_offset(OSEventTbl, ix_next, OS_EVENT) &&
              init_event_list_loop_state(sg, ix)
            which implies
              osMaxEvents(sg) == 10 &&
              g_OSEventTbl(sg) == OSEventTbl &&
              g_OSEventFreeList(sg) == &OSEventFreeList &&
              sizeof(struct os_event) == 20 &&
              0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
              g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
              init_event_list_profile(sg) &&
              0 <= ix && ix < 9 && ix_next == ix + 1 &&
              pevent1 == g_OSEventTbl(sg) + ix * 20 &&
              pevent2 == g_OSEventTbl(sg) + (ix + 1) * 20 &&
              data_at(&(pevent1->OSEventType), unsigned char, 0) *
              data_at(&(pevent1->OSEventPtr), void *, 0) *
              init_event_list_loop_residual(sg, ix)
        */
        pevent1->OSEventType = OS_EVENT_TYPE_UNUSED;
        pevent1->OSEventPtr = pevent2;
#if OS_EVENT_NAME_EN > 0u
        pevent1->OSEventName = (INT8U *)(void *)"?";
#endif
        /*@ Assert
              osMaxEvents(sg) == 10 &&
              g_OSEventTbl(sg) == OSEventTbl &&
              g_OSEventFreeList(sg) == &OSEventFreeList &&
              sizeof(struct os_event) == 20 &&
              0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
              g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
              init_event_list_profile(sg) &&
              0 <= ix && ix < 9 &&
              init_event_list_loop_state(sg, ix + 1) *
              undef_data_at(&ix_next, unsigned short) *
              undef_data_at(&pevent1, OS_EVENT *) *
              undef_data_at(&pevent2, OS_EVENT *)
        */
    }
    pevent1 = &OSEventTbl[ix];
    /*@
          osMaxEvents(sg) == 10 &&
          g_OSEventTbl(sg) == OSEventTbl &&
          g_OSEventFreeList(sg) == &OSEventFreeList &&
          sizeof(struct os_event) == 20 &&
          0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
          g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
          init_event_list_profile(sg) &&
          0 <= ix && ix <= 9 && ix >= 9 &&
          pevent1 == pointer_offset(OSEventTbl, ix, OS_EVENT) &&
          init_event_list_loop_state(sg, ix)
        which implies
          osMaxEvents(sg) == 10 &&
          g_OSEventTbl(sg) == OSEventTbl &&
          g_OSEventFreeList(sg) == &OSEventFreeList &&
          sizeof(struct os_event) == 20 &&
          0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
          g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
          init_event_list_profile(sg) &&
          ix == 9 && pevent1 == g_OSEventTbl(sg) + 180 &&
          data_at(&(pevent1->OSEventType), unsigned char, 0) *
          data_at(&(pevent1->OSEventPtr), void *, 0) *
          init_event_list_loop_residual(sg, 9)
    */
    pevent1->OSEventType = OS_EVENT_TYPE_UNUSED;
    pevent1->OSEventPtr = (OS_EVENT *)0;
#if OS_EVENT_NAME_EN > 0u
    pevent1->OSEventName = (INT8U *)(void *)"?";
#endif
    /*@ Assert
          osMaxEvents(sg) == 10 &&
          g_OSEventTbl(sg) == OSEventTbl &&
          g_OSEventFreeList(sg) == &OSEventFreeList &&
          sizeof(struct os_event) == 20 &&
          0 <= g_OSEventTbl(sg) && g_OSEventTbl(sg) + 200 <= 4294967295 &&
          g_OSEventTbl(sg) % 4 == 0 && event_table_layout_prop(sg) &&
          init_event_list_profile(sg) &&
          undef_data_at(&OSEventFreeList, OS_EVENT *) *
          init_event_list_prefix(sg, 10) *
          undef_data_at(&ix, unsigned short) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pevent1, OS_EVENT *) *
          undef_data_at(&pevent2, OS_EVENT *)
    */
    OSEventFreeList = &OSEventTbl[0];
#else
    OSEventFreeList = &OSEventTbl[0];
    OSEventFreeList->OSEventType = OS_EVENT_TYPE_UNUSED;
    OSEventFreeList->OSEventPtr = (OS_EVENT *)0;
#if OS_EVENT_NAME_EN > 0u
    OSEventFreeList->OSEventName = (INT8U *)"?";
#endif
#endif
#endif
}
