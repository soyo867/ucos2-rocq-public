/*
 * Native source intake, not an accepted QCP/Rocq proof.
 * Base and configuration: config/queue-v2.93.01-first-round/profile.json.
 * Approved implementation delta: source_variants/mutex-current-priority/os_mutex.patch.
 * tests/mutex_current_priority/check-native-source.py compares the complete
 * preprocessed helper and native TCB with that exact patched source.
 *
 * This internal helper does not acquire a critical section or refresh the
 * high-ready cache. Its caller must supply the actual resource/entry contract.
 * The historical OSMutex_RdyAtPrio_full.c is a separate verification slice.
 */

typedef unsigned char  INT8U;
typedef unsigned short INT16U;
typedef unsigned int   INT32U;
typedef unsigned int   OS_STK;
typedef unsigned int   OS_CPU_SR;
typedef INT8U          OS_PRIO;
typedef INT16U         OS_FLAGS;

#define OS_LOWEST_PRIO          63u
#define OS_TASK_REG_TBL_SIZE     1u
#define OS_RDY_TBL_SIZE          8u
#define OS_TRACE_TASK_SUSPENDED(p_tcb)
#define OS_TRACE_TASK_READY(p_tcb)

struct os_event;
typedef struct os_event OS_EVENT;
struct os_flag_node;
typedef struct os_flag_node OS_FLAG_NODE;

typedef struct os_tcb {
    OS_STK        *OSTCBStkPtr;
    void          *OSTCBExtPtr;
    OS_STK        *OSTCBStkBottom;
    INT32U         OSTCBStkSize;
    INT16U         OSTCBOpt;
    INT16U         OSTCBId;
    struct os_tcb *OSTCBNext;
    struct os_tcb *OSTCBPrev;
    OS_EVENT      *OSTCBEventPtr;
    void          *OSTCBMsg;
    OS_FLAG_NODE  *OSTCBFlagNode;
    OS_FLAGS       OSTCBFlagsRdy;
    INT32U         OSTCBDly;
    INT8U          OSTCBStat;
    INT8U          OSTCBStatPend;
    INT8U          OSTCBPrio;
    INT8U          OSTCBX;
    INT8U          OSTCBY;
    OS_PRIO        OSTCBBitX;
    OS_PRIO        OSTCBBitY;
    INT8U          OSTCBDelReq;
    INT8U         *OSTCBTaskName;
    INT32U         OSTCBRegTbl[OS_TASK_REG_TBL_SIZE];
} OS_TCB;

extern OS_TCB *OSTCBCur;
extern OS_TCB *OSTCBPrioTbl[OS_LOWEST_PRIO + 1u];
extern INT8U OSPrioCur;
extern OS_PRIO OSRdyGrp;
extern OS_PRIO OSRdyTbl[OS_RDY_TBL_SIZE];

static void OSMutex_RdyAtPrio(OS_TCB *ptcb, INT8U prio)
{
    INT8U y;

    y = ptcb->OSTCBY;
    OSRdyTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;
    OS_TRACE_TASK_SUSPENDED(ptcb);
    if (OSRdyTbl[y] == 0u) {
        OSRdyGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
    }
    ptcb->OSTCBPrio = prio;
    if (ptcb == OSTCBCur) {
        OSPrioCur = prio;
    }
    ptcb->OSTCBY = (INT8U)((INT8U)(prio >> 3u) & 0x07u);
    ptcb->OSTCBX = (INT8U)(prio & 0x07u);
    ptcb->OSTCBBitY = (OS_PRIO)(1uL << ptcb->OSTCBY);
    ptcb->OSTCBBitX = (OS_PRIO)(1uL << ptcb->OSTCBX);
    OSRdyGrp |= ptcb->OSTCBBitY;
    OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
    OSTCBPrioTbl[prio] = ptcb;
    OS_TRACE_TASK_READY(ptcb);
}
