/*
 * Executable-source skeleton for OSQFlush, uC/OS-II V2.93.01.
 * Upstream: https://github.com/weston-embedded/uC-OS2.git
 * Pinned commit: bfc6120f20cb27a927a9fc5dd667f9e455495777
 * Source: Source/os_q.c, OSQFlush (lines 372-396).
 * Declarations/constants: Source/ucos_ii.h.
 * Profile: uC-OS2_verify/config/queue-v2.93.01-first-round/profile.json.
 * OS_ARG_CHK_EN=1 and OS_Q_FLUSH_EN=1; OS_CRITICAL_METHOD=3 is
 * expanded to the selected save/restore calls. Executable order is unchanged.
 * Flushing discards logical message references; it does not clear the buffer
 * or free the objects referenced by messages.
 */

typedef unsigned char  INT8U;
typedef unsigned short INT16U;
typedef unsigned int   OS_CPU_SR;
typedef unsigned char  OS_PRIO;

#define OS_EVENT_TBL_SIZE 8u
#define OS_EVENT_TYPE_Q   2u
#define OS_ERR_NONE        0u
#define OS_ERR_EVENT_TYPE  1u
#define OS_ERR_PEVENT_NULL 4u

typedef struct os_event {
    INT8U    OSEventType;
    void    *OSEventPtr;
    INT16U   OSEventCnt;
    OS_PRIO  OSEventGrp;
    OS_PRIO  OSEventTbl[OS_EVENT_TBL_SIZE];
} OS_EVENT;

typedef struct os_q {
    struct os_q   *OSQPtr;
    void         **OSQStart;
    void         **OSQEnd;
    void         **OSQIn;
    void         **OSQOut;
    INT16U         OSQSize;
    INT16U         OSQEntries;
} OS_Q;

OS_CPU_SR OS_CPU_SR_Save(void);
void OS_CPU_SR_Restore(OS_CPU_SR cpu_sr);

INT8U OSQFlush(OS_EVENT *pevent)
{
    OS_Q *pq;
    OS_CPU_SR cpu_sr = 0u;

    if (pevent == (OS_EVENT *)0) {
        return (OS_ERR_PEVENT_NULL);
    }
    if (pevent->OSEventType != OS_EVENT_TYPE_Q) {
        return (OS_ERR_EVENT_TYPE);
    }
    cpu_sr = OS_CPU_SR_Save();
    pq = (OS_Q *)pevent->OSEventPtr;
    pq->OSQIn = pq->OSQStart;
    pq->OSQOut = pq->OSQStart;
    pq->OSQEntries = 0u;
    OS_CPU_SR_Restore(cpu_sr);
    return (OS_ERR_NONE);
}
