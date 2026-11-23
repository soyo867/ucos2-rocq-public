/* Actual selected kernel C, with the existing ucontext-style host port fixture.
 * This diagnostic is not an ARM/BSP, whole-OSInit, QCP or Rocq proof. */
#define _XOPEN_SOURCE 700
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ucontext.h>
#define OS_GLOBALS
#include <ucos_ii.h>

#if !defined(QCP_CORE_SOURCE) || !defined(QCP_TASK_SOURCE) || !defined(QCP_MUTEX_SOURCE)
#error Select the exact prepared source paths
#endif
#ifndef QCP_TASK_TRANSITION_REPAIRED
#error Select original or repaired Task explicitly
#endif
#include QCP_CORE_SOURCE
#include QCP_TASK_SOURCE
#include QCP_MUTEX_SOURCE

enum { HOST_LIMIT = 8, HOST_BYTES = 65536, KERNEL_WORDS = 256 };
struct host_task {
    ucontext_t context;
    void (*entry)(void *);
    void *argument;
    OS_STK *marker;
    OS_CPU_SR status;
    unsigned char stack[HOST_BYTES];
};
static struct host_task contexts[HOST_LIMIT];
static unsigned context_count, switches;
static OS_STK stacks[6][KERNEL_WORDS];
static OS_CPU_SR cpu_status = 0x13u;
static OS_EVENT *mutex;
static OS_TCB *owner;
static int idle_mode, tick_crash, injected;
static int suspend_started, suspend_returned, waiter_returned;
static INT8U suspend_argument = 20u;

_Static_assert(OS_LOWEST_PRIO == 63u && OS_PRIO_SELF == 255u, "priority profile");
_Static_assert(OS_EVENT_MULTI_EN == 0u && OS_EVENT_NAME_EN == 0u &&
               OS_TASK_PROFILE_EN == 0u, "selected optional features");
_Static_assert(OS_ARG_CHK_EN == 1u && OS_TASK_CHANGE_PRIO_EN == 1u &&
               OS_TASK_SUSPEND_EN == 1u, "enabled target APIs");

static struct host_task *context_for(OS_TCB *task)
{
    assert(task && task != OS_TCB_RESERVED);
    for (unsigned i = 0; i < context_count; ++i)
        if (contexts[i].marker == task->OSTCBStkPtr)
            return &contexts[i];
    abort();
}

static int ready(OS_TCB *task)
{
    return (OSRdyTbl[task->OSTCBY] & task->OSTCBBitX) != 0u;
}

static void host_entry(void)
{
    struct host_task *task = context_for(OSTCBCur);
    assert(cpu_status == 0x13u);
    task->entry(task->argument);
    abort();
}

OS_STK *OSTaskStkInit(void (*entry)(void *), void *argument,
                    OS_STK *top, INT16U options)
{
    (void)options;
    assert(context_count < HOST_LIMIT);
    struct host_task *task = &contexts[context_count++];
    assert(getcontext(&task->context) == 0);
    task->entry = entry;
    task->argument = argument;
    task->marker = top;
    task->status = 0x13u;
    task->context.uc_stack.ss_sp = task->stack;
    task->context.uc_stack.ss_size = sizeof(task->stack);
    task->context.uc_link = NULL;
    makecontext(&task->context, host_entry, 0);
    return top;
}

OS_CPU_SR OS_CPU_SR_Save(void)
{
    OS_CPU_SR old = cpu_status;
    cpu_status |= 0xc0u;
    return old;
}

static void change_idle_interrupt(void);

void OS_CPU_SR_Restore(OS_CPU_SR saved)
{
    assert((cpu_status & 0xc0u) == 0xc0u);
    cpu_status = saved;
    /* Interrupt the actual Idle loop after its first counter-store/Restore.
     * No application Idle-hook call is inserted or modified. */
    if (idle_mode && !injected && OSRunning && OSIdleCtr == 1u &&
        OSTCBCur && OSTCBCur->OSTCBPrio == OS_TASK_IDLE_PRIO &&
        (cpu_status & 0xc0u) == 0u) {
        injected = 1;
        change_idle_interrupt();
    }
}

void OSTCBInitHook(OS_TCB *task) { (void)task; }
void OSTaskCreateHook(OS_TCB *task) { (void)task; }
void OSTimeTickHook(void) { }
void App_TaskIdleHook(void);
void OSTaskIdleHook(void) { App_TaskIdleHook(); }

void OSCtxSw(void)
{
    OS_TCB *previous = OSTCBCur;
    struct host_task *from = context_for(previous);
    struct host_task *to = context_for(OSTCBHighRdy);
    assert(OSIntNesting == 0u && OSLockNesting == 0u);
    assert((cpu_status & 0xc0u) == 0xc0u && previous != OSTCBHighRdy);
    assert(ready(OSTCBHighRdy));
    from->status = cpu_status;
    OSTCBCur = OSTCBHighRdy;
    OSPrioCur = OSPrioHighRdy;
    cpu_status = to->status;
    ++switches;
    assert(swapcontext(&from->context, &to->context) == 0);
    assert(OSTCBCur == previous && OSPrioCur == previous->OSTCBPrio);
    assert(cpu_status == from->status);
}

void OSIntCtxSw(void) { OSCtxSw(); }

void OSStartHighRdy(void)
{
    OSRunning = OS_TRUE;
    struct host_task *first = context_for(OSTCBHighRdy);
    cpu_status = first->status;
    assert(setcontext(&first->context) == 0);
    abort();
}

static INT8U create_task(unsigned index, void (*body)(void *), INT8U priority)
{
    return OSTaskCreate(body, NULL, &stacks[index][KERNEL_WORDS - 1u], priority);
}

static void waiter(void *argument)
{
    (void)argument;
    INT8U error = 0xffu;
    assert(OSTCBCur->OSTCBPrio == 10u);
    OSMutexPend(mutex, 0u, &error);
    assert(error == OS_ERR_NONE && suspend_returned);
    assert(mutex->OSEventPtr == OSTCBCur);
    assert(OSMutexPost(mutex) == OS_ERR_NONE);
    waiter_returned = 1;
    assert(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
    abort();
}

static void resumer(void *argument)
{
    (void)argument;
    assert(OSTCBCur->OSTCBPrio == 30u);
    assert(suspend_started && !suspend_returned);
    assert(owner->OSTCBPrio == 5u && owner->OSTCBStat == OS_STAT_SUSPEND);
    assert(!ready(owner) && mutex->OSEventPtr == owner);
    assert(OSTCBPrioTbl[5u] == owner && OSTCBPrioTbl[20u] == owner);
    unsigned before = switches;
    /* Noncurrent alias suspension is idempotent and must not self-switch. */
    assert(OSTaskSuspend(20u) == OS_ERR_NONE && switches == before);
    assert(!ready(owner));
    assert(OSTaskResume(20u) == OS_ERR_NONE);
    abort();
}

static void owner_body(void *argument)
{
    (void)argument;
    INT8U error = 0xffu;
    owner = OSTCBCur;
    assert(owner->OSTCBPrio == 20u && ready(owner));
    assert(OSMutexAccept(mutex, &error) == OS_TRUE && error == OS_ERR_NONE);
    assert(OSTaskResume(10u) == OS_ERR_NONE);
    /* Real waiter Pend supplied the alias and actual priority boost. */
    assert(OSTCBCur == owner && owner->OSTCBPrio == 5u && OSPrioCur == 5u);
    assert(OSTCBPrioTbl[5u] == owner && OSTCBPrioTbl[20u] == owner);
    assert(mutex->OSEventPtr == owner && mutex->OSEventGrp != 0u);
    assert(owner->OSTCBEventPtr == NULL && owner->OSTCBDly == 0u && ready(owner));
    unsigned before = switches;
    suspend_started = 1;
    assert(OSTaskSuspend(suspend_argument) == OS_ERR_NONE);
    suspend_returned = 1;
    if (!QCP_TASK_TRANSITION_REPAIRED && suspend_argument == 20u) {
        assert(switches == before && OSTCBCur == owner);
        assert(owner->OSTCBStat == OS_STAT_SUSPEND && !ready(owner));
        assert(mutex->OSEventPtr == owner);
        puts("reproduced: real inherited owner Suspend(base=20) returned while itself suspended, without scheduling");
        puts("scope: API-created tasks; real Mutex Accept/Pend inheritance; ucontext platform boundary");
        exit(0);
    }
    assert(switches >= before + 2u && OSTCBCur == owner && ready(owner));
    assert(owner->OSTCBStat == OS_STAT_RDY && mutex->OSEventPtr == owner);
    assert(OSMutexPost(mutex) == OS_ERR_NONE && waiter_returned);
    assert(owner->OSTCBPrio == 20u && ready(owner));
    printf("passed: Suspend(%u) switched, Resume(base) restored same call, actual Post/Pend completed; %u switches\n",
           suspend_argument, switches);
    exit(0);
}

static void setup(void *argument)
{
    (void)argument;
    INT8U error = 0xffu;
    mutex = OSMutexCreate(5u, &error);
    assert(mutex && error == OS_ERR_NONE);
    assert(create_task(2u, owner_body, 20u) == OS_ERR_NONE);
    assert(create_task(3u, waiter, 10u) == OS_ERR_NONE);
    assert(create_task(4u, resumer, 30u) == OS_ERR_NONE);
    assert(OSTaskSuspend(10u) == OS_ERR_NONE);
    assert(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
    abort();
}

static void change_idle_interrupt(void)
{
    OS_TCB *idle = OSTCBCur;
    OS_TCB old = *idle;
    OS_PRIO rows[OS_RDY_TBL_SIZE], group = OSRdyGrp;
    memcpy(rows, OSRdyTbl, sizeof(rows));
    assert(OSRunning && idle->OSTCBPrio == 63u && idle->OSTCBNext == NULL);
    assert(OSTCBPrioTbl[5u] == NULL && ready(idle));
    cpu_status |= 0xc0u;
    OSIntEnter();
    assert(OSIntNesting == 1u);
    INT8U error = OSTaskChangePrio(OS_PRIO_SELF, 5u);
    assert(OSIntNesting == 1u && switches == 0u && cpu_status == (0x13u | 0xc0u));
    if (!QCP_TASK_TRANSITION_REPAIRED) {
        assert(error == OS_ERR_NONE && idle->OSTCBPrio == 5u);
        assert(OSTCBPrioTbl[63u] == NULL && OSTCBPrioTbl[5u] == idle);
        assert(ready(idle) && idle->OSTCBNext == NULL);
        puts("reproduced: ISR ChangePrio(SELF,5) removed actual Idle priority-63 traversal sentinel");
        fflush(stdout);
        if (tick_crash) {
            OSTimeTick(); /* Expected UBSan NULL-member diagnostic in real C. */
            abort();
        }
        exit(0);
    }
    assert(error == OS_ERR_PRIO_INVALID && memcmp(&old, idle, sizeof(old)) == 0);
    assert(OSTCBPrioTbl[5u] == NULL && OSTCBPrioTbl[63u] == idle);
    assert(memcmp(rows, OSRdyTbl, sizeof(rows)) == 0 && group == OSRdyGrp);
    OSTimeTick();
    OSIntExit();
    assert(OSIntNesting == 0u && switches == 0u && OSTCBCur == idle);
    puts("passed: actual Idle loop interrupted; ChangePrio SELF rejected with no writes; actual Tick/IntExit returned");
    exit(0);
}

int main(int argc, char **argv)
{
    assert(argc <= 2);
    if (argc == 2) {
        if (!strcmp(argv[1], "--idle")) idle_mode = 1;
        else if (!strcmp(argv[1], "--idle-tick")) idle_mode = tick_crash = 1;
        else if (!strcmp(argv[1], "--self")) suspend_argument = OS_PRIO_SELF;
        else if (!strcmp(argv[1], "--effective")) suspend_argument = 5u;
        else abort();
    }
    /* Existing diagnostic startup contract: real static initialization
     * helpers, real task creation and OSStart; not complete OSInit. */
    OS_InitMisc();
    OS_InitRdyList();
    OS_InitTCBList();
    OS_InitEventList();
    assert(create_task(0u, OS_TaskIdle, OS_TASK_IDLE_PRIO) == OS_ERR_NONE);
    if (!idle_mode) assert(create_task(1u, setup, 2u) == OS_ERR_NONE);
    OSStart();
    abort();
}
