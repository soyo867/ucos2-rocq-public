/*
 * Selected application creation hooks for the native Task verification profile.
 * Function definitions extracted without executable changes from uC/OS-II
 * V2.93.01 Cfg/Template/app_hooks.c (see hook-source-binding.json).
 * The upstream file labels this as EXAMPLE CODE and permits reuse in whole
 * or in part. The opaque declaration below replaces its os.h include: neither
 * selected function reads the TCB, so no substitute structure layout is used.
 */
typedef struct os_tcb OS_TCB;

void App_TaskCreateHook(OS_TCB *ptcb)
{
    (void)ptcb;
}

void App_TCBInitHook(OS_TCB *ptcb)
{
    (void)ptcb;
}
