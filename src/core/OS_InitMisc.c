/*
 * uC/OS-II V2.93.01, Source/os_core.c:1389: OS_InitMisc.
 * Bound source: /tmp/ucos2-official-audit-20260802/Source/
 * Selected queue-v2.93.01-first-round profile: time/statistics enabled,
 * one task register, IEC61508 safety flag disabled. Retains volatile RAM
 * declarations and the original store order. No CPU/BSP effect is assumed.
 */

#include "verification_stdlib.h"

/*@ Extern Coq (StableGlobVars :: *) */
/*@ Extern Coq (g_OSTime : StableGlobVars -> Z)
               (g_OSIntNesting : StableGlobVars -> Z)
               (g_OSLockNesting : StableGlobVars -> Z)
               (g_OSTaskCtr : StableGlobVars -> Z)
               (g_OSRunning : StableGlobVars -> Z)
               (g_OSCtxSwCtr : StableGlobVars -> Z)
               (g_OSIdleCtr : StableGlobVars -> Z)
               (g_OSIdleCtrRun : StableGlobVars -> Z)
               (g_OSIdleCtrMax : StableGlobVars -> Z)
               (g_OSStatRdy : StableGlobVars -> Z)
               (g_OSTaskRegNextAvailID : StableGlobVars -> Z)
               (init_misc_zero : StableGlobVars -> Assertion) */
/*@ Import Coq Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec */
/*@ Import Coq Import UCOS2_C_Rules */

typedef unsigned char INT8U;
typedef unsigned int INT32U;
typedef unsigned char BOOLEAN;

#define OS_FALSE 0u
#define OS_TIME_GET_SET_EN 1u
#define OS_TASK_STAT_EN 1u
#define OS_TASK_REG_TBL_SIZE 1u

extern volatile INT32U OSTime;
extern INT8U OSIntNesting;
extern INT8U OSLockNesting;
extern INT8U OSTaskCtr;
extern BOOLEAN OSRunning;
extern INT32U OSCtxSwCtr;
extern volatile INT32U OSIdleCtr;
extern INT32U OSIdleCtrRun;
extern INT32U OSIdleCtrMax;
extern BOOLEAN OSStatRdy;
extern INT8U OSTaskRegNextAvailID;

#ifdef OS_SAFETY_CRITICAL_IEC61508
extern BOOLEAN OSSafetyCriticalStartFlag;
#endif

static void OS_InitMisc (void)
/*@ With (sg : StableGlobVars) (R : Assertion)
    Require &OSTime == g_OSTime(sg) &&
            &OSIntNesting == g_OSIntNesting(sg) &&
            &OSLockNesting == g_OSLockNesting(sg) &&
            &OSTaskCtr == g_OSTaskCtr(sg) &&
            &OSRunning == g_OSRunning(sg) &&
            &OSCtxSwCtr == g_OSCtxSwCtr(sg) &&
            &OSIdleCtr == g_OSIdleCtr(sg) &&
            &OSIdleCtrRun == g_OSIdleCtrRun(sg) &&
            &OSIdleCtrMax == g_OSIdleCtrMax(sg) &&
            &OSStatRdy == g_OSStatRdy(sg) &&
            &OSTaskRegNextAvailID == g_OSTaskRegNextAvailID(sg) &&
            undef_data_at(&OSTime, INT32U) *
            undef_data_at(&OSIntNesting, INT8U) *
            undef_data_at(&OSLockNesting, INT8U) *
            undef_data_at(&OSTaskCtr, INT8U) *
            undef_data_at(&OSRunning, BOOLEAN) *
            undef_data_at(&OSCtxSwCtr, INT32U) *
            undef_data_at(&OSIdleCtr, INT32U) *
            undef_data_at(&OSIdleCtrRun, INT32U) *
            undef_data_at(&OSIdleCtrMax, INT32U) *
            undef_data_at(&OSStatRdy, BOOLEAN) *
            undef_data_at(&OSTaskRegNextAvailID, INT8U) * R
    Ensure init_misc_zero(sg) * R
*/
{
#if OS_TIME_GET_SET_EN > 0u
    OSTime = 0uL;
#endif
    OSIntNesting = 0u;
    OSLockNesting = 0u;
    OSTaskCtr = 0u;
    OSRunning = OS_FALSE;
    OSCtxSwCtr = 0u;
    OSIdleCtr = 0uL;
#if OS_TASK_STAT_EN > 0u
    OSIdleCtrRun = 0uL;
    OSIdleCtrMax = 0uL;
    OSStatRdy = OS_FALSE;
#endif
#ifdef OS_SAFETY_CRITICAL_IEC61508
    OSSafetyCriticalStartFlag = OS_FALSE;
#endif
#if OS_TASK_REG_TBL_SIZE > 0u
    OSTaskRegNextAvailID = 0u;
#endif
}
