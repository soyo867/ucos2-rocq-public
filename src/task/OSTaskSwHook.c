/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTaskSwHook (void)
/*@ With (sg : StableGlobVars) (state : UCOS2_Verify_State) (frame : Assertion)
    Require frame
    Ensure task_sw_hook_step(sg, state, state) && frame
*/
{
#if OS_CFG_DBG_EN > 0u
    INT32U  ctx_id;
#endif

#if OS_APP_HOOKS_EN > 0u
    App_TaskSwHook() /*@ where sg = sg, state = state, frame = frame */;
#endif

    OS_TRACE_TASK_SWITCHED_IN(OSTCBHighRdy);

#if OS_CFG_DBG_EN > 0u
    ctx_id = ((INT32U)(OSPrioHighRdy    << 24u)             )
           | ((INT32U)(OSTCBHighRdy           ) & 0x00FFFFFF);
    OS_CPU_ARM_CtxID_Set(ctx_id);
#endif
}
