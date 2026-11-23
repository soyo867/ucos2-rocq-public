/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSIntEnter (void)
/*@ With (platform : InterruptPlatformResources) (invocation : nat)
         (origin : TaskInvocationOrigin) (mask : Z)
         (sg : StableGlobVars) (before : UCOS2_Verify_State)
         (X : unit -> UCOS2_Verify_State -> Prop)
    Require os_int_enter_global_addresses(sg, &OSRunning, &OSIntNesting) &&
      os_int_enter_irq_masked(mask) && os_int_enter_safe(before, X) &&
      interrupt_platform_running(platform, invocation, origin, mask) * UCOS2_inv(sg, before)
    Ensure os_int_enter_irq_masked(mask) && os_int_enter_return_safe(before, X) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      UCOS2_inv(sg, os_int_enter_state(before))
*/
{
    /*@ os_int_enter_global_addresses(sg, &OSRunning, &OSIntNesting) &&
      UCOS2_inv(sg, before)
      which implies
      os_int_enter_global_addresses(sg, &OSRunning, &OSIntNesting) &&
      UCOS2_state_inv(sg, before) &&
      0 <= os_int_enter_nesting(before) && os_int_enter_nesting(before) <= 255 &&
      data_at(&OSRunning, unsigned char, os_int_enter_running(before)) *
      data_at(&OSIntNesting, unsigned char, os_int_enter_nesting(before)) *
      os_int_enter_frame(sg, before)
    */
    if (OSRunning == OS_TRUE) {
        if (OSIntNesting < 255u) {
            OSIntNesting++;                      /* Increment ISR nesting level                        */
        }
        OS_TRACE_ISR_ENTER();
    }
}
