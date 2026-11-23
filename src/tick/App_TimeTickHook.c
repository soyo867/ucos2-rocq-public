/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  App_TimeTickHook (void)
/*@ With (sg: StableGlobVars) (state: UCOS2_Verify_State) (frame: Assertion)
    Require frame
    Ensure app_time_tick_hook_step(sg, state, state) && frame
*/
{

}
