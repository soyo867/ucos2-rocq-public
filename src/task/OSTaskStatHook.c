/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTaskStatHook (void)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
#if OS_APP_HOOKS_EN > 0u
    App_TaskStatHook() /*@ where frame = frame */;
#endif
}
