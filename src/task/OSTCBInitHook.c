/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTCBInitHook (OS_TCB *ptcb)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
#if OS_APP_HOOKS_EN > 0u
    App_TCBInitHook(ptcb) /*@ where frame = frame */;
#else
    (void)ptcb;                                            /* Prevent compiler warning                 */
#endif
}
