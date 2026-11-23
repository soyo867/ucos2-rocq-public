/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  App_TaskReturnHook (OS_TCB  *ptcb)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
    (void)ptcb;
}
