/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and guards remain in the environment.
 */

void  App_TaskCreateHook (OS_TCB *ptcb)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
    (void)ptcb;
}
