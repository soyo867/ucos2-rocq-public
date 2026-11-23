/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  App_TaskStatHook (void)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
}
