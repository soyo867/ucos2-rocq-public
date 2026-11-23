/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT16U  OSVersion (void)
/*@ With (s : UCOS2_Verify_State) (X : Z -> UCOS2_Verify_State -> Prop) (frame : Assertion)
    Require os_version_safe(s, X) && frame
    Ensure __return == OS_VERSION && os_version_safe_return(s, __return, X) && frame
*/
{
    return (OS_VERSION);
}
