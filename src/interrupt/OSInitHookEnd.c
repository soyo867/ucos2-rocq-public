/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSInitHookEnd (void)
/*@ With (P : Assertion)
    Require P
    Ensure P
*/
{
#if OS_CPU_INT_DIS_MEAS_EN > 0u
    OS_CPU_IntDisMeasInit();
#endif
}
