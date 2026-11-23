/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_MemClr (INT8U  *pdest,
                 INT16U  size)
/*@ Require
      0 <= size && size <= 65535 &&
      0 <= pdest && pdest + size <= 4294967295 &&
      mem_clr_pre(pdest, size)
    Ensure mem_clr_post(pdest, size)
*/
{
    /*@ Inv Assert
          0 <= size && size <= size@pre && size@pre <= 65535 &&
          0 <= pdest@pre && pdest@pre + size@pre <= 4294967295 &&
          pdest == pdest@pre + (size@pre - size) &&
          mem_clr_loop_state(pdest@pre, size@pre, size)
    */
    while (size > 0u) {
        /*@ 0 < size && size <= size@pre && size@pre <= 65535 &&
              0 <= pdest@pre && pdest@pre + size@pre <= 4294967295 &&
              pdest == pdest@pre + (size@pre - size) &&
              mem_clr_loop_state(pdest@pre, size@pre, size)
            which implies
              0 < size && size <= size@pre && size@pre <= 65535 &&
              0 <= pdest@pre && pdest@pre + size@pre <= 4294967295 &&
              pdest == pdest@pre + (size@pre - size) &&
              undef_data_at(pdest, unsigned char) *
              mem_clr_loop_residual(pdest@pre, size@pre, size)
        */
        /* QCP frontend adaptation: preserve the source postfix-store order. */
        *pdest = (INT8U)0;
        pdest++;
        size--;
    }
}
