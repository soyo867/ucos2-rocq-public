/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_MemCopy (INT8U  *pdest,
                  INT8U  *psrc,
                  INT16U  size)
/*@ With (bytes : list Z)
    Require
      0 <= size && size <= 65535 && Zlength(bytes) == size &&
      0 <= pdest && pdest + size <= 4294967295 &&
      0 <= psrc && psrc + size <= 4294967295 &&
      mem_copy_pre(pdest, psrc, size, bytes)
    Ensure mem_copy_post(pdest, psrc, size, bytes)
*/
{
    /*@ Inv Assert
          0 <= size && size <= size@pre && size@pre <= 65535 &&
          Zlength(bytes) == size@pre &&
          0 <= pdest@pre && pdest@pre + size@pre <= 4294967295 &&
          0 <= psrc@pre && psrc@pre + size@pre <= 4294967295 &&
          pdest == pdest@pre + (size@pre - size) &&
          psrc == psrc@pre + (size@pre - size) &&
          UCharArray::seg(pdest@pre, 0, size@pre - size,
                          sublist(0, size@pre - size, bytes)) *
          UCharArray::undef_seg(pdest@pre, size@pre - size, size@pre) *
          UCharArray::full(psrc@pre, size@pre, bytes)
    */
    while (size > 0u) {
        /*@
              0 < size && size <= size@pre && size@pre <= 65535 &&
              Zlength(bytes) == size@pre &&
              0 <= pdest@pre && pdest@pre + size@pre <= 4294967295 &&
              0 <= psrc@pre && psrc@pre + size@pre <= 4294967295 &&
              pdest == pdest@pre + (size@pre - size) &&
              psrc == psrc@pre + (size@pre - size) &&
              UCharArray::seg(pdest@pre, 0, size@pre - size,
                              sublist(0, size@pre - size, bytes)) *
              UCharArray::undef_seg(pdest@pre, size@pre - size, size@pre) *
              UCharArray::full(psrc@pre, size@pre, bytes)
            which implies
              0 < size && size <= size@pre && size@pre <= 65535 &&
              Zlength(bytes) == size@pre &&
              0 <= pdest@pre && pdest@pre + size@pre <= 4294967295 &&
              0 <= psrc@pre && psrc@pre + size@pre <= 4294967295 &&
              pdest == pdest@pre + (size@pre - size) &&
              psrc == psrc@pre + (size@pre - size) &&
              undef_data_at(pdest, unsigned char) *
              data_at(psrc, unsigned char, bytes[size@pre - size]) *
              UCharArray::missing_i(psrc@pre, size@pre - size, 0,
                                    size@pre, bytes) *
              UCharArray::seg(pdest@pre, 0, size@pre - size,
                              sublist(0, size@pre - size, bytes)) *
              UCharArray::undef_seg(pdest@pre, size@pre - size + 1, size@pre)
        */
        /* QCP's current frontend rejects upstream `*pdest++ = *psrc++;`.
         * This lowering reads the old source byte and writes the old
         * destination, then advances both non-volatile local cursors.  The
         * owned byte arrays and parameter cells are separate; there are no
         * volatile/MMIO accesses, calls, or observable concurrent steps.
         * Both final increments and the following size decrement remain. */
        *pdest = *psrc;
        pdest++;
        psrc++;
        size--;
    }
}
