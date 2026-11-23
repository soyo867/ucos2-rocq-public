/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OS_StrLen (INT8U *psrc)
/*@ exact_frame_spec
    With (entry base : Z) (names : NameResourceState) (chars : list Z) (frame : Assertion)
    Require
      psrc == entry && ((psrc == 0 && frame) ||
      (psrc != 0 && psrc == base &&
       readable_name(names, psrc, chars) &&
       os_strlen_bytes(psrc, chars) * frame))
    Ensure
      (entry == 0 && __return == 0 && frame) ||
      (entry != 0 && entry == base &&
       os_strlen_result(chars, __return) &&
       os_strlen_bytes(entry, chars) * frame)
*/
{
    INT8U  len;


#if OS_ARG_CHK_EN > 0u
    if (psrc == (INT8U *)0) {
        return (0u);
    }
#endif

    len = 0u;
    
/*@ Inv Assert
          base != 0 &&
          psrc == base + (psrc - base) &&
          readable_name(names, base, chars) &&
          0 <= psrc - base &&
          psrc - base <= Zlength(chars) &&
          len == kernel_u8(psrc - base) &&
          entry == base &&
          data_at(psrc, unsigned char, Znth(psrc - base, os_strlen_source(chars), 0)) *
          os_strlen_loop_residual(base, chars, psrc - base, len, frame)
    */
while (*psrc != OS_ASCII_NUL) {
        psrc++;
        len++;
    }
    return (len);
}
