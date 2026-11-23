/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  OS_TMR  *OSTmr_Alloc (void)
/*@ With (head : Z) (next : Z) (prev : Z) (used : Z) (free : Z)
         (frame : Assertion)
    Require
      tmr_alloc_low_pre(head, next, prev, used, free) * frame
    Ensure
      tmr_alloc_low_post(head, next, prev, used, free, __return) * frame
*/
{
    /*@ tmr_alloc_low_pre(head, next, prev, used, free)
        which implies
      data_at(&OSTmrFreeList, OS_TMR *, head) *
      data_at(&OSTmrUsed, INT16U, used) *
      data_at(&OSTmrFree, INT16U, free) *
      ((head == 0 && emp) ||
       (head != 0 &&
        data_at(&(((OS_TMR *)head)->OSTmrNext), void *, next) *
        data_at(&(((OS_TMR *)head)->OSTmrPrev), void *, prev)))
    */
    OS_TMR *ptmr;


    if (OSTmrFreeList == (OS_TMR *)0) {
        return ((OS_TMR *)0);
    }
    ptmr            = (OS_TMR *)OSTmrFreeList;
    OSTmrFreeList   = (OS_TMR *)ptmr->OSTmrNext;
    ptmr->OSTmrNext = (OS_TCB *)0;
    ptmr->OSTmrPrev = (OS_TCB *)0;
    OSTmrUsed++;
    OSTmrFree--;
    return (ptmr);
}
