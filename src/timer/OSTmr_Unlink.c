/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  void  OSTmr_Unlink (OS_TMR *ptmr)
/*@ raw_spec
    With (p base match_time next prev first entries : Z) (R : Assertion)
    Require ptmr == p && OSTmrWheelTbl == base &&
            tmr_unlink_raw_pre(p, base, match_time,
                              next, prev, first, entries, R)
    Ensure tmr_unlink_raw_post(p, base, match_time,
                              next, prev, first, entries, R)
*/
{
    OS_TMR        *ptmr1;
    OS_TMR        *ptmr2;
    OS_TMR_WHEEL  *pspoke;
    INT16U         spoke;


    
/*@ ptmr == p && tmr_unlink_raw_pre(p, base, match_time,
                           next, prev, first, entries, R)
        which implies
        ptmr == p && tmr_unlink_wheel_size && 0 < p && p + 40 <= 4294967296 &&
        0 < base && base + 56 <= 4294967296 &&
        0 <= match_time && match_time < 4294967296 &&
        0 <= entries && entries < 65536 &&
        tmr_unlink_neighbor_bounds(p, next, prev, first) &&
        data_at(&(ptmr->OSTmrMatch), unsigned int, match_time) *
        data_at(&(ptmr->OSTmrNext), void *, next) *
        data_at(&(ptmr->OSTmrPrev), void *, prev) *
        undef_data_at(&(ptmr->OSTmrState), unsigned char) *
        data_at(&(((OS_TMR_WHEEL *)(base + 8 * (match_time % 7)))->OSTmrFirst), OS_TMR *, first) *
        data_at(&(((OS_TMR_WHEEL *)(base + 8 * (match_time % 7)))->OSTmrEntries), unsigned short, entries) *
        tmr_unlink_neighbor_pre(p, next, prev, first) * R
    */
spoke  = (INT16U)(ptmr->OSTmrMatch % OS_TMR_CFG_WHEEL_SIZE);
    
/*@ spoke == match_time % 7 by local */
pspoke = &OSTmrWheelTbl[spoke];

    
/*@ pspoke == base + 8 * (match_time % 7) by local */
if (pspoke->OSTmrFirst == ptmr) {                       /* See if timer to remove is at the beginning of list     */
        
/*@ first == p && tmr_unlink_neighbor_pre(p, next, prev, first)
            which implies
            (next == 0 && emp) ||
            (next != 0 && data_at(&(((OS_TMR *)next)->OSTmrPrev), void *, p))
        */
ptmr1              = (OS_TMR *)ptmr->OSTmrNext;
        pspoke->OSTmrFirst = (OS_TMR *)ptmr1;
        if (ptmr1 != (OS_TMR *)0) {
            ptmr1->OSTmrPrev = (void *)0;
        }
    } else {
        
/*@ first != p && tmr_unlink_neighbor_pre(p, next, prev, first)
            which implies
            data_at(&(((OS_TMR *)prev)->OSTmrNext), void *, p) *
            ((next == 0 && emp) ||
             (next != 0 && data_at(&(((OS_TMR *)next)->OSTmrPrev), void *, p)))
        */
ptmr1            = (OS_TMR *)ptmr->OSTmrPrev;       /* Remove timer from somewhere in the list                */
        ptmr2            = (OS_TMR *)ptmr->OSTmrNext;
        ptmr1->OSTmrNext = ptmr2;
        if (ptmr2 != (OS_TMR *)0) {
            ptmr2->OSTmrPrev = (void *)ptmr1;
        }
    }
    ptmr->OSTmrState = OS_TMR_STATE_STOPPED;
    ptmr->OSTmrNext  = (void *)0;
    ptmr->OSTmrPrev  = (void *)0;
    pspoke->OSTmrEntries--;
}
