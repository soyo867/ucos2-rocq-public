/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  void  OSTmr_Link (OS_TMR  *ptmr,
                          INT8U    type)
/*@ raw_spec
    With (p base clock kind time delay period first entries : Z) (R : Assertion)
    Require ptmr == p && type == kind && OSTmrWheelTbl == base &&
            &OSTmrTime == clock &&
            tmr_link_raw_pre(p, base, clock, kind, time, delay, period, first, entries, R)
    Ensure tmr_link_raw_post(p, base, clock, kind, time, delay, period, first, entries, R)
*/
{
    OS_TMR       *ptmr1;
    OS_TMR_WHEEL *pspoke;
    INT16U        spoke;


    
/*@ ptmr == p && type == kind && &OSTmrTime == clock &&
        tmr_link_raw_pre(p, base, clock, kind, time, delay, period, first, entries, R)
        which implies
        ptmr == p && type == kind && &OSTmrTime == clock && tmr_link_wheel_size &&
        0 < p && p + 40 <= 4294967296 &&
        0 < base && base + 56 <= 4294967296 &&
        0 <= kind && kind < 256 && 0 <= time && time < 4294967296 &&
        0 <= delay && delay < 4294967296 &&
        0 <= period && period < 4294967296 &&
        0 <= entries && entries < 65536 && tmr_link_neighbor_bounds(first) &&
        undef_data_at(&(ptmr->OSTmrState), unsigned char) *
        undef_data_at(&(ptmr->OSTmrMatch), unsigned int) *
        data_at(&(ptmr->OSTmrDly), unsigned int, delay) *
        data_at(&(ptmr->OSTmrPeriod), unsigned int, period) *
        undef_data_at(&(ptmr->OSTmrNext), void *) *
        undef_data_at(&(ptmr->OSTmrPrev), void *) *
        data_at(&OSTmrTime, unsigned int, time) *
        data_at(&(((OS_TMR_WHEEL *)(base + 8 * (tmr_link_match(kind, delay, period, time) % 7)))->OSTmrFirst), OS_TMR *, first) *
        data_at(&(((OS_TMR_WHEEL *)(base + 8 * (tmr_link_match(kind, delay, period, time) % 7)))->OSTmrEntries), unsigned short, entries) *
        tmr_link_neighbor_pre(first) * R
    */
ptmr->OSTmrState = OS_TMR_STATE_RUNNING;
    if (type == OS_TMR_LINK_PERIODIC) {                            /* Determine when timer will expire                */
        ptmr->OSTmrMatch = ptmr->OSTmrPeriod + OSTmrTime;
    } else {
        if (ptmr->OSTmrDly == 0u) {
            ptmr->OSTmrMatch = ptmr->OSTmrPeriod + OSTmrTime;
        } else {
            ptmr->OSTmrMatch = ptmr->OSTmrDly    + OSTmrTime;
        }
    }
    
/*@ ptmr->OSTmrMatch == tmr_link_match(kind, delay, period, time) by local */
spoke  = (INT16U)(ptmr->OSTmrMatch % OS_TMR_CFG_WHEEL_SIZE);
    
/*@ spoke == tmr_link_match(kind, delay, period, time) % 7 by local */
pspoke = &OSTmrWheelTbl[spoke];

    
/*@ pspoke == base + 8 * (tmr_link_match(kind, delay, period, time) % 7) by local */
if (pspoke->OSTmrFirst == (OS_TMR *)0) {                       /* Link into timer wheel                           */
        pspoke->OSTmrFirst   = ptmr;
        ptmr->OSTmrNext      = (OS_TMR *)0;
        pspoke->OSTmrEntries = 1u;
    } else {
        
/*@ first != 0 && tmr_link_neighbor_pre(first)
            which implies
            undef_data_at(&(((OS_TMR *)first)->OSTmrPrev), void *)
        */
ptmr1                = pspoke->OSTmrFirst;                 /* Point to first timer in the spoke               */
        pspoke->OSTmrFirst   = ptmr;
        ptmr->OSTmrNext      = (void *)ptmr1;
        ptmr1->OSTmrPrev     = (void *)ptmr;
        pspoke->OSTmrEntries++;
    }
    ptmr->OSTmrPrev = (void *)0;                                   /* Timer always inserted as first node in list     */
}
