/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  void  OSTmr_Free (OS_TMR *ptmr)
/*@ write_spec
    With (root used free : Z) (LitMap : String -> Z)
    Require tmr_free_write_pre(ptmr, root, used, free) * GlobalStrings(LitMap)
    Ensure tmr_free_write_post(ptmr, root, used, free, LitMap("?")) * GlobalStrings(LitMap)
*/
{
    
/*@ tmr_free_write_pre(ptmr, root, used, free)
        which implies
        undef_data_at(&(ptmr->OSTmrState), INT8U) *
        undef_data_at(&(ptmr->OSTmrOpt), INT8U) *
        undef_data_at(&(ptmr->OSTmrPeriod), INT32U) *
        undef_data_at(&(ptmr->OSTmrMatch), INT32U) *
        undef_data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK) *
        undef_data_at(&(ptmr->OSTmrCallbackArg), void *) *
        undef_data_at(&(ptmr->OSTmrName), INT8U *) *
        undef_data_at(&(ptmr->OSTmrPrev), void *) *
        undef_data_at(&(ptmr->OSTmrNext), void *) *
        data_at(&OSTmrFreeList, OS_TMR *, root) *
        data_at(&OSTmrUsed, INT16U, used) * data_at(&OSTmrFree, INT16U, free)
    */
ptmr->OSTmrState       = OS_TMR_STATE_UNUSED;      /* Clear timer object fields                                   */
    ptmr->OSTmrOpt         = OS_TMR_OPT_NONE;
    ptmr->OSTmrPeriod      = 0u;
    ptmr->OSTmrMatch       = 0u;
    ptmr->OSTmrCallback    = (OS_TMR_CALLBACK)0;
    ptmr->OSTmrCallbackArg = (void *)0;
#if OS_TMR_CFG_NAME_EN > 0u
    ptmr->OSTmrName        = (INT8U *)(void *)"?";
#endif

    ptmr->OSTmrPrev        = (OS_TCB *)0;              /* Chain timer to free list                                    */
    ptmr->OSTmrNext        = OSTmrFreeList;
    OSTmrFreeList          = ptmr;

    OSTmrUsed--;                                       /* Update timer object statistics                              */
    OSTmrFree++;
}
