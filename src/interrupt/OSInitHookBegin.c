/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSInitHookBegin (void)
/*@ With (base : Z) (initial : list (option Z)) (R : Assertion)
    Require base == &OS_CPU_ExceptStk &&
            os_init_hook_begin_pre(base, &OS_CPU_ExceptStkBase,
                                   &OS_CPU_ARM_DRegCnt, &OSTmrCtr, initial, R)
    Ensure base == &OS_CPU_ExceptStk &&
           os_init_hook_begin_post(base, &OS_CPU_ExceptStkBase,
                                  &OS_CPU_ARM_DRegCnt, &OSTmrCtr, R)
*/
{
    INT32U   size;
    OS_STK  *pstk;

    /*@ os_init_hook_begin_pre(base, &OS_CPU_ExceptStkBase,
                              &OS_CPU_ARM_DRegCnt, &OSTmrCtr, initial, R)
        which implies
        0 < base && base % 4 == 0 && base + 4096 <= 4294967295 &&
        Zlength(initial) == 1024 &&
        task_stack_clear_rep(base, initial, 0) *
        undef_data_at(&OS_CPU_ExceptStkBase, OS_STK *) *
        undef_data_at(&OS_CPU_ARM_DRegCnt, INT32U) *
        undef_data_at(&OSTmrCtr, INT16U) * R
    */
                                                                /* Clear exception stack for stack checking.            */
    pstk = &OS_CPU_ExceptStk[0];
    size = OS_CPU_EXCEPT_STK_SIZE;
    /*@ Inv Assert
        base == &OS_CPU_ExceptStk &&
        0 < base && base % 4 == 0 && base + 4096 <= 4294967295 &&
        Zlength(initial) == 1024 && 0 <= size && size <= 1024 &&
        pstk == base + 4 * (1024 - size) &&
        task_stack_clear_rep(base, initial, 1024 - size) *
        undef_data_at(&OS_CPU_ExceptStkBase, OS_STK *) *
        undef_data_at(&OS_CPU_ARM_DRegCnt, INT32U) *
        undef_data_at(&OSTmrCtr, INT16U) * R
    */
    while (size > 0u) {
        /*@ task_stack_clear_rep(base, initial, 1024 - size) &&
            Zlength(initial) == 1024 && 0 < size && size <= 1024 &&
            pstk == base + 4 * (1024 - size)
            which implies
            Zlength(initial) == 1024 && 0 < size && size <= 1024 &&
            pstk == base + 4 * (1024 - size) &&
            undef_data_at(pstk, OS_STK) *
            os_init_hook_begin_stack_cell_rest(base, initial, 1024 - size)
        */
        size--;
       *pstk = (OS_STK)0;
        pstk++;
    }
                                                                /* Align the ISR stack to 8-bytes                       */
    OS_CPU_ExceptStkBase = (OS_STK *)&OS_CPU_ExceptStk[OS_CPU_EXCEPT_STK_SIZE];
    OS_CPU_ExceptStkBase = (OS_STK *)((OS_STK)(OS_CPU_ExceptStkBase) & 0xFFFFFFF8);

    OS_CPU_ARM_DRegCnt = OS_CPU_ARM_DRegCntGet() /*@ where P=R */;

#if OS_TMR_EN > 0u
    OSTmrCtr = 0u;
#endif
}
