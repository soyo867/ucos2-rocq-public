/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_TaskStkClr (OS_STK  *pbos,
                     INT32U   size,
                     INT16U   opt)
/*@ With (initial : list (option Z)) (R : Assertion)
    Require 0 <= size && size <= 4294967295 &&
            0 <= opt && opt <= 65535 &&
            task_stk_clr_pre(pbos, size, opt, initial) * R
    Ensure task_stk_clr_post(pbos, size, opt, initial) * R
*/
{
    if ((opt & OS_TASK_OPT_STK_CHK) != 0x0000u) {      /* See if stack checking has been enabled       */
        if ((opt & OS_TASK_OPT_STK_CLR) != 0x0000u) {  /* See if stack needs to be cleared             */
#if OS_STK_GROWTH == 1u
            /*@ Inv Assert
                  0 <= size && size <= size@pre && size@pre <= 4294967295 &&
                  opt == opt@pre && 0 <= opt && opt <= 65535 &&
                  (opt & OS_TASK_OPT_STK_CHK) != 0 &&
                  (opt & OS_TASK_OPT_STK_CLR) != 0 &&
                  pbos == pbos@pre + (size@pre - size) &&
                  task_stk_clr_loop(pbos@pre, size@pre, size, initial) * R
            */
            while (size > 0u) {                        /* Stack grows from HIGH to LOW memory          */
                /*@ 0 < size && size <= size@pre &&
                      pbos == pbos@pre + (size@pre - size) &&
                      task_stk_clr_loop(pbos@pre, size@pre, size, initial)
                    which implies
                      Zlength(initial) == size@pre &&
                      0 < pbos@pre && pbos@pre % 4 == 0 &&
                      pbos@pre + size@pre <= 4294967295 &&
                      0 < size && size <= size@pre &&
                      pbos == pbos@pre + (size@pre - size) &&
                      0 < pbos && pbos + 1 <= 4294967295 &&
                      undef_data_at(pbos, OS_STK) *
                      task_stk_clr_residual(pbos@pre, size@pre, size, initial)
                */
                size--;
                *pbos = (OS_STK)0;                     /* Clear from bottom of stack and up!           */
                pbos++;
            }
#else
            while (size > 0u) {                        /* Stack grows from LOW to HIGH memory          */
                size--;
                *pbos-- = (OS_STK)0;                   /* Clear from bottom of stack and down          */
            }
#endif
        }
    }
}
