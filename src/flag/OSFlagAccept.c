/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_FLAGS  OSFlagAccept (OS_FLAG_GRP  *pgrp,
                        OS_FLAGS      flags,
                        INT8U         wait_type,
                        INT8U        *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (irq_mask: Z) (before: UCOS2_Verify_State) (view: FlagAcceptView)
    (observed: FlagGroupImage) (pe error_addr: addr) (requested wait_request: Z)
    (caller_frame: Assertion) (X: Z -> Z -> UCOS2_Verify_State -> Prop)
    Require pgrp == pe && perr == error_addr && flags == requested && wait_type == wait_request &&
      flag_accept_profile(sg) &&
      flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed), requested, wait_request, before, X) &&
      undef_data_at(perr, unsigned char) * caller_frame *
      flag_accept_before_resource(platform, critical, sg, invocation, origin, irq_mask, view, pe, before, observed)
    Ensure flag_accept_api_post(platform, critical, sg, invocation, origin, irq_mask,
      view, pe, error_addr, before, observed, requested, wait_request, __return, X) * caller_frame
*/
{
    OS_FLAGS      flags_rdy;
    INT8U         result;
    BOOLEAN       consume;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR     cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_FLAGS)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pgrp == (OS_FLAG_GRP *)0) {                        /* Validate 'pgrp'                          */
        *perr = OS_ERR_FLAG_INVALID_PGRP;
        return ((OS_FLAGS)0);
    }
#endif
    /*@ flag_accept_profile(sg) && pe != 0 &&
        flag_accept_before_resource(platform, critical, sg, invocation, origin, irq_mask, view, pe, before, observed)
        which implies flag_accept_profile(sg) && pe != 0 &&
        data_at(&((OS_FLAG_GRP *)pe)->OSFlagType, unsigned char, flagImageType(observed)) *
        flag_accept_type_frame(platform, sg, invocation, origin, irq_mask, view, pe, before, observed)
    */
    if (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG) {          /* Validate event block type                */
        /*@ flag_accept_profile(sg) && pe != 0 && flagImageType(observed) != 5 &&
            data_at(&((OS_FLAG_GRP *)pe)->OSFlagType, unsigned char, flagImageType(observed)) *
            flag_accept_type_frame(platform, sg, invocation, origin, irq_mask, view, pe, before, observed)
            which implies
            flag_accept_before_resource(platform, critical, sg, invocation, origin, irq_mask, view, pe, before, observed)
        */
        *perr = OS_ERR_EVENT_TYPE;
        return ((OS_FLAGS)0);
    }
    /*@ flag_accept_profile(sg) && flagImageType(observed) == 5 &&
        data_at(&((OS_FLAG_GRP *)pe)->OSFlagType, unsigned char, flagImageType(observed)) *
        flag_accept_type_frame(platform, sg, invocation, origin, irq_mask, view, pe, before, observed)
        which implies flag_accept_profile(sg) && flagImageType(observed) == 5 &&
        flag_accept_admission(sg, pe, view, before, observed) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, irq_mask, before) *
        flag_accept_source_rep(sg, pe, view)
    */
    /*@ 0 <= wait_type && wait_type <= 255 && 0 <= flags && flags <= 65535 by local */
    result = (INT8U)(wait_type & OS_FLAG_CONSUME);
    if (result != (INT8U)0) {                              /* See if we need to consume the flags      */
        wait_type &= ~OS_FLAG_CONSUME;
        consume    = OS_TRUE;
    } else {
        consume    = OS_FALSE;
    }

    *perr = OS_ERR_NONE;                                   /* Assume NO error until proven otherwise.  */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
        flag_accept_profile(sg) && pe != 0 && flagImageType(observed) == 5 &&
        flag_accept_admission(sg, pe, view, before, observed) &&
        time_get_acquire_facts(critical, sg, invocation, irq_mask, cpu_sr, before, entry) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, entry) * flag_accept_source_rep(sg, pe, view)
        which implies exists (entry: UCOS2_Verify_State) (image: FlagGroupImage),
        data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, flagImageBits(image)) *
        flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, cpu_sr,
          view, pe, before, observed, entry, image)
    */
    /*@ Given entry image */
    /*@ Assert exists (acquired_saved: Z),
        pgrp == pe && perr == error_addr && flags == requested &&
        0 <= wait_request && wait_request <= 255 && 0 <= requested && requested <= 65535 &&
        wait_type == flag_accept_mode(wait_request) &&
        result == flag_accept_consume_bit(wait_request) &&
        consume == flag_accept_consume_value(wait_request) && cpu_sr == acquired_saved &&
        flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
          requested, wait_request, before, X) &&
        caller_frame * undef_data_at(&flags_rdy, unsigned short) * data_at(error_addr, unsigned char, 0) *
        data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, flagImageBits(image)) *
        flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, acquired_saved,
          view, pe, before, observed, entry, image)
    */
    /*@ Given acquired_saved */
    switch (wait_type) {
        case OS_FLAG_WAIT_SET_ALL:                         /* See if all required flags are set        */
             flags_rdy = (OS_FLAGS)(pgrp->OSFlagFlags & flags);     /* Extract only the bits we want   */
             if (flags_rdy == flags) {                     /* Must match ALL the bits that we want     */
                 if (consume == OS_TRUE) {                 /* See if we need to consume the flags      */
                     pgrp->OSFlagFlags &= (OS_FLAGS)~flags_rdy;     /* Clear ONLY the flags we wanted  */
                 }
             } else {
                 *perr = OS_ERR_FLAG_NOT_RDY;
             }
             /*@ Assert exists (bits: Z) (error: Z) (ready: Z) (saved: Z),
                 pgrp == pe && perr == error_addr && flags == requested &&
                 0 <= wait_request && wait_request <= 255 && 0 <= requested && requested <= 65535 &&
                 wait_type == flag_accept_mode(wait_request) &&
                 result == flag_accept_consume_bit(wait_request) &&
                 consume == flag_accept_consume_value(wait_request) &&
                 cpu_sr == saved && flags_rdy == ready && 0 <= bits && bits <= 65535 &&
                 flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, bits, ready, error) &&
                 caller_frame * data_at(error_addr, unsigned char, error) *
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, bits) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
             */
             /*@ Given bits error ready saved */
             /*@ 0 <= bits && bits <= 65535 &&
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, bits) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
                 which implies
                 mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, irq_mask, saved,
                   entry, flag_accept_released(view, entry, image, bits)) *
                 flag_accept_raw_post(sg, pe, view, image, bits)
             */
             OS_EXIT_CRITICAL();
             /*@ flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, bits, ready, error) &&
                 time_get_restore_post(platform, critical, sg, invocation, origin, saved,
                   flag_accept_released(view, entry, image, bits)) *
                 flag_accept_raw_post(sg, pe, view, image, bits) * data_at(error_addr, unsigned char, error)
                 which implies
                 flag_accept_api_post(platform, critical, sg, invocation, origin, irq_mask,
                   view, pe, error_addr, before, observed, requested, wait_request, ready, X)
             */
             break;

        case OS_FLAG_WAIT_SET_ANY:
             flags_rdy = (OS_FLAGS)(pgrp->OSFlagFlags & flags);     /* Extract only the bits we want   */
             if (flags_rdy != (OS_FLAGS)0) {               /* See if any flag set                      */
                 if (consume == OS_TRUE) {                 /* See if we need to consume the flags      */
                     pgrp->OSFlagFlags &= (OS_FLAGS)~flags_rdy;     /* Clear ONLY the flags we got     */
                 }
             } else {
                 *perr = OS_ERR_FLAG_NOT_RDY;
             }
             /*@ Assert exists (bits: Z) (error: Z) (ready: Z) (saved: Z),
                 pgrp == pe && perr == error_addr && flags == requested &&
                 0 <= wait_request && wait_request <= 255 && 0 <= requested && requested <= 65535 &&
                 wait_type == flag_accept_mode(wait_request) &&
                 result == flag_accept_consume_bit(wait_request) &&
                 consume == flag_accept_consume_value(wait_request) &&
                 cpu_sr == saved && flags_rdy == ready && 0 <= bits && bits <= 65535 &&
                 flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, bits, ready, error) &&
                 caller_frame * data_at(error_addr, unsigned char, error) *
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, bits) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
             */
             /*@ Given bits error ready saved */
             /*@ 0 <= bits && bits <= 65535 &&
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, bits) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
                 which implies
                 mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, irq_mask, saved,
                   entry, flag_accept_released(view, entry, image, bits)) *
                 flag_accept_raw_post(sg, pe, view, image, bits)
             */
             OS_EXIT_CRITICAL();
             /*@ flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, bits, ready, error) &&
                 time_get_restore_post(platform, critical, sg, invocation, origin, saved,
                   flag_accept_released(view, entry, image, bits)) *
                 flag_accept_raw_post(sg, pe, view, image, bits) * data_at(error_addr, unsigned char, error)
                 which implies
                 flag_accept_api_post(platform, critical, sg, invocation, origin, irq_mask,
                   view, pe, error_addr, before, observed, requested, wait_request, ready, X)
             */
             break;

#if OS_FLAG_WAIT_CLR_EN > 0u
        case OS_FLAG_WAIT_CLR_ALL:                         /* See if all required flags are cleared    */
             flags_rdy = (OS_FLAGS)~pgrp->OSFlagFlags & flags;    /* Extract only the bits we want     */
             if (flags_rdy == flags) {                     /* Must match ALL the bits that we want     */
                 if (consume == OS_TRUE) {                 /* See if we need to consume the flags      */
                     pgrp->OSFlagFlags |= flags_rdy;       /* Set ONLY the flags that we wanted        */
                 }
             } else {
                 *perr = OS_ERR_FLAG_NOT_RDY;
             }
             /*@ Assert exists (bits: Z) (error: Z) (ready: Z) (saved: Z),
                 pgrp == pe && perr == error_addr && flags == requested &&
                 0 <= wait_request && wait_request <= 255 && 0 <= requested && requested <= 65535 &&
                 wait_type == flag_accept_mode(wait_request) &&
                 result == flag_accept_consume_bit(wait_request) &&
                 consume == flag_accept_consume_value(wait_request) &&
                 cpu_sr == saved && flags_rdy == ready && 0 <= bits && bits <= 65535 &&
                 flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, bits, ready, error) &&
                 caller_frame * data_at(error_addr, unsigned char, error) *
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, bits) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
             */
             /*@ Given bits error ready saved */
             /*@ 0 <= bits && bits <= 65535 &&
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, bits) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
                 which implies
                 mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, irq_mask, saved,
                   entry, flag_accept_released(view, entry, image, bits)) *
                 flag_accept_raw_post(sg, pe, view, image, bits)
             */
             OS_EXIT_CRITICAL();
             /*@ flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, bits, ready, error) &&
                 time_get_restore_post(platform, critical, sg, invocation, origin, saved,
                   flag_accept_released(view, entry, image, bits)) *
                 flag_accept_raw_post(sg, pe, view, image, bits) * data_at(error_addr, unsigned char, error)
                 which implies
                 flag_accept_api_post(platform, critical, sg, invocation, origin, irq_mask,
                   view, pe, error_addr, before, observed, requested, wait_request, ready, X)
             */
             break;

        case OS_FLAG_WAIT_CLR_ANY:
             flags_rdy = (OS_FLAGS)~pgrp->OSFlagFlags & flags;   /* Extract only the bits we want      */
             if (flags_rdy != (OS_FLAGS)0) {               /* See if any flag cleared                  */
                 if (consume == OS_TRUE) {                 /* See if we need to consume the flags      */
                     pgrp->OSFlagFlags |= flags_rdy;       /* Set ONLY the flags that we got           */
                 }
             } else {
                 *perr = OS_ERR_FLAG_NOT_RDY;
             }
             /*@ Assert exists (bits: Z) (error: Z) (ready: Z) (saved: Z),
                 pgrp == pe && perr == error_addr && flags == requested &&
                 0 <= wait_request && wait_request <= 255 && 0 <= requested && requested <= 65535 &&
                 wait_type == flag_accept_mode(wait_request) &&
                 result == flag_accept_consume_bit(wait_request) &&
                 consume == flag_accept_consume_value(wait_request) &&
                 cpu_sr == saved && flags_rdy == ready && 0 <= bits && bits <= 65535 &&
                 flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, bits, ready, error) &&
                 caller_frame * data_at(error_addr, unsigned char, error) *
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, bits) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
             */
             /*@ Given bits error ready saved */
             /*@ 0 <= bits && bits <= 65535 &&
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, bits) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
                 which implies
                 mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, irq_mask, saved,
                   entry, flag_accept_released(view, entry, image, bits)) *
                 flag_accept_raw_post(sg, pe, view, image, bits)
             */
             OS_EXIT_CRITICAL();
             /*@ flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, bits, ready, error) &&
                 time_get_restore_post(platform, critical, sg, invocation, origin, saved,
                   flag_accept_released(view, entry, image, bits)) *
                 flag_accept_raw_post(sg, pe, view, image, bits) * data_at(error_addr, unsigned char, error)
                 which implies
                 flag_accept_api_post(platform, critical, sg, invocation, origin, irq_mask,
                   view, pe, error_addr, before, observed, requested, wait_request, ready, X)
             */
             break;
#endif

        default:
             /*@ Assert exists (saved: Z),
                 pgrp == pe && perr == error_addr && flags == requested &&
                 0 <= wait_request && wait_request <= 255 && 0 <= requested && requested <= 65535 &&
                 wait_type == flag_accept_mode(wait_request) &&
                 result == flag_accept_consume_bit(wait_request) &&
                 consume == flag_accept_consume_value(wait_request) && cpu_sr == saved &&
                 0 <= flagImageBits(image) && flagImageBits(image) <= 65535 &&
                 flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, flagImageBits(image), 0, 111) &&
                 caller_frame * undef_data_at(&flags_rdy, unsigned short) * data_at(error_addr, unsigned char, 0) *
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, flagImageBits(image)) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
             */
             /*@ Given saved */
             /*@ 0 <= flagImageBits(image) && flagImageBits(image) <= 65535 &&
                 data_at(&((OS_FLAG_GRP *)pe)->OSFlagFlags, unsigned short, flagImageBits(image)) *
                 flag_accept_bits_frame(platform, critical, sg, invocation, origin, irq_mask, saved,
                   view, pe, before, observed, entry, image)
                 which implies
                 mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, irq_mask, saved,
                   entry, flag_accept_released(view, entry, image, flagImageBits(image))) *
                 flag_accept_raw_post(sg, pe, view, image, flagImageBits(image))
             */
             OS_EXIT_CRITICAL();
             flags_rdy = (OS_FLAGS)0;
             *perr     = OS_ERR_FLAG_WAIT_TYPE;
             /*@ flag_accept_safe(critical, sg, invocation, view, pe, flagImageType(observed),
                   requested, wait_request, before, X) &&
                 flag_accept_checkpoint_facts(critical, sg, invocation, irq_mask, saved,
                   view, pe, before, observed, entry, image, requested, wait_request, flagImageBits(image), 0, 111) &&
                 time_get_restore_post(platform, critical, sg, invocation, origin, saved,
                   flag_accept_released(view, entry, image, flagImageBits(image))) *
                 flag_accept_raw_post(sg, pe, view, image, flagImageBits(image)) * data_at(error_addr, unsigned char, 111)
                 which implies
                 flag_accept_api_post(platform, critical, sg, invocation, origin, irq_mask,
                   view, pe, error_addr, before, observed, requested, wait_request, 0, X)
             */
             break;
    }
    return (flags_rdy);
}
