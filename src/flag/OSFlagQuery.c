/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_FLAGS  OSFlagQuery (OS_FLAG_GRP  *pgrp,
                       INT8U        *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (view: FlagQueryView)
    (observed: FlagGroupImage) (p error_addr: addr) (caller_frame: Assertion)
    (X: Z -> Z -> UCOS2_Verify_State -> Prop)
    Require pgrp == p && perr == error_addr &&
      flag_query_admission(sg, p, view, before, observed) &&
      flag_query_safe(critical, sg, invocation, p, view, before, X) &&
      undef_data_at(perr, unsigned char) *
      flag_query_resources(platform, critical, sg, invocation, origin, mask, p, view, before) * caller_frame
    Ensure flag_query_api_post(platform, critical, sg, invocation, origin, mask,
      p, error_addr, view, before, __return, X) * caller_frame
*/
{
    OS_FLAGS   flags;
#if OS_CRITICAL_METHOD == 3u                      /* Allocate storage for CPU status register          */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_FLAGS)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pgrp == (OS_FLAG_GRP *)0) {               /* Validate 'pgrp'                                   */
        *perr = OS_ERR_FLAG_INVALID_PGRP;
        return ((OS_FLAGS)0);
    }
#endif
    /*@ pgrp == p && pgrp != 0 &&
        flag_query_admission(sg, p, view, before, observed) &&
        flag_query_resources(platform, critical, sg, invocation, origin, mask, p, view, before)
        which implies pgrp == p && pgrp != 0 &&
        flag_query_admission(sg, p, view, before, observed) &&
        data_at(&(pgrp->OSFlagType), unsigned char, flagImageType(observed)) *
        flag_query_type_frame(platform, critical, sg, invocation, origin, mask, p, view, before, observed)
    */
    if (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG) { /* Validate event block type                         */
        /*@ pgrp == p && pgrp != 0 && flagImageType(observed) != 5 &&
            flag_query_admission(sg, p, view, before, observed) &&
            data_at(&(pgrp->OSFlagType), unsigned char, flagImageType(observed)) *
            flag_query_type_frame(platform, critical, sg, invocation, origin, mask, p, view, before, observed)
            which implies pgrp == p && pgrp != 0 && flagImageType(observed) != 5 &&
            flag_query_admission(sg, p, view, before, observed) &&
            flag_query_resources(platform, critical, sg, invocation, origin, mask, p, view, before)
        */
        *perr = OS_ERR_EVENT_TYPE;
        return ((OS_FLAGS)0);
    }
    /*@ pgrp == p && pgrp != 0 && flagImageType(observed) == 5 &&
        flag_query_admission(sg, p, view, before, observed) &&
        data_at(&(pgrp->OSFlagType), unsigned char, flagImageType(observed)) *
        flag_query_type_frame(platform, critical, sg, invocation, origin, mask, p, view, before, observed)
        which implies pgrp == p && pgrp != 0 && flagImageType(observed) == 5 &&
        flag_query_admission(sg, p, view, before, observed) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
        flag_query_private_words(p, view)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
        pgrp == p && pgrp != 0 && flagImageType(observed) == 5 &&
        flag_query_admission(sg, p, view, before, observed) &&
        time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, entry) * flag_query_private_words(p, view)
        which implies exists (entry: UCOS2_Verify_State) (acquired: FlagGroupImage),
        pgrp == p && pgrp != 0 && flagImageType(observed) == 5 &&
        flag_query_admission(sg, p, view, before, observed) &&
        time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        flag_query_selected(view, entry, acquired) &&
        0 <= flagImageBits(acquired) && flagImageBits(acquired) <= 65535 &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&(pgrp->OSFlagFlags), unsigned short, flagImageBits(acquired)) *
        flag_query_flags_frame(sg, p, view, entry, acquired)
    */
    /*@ Given entry acquired */
    flags = pgrp->OSFlagFlags;
    /*@ pgrp == p && pgrp != 0 &&
        flag_query_admission(sg, p, view, before, observed) && flag_query_selected(view, entry, acquired) &&
        data_at(&(pgrp->OSFlagFlags), unsigned short, flagImageBits(acquired)) *
        flag_query_flags_frame(sg, p, view, entry, acquired)
        which implies pgrp == p && pgrp != 0 &&
        flag_query_admission(sg, p, view, before, observed) && flag_query_selected(view, entry, acquired) &&
        UCOS2_inv(sg, entry) * flag_query_private_words(p, view)
    */
    OS_EXIT_CRITICAL();
    *perr = OS_ERR_NONE;
    return (flags);                               /* Return the current value of the event flags       */
}
