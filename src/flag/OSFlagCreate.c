/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_FLAG_GRP  *OSFlagCreate (OS_FLAGS  flags,
                            INT8U    *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask bits error_addr: Z) (before: UCOS2_Verify_State)
    (LitMap: String -> Z) (literals: list String) (caller_frame: Assertion)
    (X: Z -> Z -> UCOS2_Verify_State -> Prop)
    Require flags == bits && 0 <= bits && bits <= 65535 && perr == error_addr &&
      flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
      flag_create_name_admission(critical, sg, invocation, before, LitMap("?")) &&
      flag_create_safe(critical, sg, invocation, bits, LitMap("?"), before, X) &&
      undef_data_at(perr, unsigned char) *
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
      caller_frame * GlobalStrings_missing(LitMap, literals)
    Ensure flag_create_api_post(platform, critical, sg, invocation, origin, mask,
      bits, LitMap("?"), error_addr, before, __return, X) *
      caller_frame * GlobalStrings_missing(LitMap, literals)
*/
{
    OS_FLAG_GRP *pgrp;
#if OS_CRITICAL_METHOD == 3u                        /* Allocate storage for CPU status register        */
    OS_CPU_SR    cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_FLAG_GRP *)0);
    }
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        *perr = OS_ERR_ILLEGAL_CREATE_RUN_TIME;
        return ((OS_FLAG_GRP *)0);
    }
#endif

    /*@ flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
        data_at(&OSIntNesting, unsigned char, flag_create_depth(before)) *
        flag_create_interrupt_frame(platform, critical, sg, invocation, origin, mask, before)
    */
    if (OSIntNesting > 0u) {                        /* See if called from ISR ...                      */
        /*@ flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
            0 < flag_create_depth(before) &&
            data_at(&OSIntNesting, unsigned char, flag_create_depth(before)) *
            flag_create_interrupt_frame(platform, critical, sg, invocation, origin, mask, before)
            which implies flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
            0 < flag_create_depth(before) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        */
        *perr = OS_ERR_CREATE_ISR;                  /* ... can't CREATE from an ISR                    */
        return ((OS_FLAG_GRP *)0);
    }
    /*@ flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
        flag_create_depth(before) <= 0 &&
        data_at(&OSIntNesting, unsigned char, flag_create_depth(before)) *
        flag_create_interrupt_frame(platform, critical, sg, invocation, origin, mask, before)
        which implies flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
        flag_create_depth(before) <= 0 &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
        flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
        time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies exists (entry: UCOS2_Verify_State),
        flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
        time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&OSFlagFreeList, OS_FLAG_GRP *, flag_create_free_head(sg, entry)) * flag_create_pool_frame(sg, entry)
    */
    /*@ Given entry */
    pgrp = OSFlagFreeList;                          /* Get next free event flag                        */
    if (pgrp != (OS_FLAG_GRP *)0) {                 /* See if we have event flag groups available      */
        /*@ flags == bits && 0 <= bits && bits <= 65535 &&
            pgrp == flag_create_free_head(sg, entry) && pgrp != 0 &&
            flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
            flag_create_depth(before) <= 0 &&
            flag_create_name_admission(critical, sg, invocation, before, LitMap("?")) &&
            time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
            data_at(&OSFlagFreeList, OS_FLAG_GRP *, pgrp) * flag_create_pool_frame(sg, entry)
            which implies exists (id: Z) (rest: list Z) (old: FlagGroupImage),
            flags == bits && 0 <= bits && bits <= 65535 &&
            pgrp == flag_pool_addr(sg, id) && pgrp == flag_create_free_head(sg, entry) && pgrp != 0 &&
            flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
            flag_create_depth(before) <= 0 &&
            time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
            flag_create_slot(sg, entry, id, rest, old) && flag_create_default_name(entry, LitMap("?")) &&
            data_at(&OSFlagFreeList, OS_FLAG_GRP *, pgrp) *
            data_at(&(pgrp->OSFlagType), unsigned char, 0) *
            data_at(&(pgrp->OSFlagWaitList), void *, flagImageHead(old)) *
            data_at(&(pgrp->OSFlagFlags), unsigned short, flagImageBits(old)) *
            data_at(&(pgrp->OSFlagName), INT8U *, flagImageName(old)) *
            flag_create_fields_frame(sg, entry, id, old)
        */
        /*@ Given id rest old */
                                                    /* Adjust free list                                */
        OSFlagFreeList       = (OS_FLAG_GRP *)OSFlagFreeList->OSFlagWaitList;
        pgrp->OSFlagType     = OS_EVENT_TYPE_FLAG;  /* Set to event flag group type                    */
        pgrp->OSFlagFlags    = flags;               /* Set to desired initial value                    */
        pgrp->OSFlagWaitList = (void *)0;           /* Clear list of tasks waiting on flags            */
#if OS_FLAG_NAME_EN > 0u
        /*@ flag_create_default_name(entry, LitMap("?")) && flag_create_fields_frame(sg, entry, id, old)
            which implies flag_create_default_name(entry, LitMap("?")) &&
            store_stringLit(LitMap("?"), "?") * flag_create_literal_frame(sg, entry, id, old, LitMap("?"))
        */
        pgrp->OSFlagName     = (INT8U *)(void *)"?";
        /*@ flag_create_default_name(entry, LitMap("?")) &&
            store_stringLit(LitMap("?"), "?") * flag_create_literal_frame(sg, entry, id, old, LitMap("?"))
            which implies flag_create_default_name(entry, LitMap("?")) && flag_create_fields_frame(sg, entry, id, old)
        */
#endif
        OS_TRACE_FLAG_CREATE(pgrp, pgrp->OSFlagName);
        /*@ flags == bits && 0 <= bits && bits <= 65535 &&
            pgrp == flag_create_free_head(sg, entry) && pgrp != 0 &&
            flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
            flag_create_slot(sg, entry, id, rest, old) && flag_create_default_name(entry, LitMap("?")) &&
            data_at(&OSFlagFreeList, OS_FLAG_GRP *, flagImageHead(old)) *
            data_at(&(pgrp->OSFlagType), unsigned char, 5) *
            data_at(&(pgrp->OSFlagWaitList), void *, 0) *
            data_at(&(pgrp->OSFlagFlags), unsigned short, bits) *
            data_at(&(pgrp->OSFlagName), INT8U *, LitMap("?")) * flag_create_fields_frame(sg, entry, id, old)
            which implies flags == bits && pgrp == flag_create_free_head(sg, entry) && pgrp != 0 &&
            flag_create_effect(sg, entry, bits, LitMap("?"), pgrp, 0, flag_create_checkpoint(entry, bits, LitMap("?"))) &&
            UCOS2_state_inv(sg, flag_create_checkpoint(entry, bits, LitMap("?"))) &&
            UCOS2_inv(sg, flag_create_checkpoint(entry, bits, LitMap("?")))
        */
        /*@ time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
            UCOS2_state_inv(sg, flag_create_checkpoint(entry, bits, LitMap("?"))) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
            UCOS2_inv(sg, flag_create_checkpoint(entry, bits, LitMap("?")))
            which implies time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
            mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr,
              entry, flag_create_checkpoint(entry, bits, LitMap("?")))
        */
        OS_EXIT_CRITICAL();
        *perr                = OS_ERR_NONE;
    } else {
        /*@ pgrp == 0 && pgrp == flag_create_free_head(sg, entry) &&
            flag_create_layout(sg, &OSIntNesting, &OSFlagFreeList) &&
            data_at(&OSFlagFreeList, OS_FLAG_GRP *, pgrp) * flag_create_pool_frame(sg, entry)
            which implies pgrp == 0 && pgrp == flag_create_free_head(sg, entry) &&
            flag_create_effect(sg, entry, bits, LitMap("?"), pgrp, 114, entry) &&
            UCOS2_state_inv(sg, entry) && UCOS2_inv(sg, entry)
        */
        /*@ time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
            UCOS2_state_inv(sg, entry) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
            which implies time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
            mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry, entry)
        */
        OS_EXIT_CRITICAL();
        *perr                = OS_ERR_FLAG_GRP_DEPLETED;
    }
    return (pgrp);                                  /* Return pointer to event flag group              */
}
