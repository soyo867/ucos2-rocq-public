/* Single-function annotation candidate. Original executable tokens retained.
 * Rebuild with fixed Timer profile and tmr_stop_verification.h.
 * Full canonical targets and manual proof remain to be checked.
 */

BOOLEAN  OSTmrStop (OS_TMR  *ptmr,
                    INT8U    opt,
                    void    *callback_arg,
                    INT8U   *perr)
/*@ timer_stop_public_spec
    With {Client} (ClientRep : Client -> Assertion)
         (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (callback : Z -> Z -> Z -> OsSchedCallContext -> program (TmrStopState (TmrStopCallApplication Client)) OsSchedCallContext)
         (AppRep : TmrStopCallApplication Client -> Assertion) (effects : TmrStopEffects (TmrStopCallApplication Client))
         (raw_type : TmrStopState (TmrStopCallApplication Client) -> Z) (raw_state : TmrStopState (TmrStopCallApplication Client) -> Z)
         (domain : Z -> Z -> Z -> OsSchedCallContext -> TmrStopState (TmrStopCallApplication Client) -> Prop)
         (mask nesting p i option argument error_addr : Z) (pooled : bool)
         (context : OsSchedCallContext) (before : TmrStopState (TmrStopCallApplication Client))
         (X : tmr_stop_output -> TmrStopState (TmrStopCallApplication Client) -> Prop)
    Require ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        tmr_stop_call_pre(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, X)
    Ensure tmr_stop_call_post(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, __return, X)
*/
{
    OS_TMR_CALLBACK  pfnct;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr && AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) && tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) && tmr_stop_call_pre(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, X) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */


#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (OS_FALSE);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (ptmr == (OS_TMR *)0) {
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p == 0 &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p == 0 &&
        undef_data_at(perr, INT8U) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
        *perr = OS_ERR_TMR_INVALID;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p == 0 &&
        data_at(perr, INT8U, 138) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p == 0 &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(138, before)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Assert tmr_stop_call_post(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, 0, X) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
        data_at(&ptmr, OS_TMR *, p) *
        data_at(&opt, INT8U, option) *
        data_at(&callback_arg, void *, argument) *
        data_at(&perr, INT8U *, error_addr) */
        return (OS_FALSE);
    }
#endif

    OS_TRACE_TMR_STOP_ENTER(ptmr);

    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (ty : Z),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        data_at(&(ptmr->OSTmrType), INT8U, ty) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, before, p, StopTypeField, ty) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given ty */
    if (ptmr->OSTmrType != OS_TMR_TYPE) {                         /* Validate timer structure                         */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty != 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        data_at(&(ptmr->OSTmrType), INT8U, ty) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, before, p, StopTypeField, ty) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty != 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty != 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty != 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        undef_data_at(perr, INT8U) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
        *perr = OS_ERR_TMR_INVALID_TYPE;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty != 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        data_at(perr, INT8U, 137) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty != 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(137, before)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Assert tmr_stop_call_post(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, 0, X) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
        data_at(&ptmr, OS_TMR *, p) *
        data_at(&opt, INT8U, option) *
        data_at(&callback_arg, void *, argument) *
        data_at(&perr, INT8U *, error_addr) */
        OS_TRACE_TMR_STOP_EXIT(*perr);
        return (OS_FALSE);
    }
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        data_at(&(ptmr->OSTmrType), INT8U, ty) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, before, p, StopTypeField, ty) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && 0 <= os_sched_lock_ints(tmr_stop_kernel(before)) && os_sched_lock_ints(tmr_stop_kernel(before)) <= 255 &&
        data_at(&OSIntNesting, INT8U, os_sched_lock_ints(tmr_stop_kernel(before))) * tmr_stop_interrupt_rest(external, platform, sg, mask, context, tmr_stop_kernel(before)) * tmr_stop_entry_client_rep(AppRep, error_addr, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    if (OSIntNesting > 0u) {                                      /* See if trying to call from an ISR                */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        data_at(&OSIntNesting, INT8U, os_sched_lock_ints(tmr_stop_kernel(before))) * tmr_stop_interrupt_rest(external, platform, sg, mask, context, tmr_stop_kernel(before)) * tmr_stop_entry_client_rep(AppRep, error_addr, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) > 0 &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) > 0 &&
        undef_data_at(perr, INT8U) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
        *perr  = OS_ERR_TMR_ISR;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) > 0 &&
        data_at(perr, INT8U, 139) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) > 0 &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(139, before)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Assert tmr_stop_call_post(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, 0, X) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
        data_at(&ptmr, OS_TMR *, p) *
        data_at(&opt, INT8U, option) *
        data_at(&callback_arg, void *, argument) *
        data_at(&perr, INT8U *, error_addr) */
        OS_TRACE_TMR_STOP_EXIT(*perr);
        return (OS_FALSE);
    }
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        data_at(&OSIntNesting, INT8U, os_sched_lock_ints(tmr_stop_kernel(before))) * tmr_stop_interrupt_rest(external, platform, sg, mask, context, tmr_stop_kernel(before)) * tmr_stop_entry_client_rep(AppRep, error_addr, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) == 0 &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) == 0 &&
        os_sched_lock_program_pre(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, tmr_stop_kernel(before), tmr_stop_call_kernel_any) * os_sched_context_resources(external, context) * unmap_table_rep(sg) * tmr_stop_entry_client_rep(AppRep, error_addr, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    OSSchedLock() /*@ where (timer_stop_lock_spec) platform=platform, critical=critical, sg=sg, invocation=os_sched_call_invocation(context), origin=os_sched_call_origin(context), mask=mask, before=tmr_stop_kernel(before), Xk=tmr_stop_call_kernel_any */;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) == 0 &&
        os_sched_lock_program_post(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, tmr_stop_kernel(before), tmr_stop_call_kernel_any) * os_sched_context_resources(external, context) * unmap_table_rep(sg) * tmr_stop_entry_client_rep(AppRep, error_addr, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (locked : TmrStopState (TmrStopCallApplication Client)),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) == 0 && tmr_stop_call_lock_step(critical, sg, effects, context, before, locked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given locked */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) == 0 && tmr_stop_call_lock_step(critical, sg, effects, context, before, locked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (status : Z),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) == 0 && tmr_stop_call_lock_step(critical, sg, effects, context, before, locked) && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopStateField, locked, status) &&
        data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, locked, p, StopStateField, status) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given status */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        p != 0 && ty == 100 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopTypeField, before, ty) && os_sched_lock_ints(tmr_stop_kernel(before)) == 0 && tmr_stop_call_lock_step(critical, sg, effects, context, before, locked) && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopStateField, locked, status) &&
        data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, locked, p, StopStateField, status) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) &&
        data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, locked, p, StopStateField, status) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    switch (ptmr->OSTmrState) {
        case OS_TMR_STATE_RUNNING:
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        status == 3 && tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) &&
        data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, locked, p, StopStateField, status) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        status == 3 && tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && p == timer_pool_addr(sg, i) && timer_api_initialized(TimerState(tmr_stop_kernel(locked))) && tmr_unlink_running(TimerState(tmr_stop_kernel(locked)), i) &&
        timer_inv(sg, TimerState(tmr_stop_kernel(locked))) * tmr_stop_call_unlink_client_frame(AppRep, external, platform, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             OSTmr_Unlink(ptmr) /*@ where (timer_stop_unlink_configured_spec) sg=sg, s=TimerState(tmr_stop_kernel(locked)), i=i, R=tmr_stop_call_unlink_client_frame(AppRep, external, platform, sg, mask, error_addr, context, locked) */;                                  /* Remove from current wheel spoke                  */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && p == timer_pool_addr(sg, i) && timer_api_initialized(TimerState(tmr_stop_kernel(locked))) && tmr_unlink_running(TimerState(tmr_stop_kernel(locked)), i) &&
        tmr_unlink_configured_post(sg, TimerState(tmr_stop_kernel(locked)), i) * tmr_stop_call_unlink_client_frame(AppRep, external, platform, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (stopped : TmrStopState (TmrStopCallApplication Client)),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, stopped) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given stopped */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, stopped) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) &&
        undef_data_at(perr, INT8U) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, stopped) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             *perr = OS_ERR_NONE;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) &&
        data_at(perr, INT8U, 0) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, stopped) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             switch (opt) {
                 case OS_TMR_OPT_CALLBACK:
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (fn : Z),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK, fn) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopCallbackField, fn) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given fn */
                      pfnct = ptmr->OSTmrCallback;                /* Execute callback function if available ...       */
                      if (pfnct != (OS_TMR_CALLBACK)0) {
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK, fn) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopCallbackField, fn) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        exists (stored_arg : Z),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopArgumentField, tmr_stop_set_error(0, stopped), stored_arg) &&
        data_at(&(ptmr->OSTmrCallbackArg), void *, stored_arg) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopArgumentField, stored_arg) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
    /*@ Given stored_arg */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopArgumentField, tmr_stop_set_error(0, stopped), stored_arg) &&
        data_at(&(ptmr->OSTmrCallbackArg), void *, stored_arg) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopArgumentField, stored_arg) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_callback_prefix(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, fn, p, stored_arg, tmr_stop_set_error(0, stopped)) && domain(fn, p, stored_arg, context, tmr_stop_set_error(0, stopped)) &&
        (fn |= void (void *cb_self, void *cb_arg)
          With (call_context : OsSchedCallContext) (call_before : TmrStopState (TmrStopCallApplication Client))
          Require domain(fn, p, stored_arg, call_context, call_before) &&
                  eq(pair(cb_self, cb_arg), pair(p, stored_arg)) &&
                  data_at(&((OS_TMR *)cb_self)->OSTmrCallbackArg, void *, stored_arg) *
                  tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, call_context, call_before, p, StopArgumentField, stored_arg)
          Ensure tmr_stop_callback_post(AppRep, external, platform, critical, sg, effects, mask, error_addr, fn, p, stored_arg, call_context, call_before, pair(cb_self, cb_arg), tt)) * data_at(&(ptmr->OSTmrCallbackArg), void *, stored_arg) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopArgumentField, stored_arg) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
                          (*pfnct)((void *)ptmr, ptmr->OSTmrCallbackArg) /*@ where call_context=context, call_before=tmr_stop_set_error(0, stopped) */;  /* Use callback arg when timer was created */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_callback_prefix(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, fn, p, stored_arg, tmr_stop_set_error(0, stopped)) &&
        tmr_stop_callback_post(AppRep, external, platform, critical, sg, effects, mask, error_addr, fn, p, stored_arg, context, tmr_stop_set_error(0, stopped), pair(p, stored_arg), tt) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_ready(AppRep, external, platform, critical, sg, effects, mask, error_addr, pooled, p, i, option, argument, raw_type, raw_state, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
                      } else {
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK, fn) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopCallbackField, fn) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(perr, INT8U, tmr_stop_error(tmr_stop_set_error(0, stopped))) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
                          *perr = OS_ERR_TMR_NO_CALLBACK;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(perr, INT8U, 143) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(143, tmr_stop_set_error(0, stopped))) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 3 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(143, tmr_stop_set_error(0, stopped))) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_ready(AppRep, external, platform, critical, sg, effects, mask, error_addr, pooled, p, i, option, argument, raw_type, raw_state, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
                      }
                      break;

                 case OS_TMR_OPT_CALLBACK_ARG:
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (fn : Z),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK, fn) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopCallbackField, fn) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given fn */
                      pfnct = ptmr->OSTmrCallback;                /* Execute callback function if available ...       */
                      if (pfnct != (OS_TMR_CALLBACK)0) {
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK, fn) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopCallbackField, fn) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn != 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_callback_prefix(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, fn, p, argument, tmr_stop_set_error(0, stopped)) && domain(fn, p, argument, context, tmr_stop_set_error(0, stopped)) &&
        (fn |= void (void *cb_self, void *cb_arg)
          With (call_context : OsSchedCallContext) (call_before : TmrStopState (TmrStopCallApplication Client))
          Require domain(fn, p, argument, call_context, call_before) &&
                  eq(pair(cb_self, cb_arg), pair(p, argument)) &&
                  tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, call_context, call_before)
          Ensure tmr_stop_callback_post(AppRep, external, platform, critical, sg, effects, mask, error_addr, fn, p, argument, call_context, call_before, pair(cb_self, cb_arg), tt)) * tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
                          (*pfnct)((void *)ptmr, callback_arg) /*@ where call_context=context, call_before=tmr_stop_set_error(0, stopped) */;   /* ... using the 'callback_arg' provided in call    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_callback_prefix(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, fn, p, argument, tmr_stop_set_error(0, stopped)) &&
        tmr_stop_callback_post(AppRep, external, platform, critical, sg, effects, mask, error_addr, fn, p, argument, context, tmr_stop_set_error(0, stopped), pair(p, argument), tt) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_ready(AppRep, external, platform, critical, sg, effects, mask, error_addr, pooled, p, i, option, argument, raw_type, raw_state, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
                      } else {
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK, fn) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, true, context, tmr_stop_set_error(0, stopped), p, StopCallbackField, fn) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(perr, INT8U, tmr_stop_error(tmr_stop_set_error(0, stopped))) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
                          *perr = OS_ERR_TMR_NO_CALLBACK;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        data_at(perr, INT8U, 143) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, tmr_stop_set_error(0, stopped)) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(143, tmr_stop_set_error(0, stopped))) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 4 && fn == 0 && tmr_stop_call_field_read(pooled, i, raw_type, raw_state, StopCallbackField, tmr_stop_set_error(0, stopped), fn) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(143, tmr_stop_set_error(0, stopped))) *
        data_at(&pfnct, OS_TMR_CALLBACK, fn)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_ready(AppRep, external, platform, critical, sg, effects, mask, error_addr, pooled, p, i, option, argument, raw_type, raw_state, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
                      }
                      break;

                 case OS_TMR_OPT_NONE:
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option == 0 &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_ready(AppRep, external, platform, critical, sg, effects, mask, error_addr, pooled, p, i, option, argument, raw_type, raw_state, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
                      break;

                 default:
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option != 0 && option != 3 && option != 4 &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(0, stopped)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option != 0 && option != 3 && option != 4 &&
        data_at(perr, INT8U, tmr_stop_error(tmr_stop_set_error(0, stopped))) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, tmr_stop_set_error(0, stopped)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
                     *perr = OS_ERR_TMR_INVALID_OPT;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option != 0 && option != 3 && option != 4 &&
        data_at(perr, INT8U, 132) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, context, tmr_stop_set_error(0, stopped)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option != 0 && option != 3 && option != 4 &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(132, tmr_stop_set_error(0, stopped))) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, 3, locked) && tmr_stop_call_unlink_step(sg, i, locked, stopped) && option != 0 && option != 3 && option != 4 &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, tmr_stop_set_error(132, tmr_stop_set_error(0, stopped))) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_ready(AppRep, external, platform, critical, sg, effects, mask, error_addr, pooled, p, i, option, argument, raw_type, raw_state, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
                     break;
             }
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_ready(AppRep, external, platform, critical, sg, effects, mask, error_addr, pooled, p, i, option, argument, raw_type, raw_state, context, before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (unlock_context : OsSchedCallContext) (unlock_before : TmrStopState (TmrStopCallApplication Client)),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_prefix(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, unlock_context, unlock_before) && tmr_stop_unlock_ready(external, critical, sg, unlock_context, unlock_before) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, unlock_context, unlock_before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given unlock_context unlock_before */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_prefix(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, unlock_context, unlock_before) && tmr_stop_unlock_ready(external, critical, sg, unlock_context, unlock_before) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, unlock_context, unlock_before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_prefix(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, unlock_context, unlock_before) && tmr_stop_unlock_ready(external, critical, sg, unlock_context, unlock_before) &&
        os_sched_unlock_program_pre(external, platform, critical, sg, unlock_context, mask, tmr_stop_kernel(unlock_before), tmr_stop_call_kernel_any) * tmr_stop_client_rep(AppRep, error_addr, unlock_before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             OSSchedUnlock() /*@ where (timer_stop_unlock_spec) external=external, platform=platform, critical=critical, sg=sg, context=unlock_context, mask=mask, before=tmr_stop_kernel(unlock_before), Xk=tmr_stop_call_kernel_any */;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_running_prefix(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, unlock_context, unlock_before) && tmr_stop_unlock_ready(external, critical, sg, unlock_context, unlock_before) &&
        os_sched_unlock_program_post(external, platform, critical, sg, unlock_context, mask, tmr_stop_kernel(unlock_before), tmr_stop_call_kernel_any) * tmr_stop_client_rep(AppRep, error_addr, unlock_before) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        tmr_stop_call_post(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, 1, X) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK) *
        data_at(&ptmr, OS_TMR *, p) *
        data_at(&opt, INT8U, option) *
        data_at(&callback_arg, void *, argument) *
        data_at(&perr, INT8U *, error_addr)
    */
             OS_TRACE_TMR_STOP_EXIT(*perr);
             return (OS_TRUE);

        case OS_TMR_STATE_COMPLETED:                              /* Timer has already completed the ONE-SHOT or ...  */
        case OS_TMR_STATE_STOPPED:                                /* ... timer has not started yet.                   */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) &&
        data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, locked, p, StopStateField, status) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) && tmr_stop_unlock_ready(external, critical, sg, context, locked) &&
        os_sched_unlock_program_pre(external, platform, critical, sg, context, mask, tmr_stop_kernel(locked), tmr_stop_call_kernel_any) * tmr_stop_entry_client_rep(AppRep, error_addr, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             OSSchedUnlock() /*@ where (timer_stop_unlock_spec) external=external, platform=platform, critical=critical, sg=sg, context=context, mask=mask, before=tmr_stop_kernel(locked), Xk=tmr_stop_call_kernel_any */;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) &&
        os_sched_unlock_program_post(external, platform, critical, sg, context, mask, tmr_stop_kernel(locked), tmr_stop_call_kernel_any) * tmr_stop_entry_client_rep(AppRep, error_addr, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (returned : OsSchedCallContext) (unlocked : TmrStopState (TmrStopCallApplication Client)),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given returned unlocked */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        undef_data_at(perr, INT8U) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             *perr = OS_ERR_TMR_STOPPED;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        data_at(perr, INT8U, 142) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && tmr_stop_call_stopped_status(status) && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, tmr_stop_set_error(142, unlocked)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Assert tmr_stop_call_post(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, 1, X) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
        data_at(&ptmr, OS_TMR *, p) *
        data_at(&opt, INT8U, option) *
        data_at(&callback_arg, void *, argument) *
        data_at(&perr, INT8U *, error_addr) */
             OS_TRACE_TMR_STOP_EXIT(*perr);
             return (OS_TRUE);

        case OS_TMR_STATE_UNUSED:                                 /* Timer was not created                            */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 &&
        data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, locked, p, StopStateField, status) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 && tmr_stop_unlock_ready(external, critical, sg, context, locked) &&
        os_sched_unlock_program_pre(external, platform, critical, sg, context, mask, tmr_stop_kernel(locked), tmr_stop_call_kernel_any) * tmr_stop_entry_client_rep(AppRep, error_addr, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             OSSchedUnlock() /*@ where (timer_stop_unlock_spec) external=external, platform=platform, critical=critical, sg=sg, context=context, mask=mask, before=tmr_stop_kernel(locked), Xk=tmr_stop_call_kernel_any */;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 &&
        os_sched_unlock_program_post(external, platform, critical, sg, context, mask, tmr_stop_kernel(locked), tmr_stop_call_kernel_any) * tmr_stop_entry_client_rep(AppRep, error_addr, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (returned : OsSchedCallContext) (unlocked : TmrStopState (TmrStopCallApplication Client)),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given returned unlocked */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        undef_data_at(perr, INT8U) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             *perr = OS_ERR_TMR_INACTIVE;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        data_at(perr, INT8U, 135) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status == 0 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, tmr_stop_set_error(135, unlocked)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Assert tmr_stop_call_post(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, 0, X) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
        data_at(&ptmr, OS_TMR *, p) *
        data_at(&opt, INT8U, option) *
        data_at(&callback_arg, void *, argument) *
        data_at(&perr, INT8U *, error_addr) */
             OS_TRACE_TMR_STOP_EXIT(*perr);
             return (OS_FALSE);

        default:
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 &&
        data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_stop_call_read_rest(AppRep, external, platform, critical, sg, mask, error_addr, false, context, locked, p, StopStateField, status) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, context, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 && tmr_stop_unlock_ready(external, critical, sg, context, locked) &&
        os_sched_unlock_program_pre(external, platform, critical, sg, context, mask, tmr_stop_kernel(locked), tmr_stop_call_kernel_any) * tmr_stop_entry_client_rep(AppRep, error_addr, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             OSSchedUnlock() /*@ where (timer_stop_unlock_spec) external=external, platform=platform, critical=critical, sg=sg, context=context, mask=mask, before=tmr_stop_kernel(locked), Xk=tmr_stop_call_kernel_any */;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 &&
        os_sched_unlock_program_post(external, platform, critical, sg, context, mask, tmr_stop_kernel(locked), tmr_stop_call_kernel_any) * tmr_stop_entry_client_rep(AppRep, error_addr, locked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        exists (returned : OsSchedCallContext) (unlocked : TmrStopState (TmrStopCallApplication Client)),
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Given returned unlocked */
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_entry_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        undef_data_at(perr, INT8U) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
             *perr = OS_ERR_TMR_INVALID_STATE;
    /*@ ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        data_at(perr, INT8U, 141) * tmr_stop_call_output_frame(AppRep, external, platform, critical, sg, mask, returned, unlocked) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
        which implies
        ptmr == p && opt == option && callback_arg == argument && perr == error_addr &&
        tmr_stop_fields_layout && tmr_unlink_layout && tmr_unlink_profile(sg) &&
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSIntNesting == g_OSIntNesting(sg) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
        AppRep == tmr_stop_call_application_rep(ClientRep, pooled, p, nesting) &&
        effects == tmr_stop_call_effects(callback) && raw_type == tmr_stop_call_raw_type &&
        raw_state == tmr_stop_call_raw_state && domain == tmr_stop_call_callback_domain(critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_input_binding(sg, nesting, pooled, p, i, before) &&
        tmr_stop_call_source_facts(external, critical, sg, effects, pooled, p, i, option, argument, raw_type, raw_state, context, before, X) &&
        tmr_stop_call_callback_resources(AppRep, external, platform, critical, sg, effects, mask, error_addr, domain, pooled, p, i, option, argument, raw_type, raw_state, context, before) &&
        tmr_stop_call_state_prefix(critical, sg, effects, pooled, p, i, raw_type, raw_state, context, before, status, locked) && status != 0 && status != 1 && status != 2 && status != 3 && tmr_stop_call_unlock_step(external, critical, sg, effects, context, locked, returned, unlocked) &&
        tmr_stop_owned(AppRep, external, platform, critical, sg, mask, error_addr, returned, tmr_stop_set_error(141, unlocked)) *
        undef_data_at(&pfnct, OS_TMR_CALLBACK)
    */
    /*@ Assert tmr_stop_call_post(ClientRep, external, platform, critical, sg, callback, mask, error_addr, nesting, pooled, p, i, option, argument, context, before, 0, X) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
        data_at(&ptmr, OS_TMR *, p) *
        data_at(&opt, INT8U, option) *
        data_at(&callback_arg, void *, argument) *
        data_at(&perr, INT8U *, error_addr) */
             OS_TRACE_TMR_STOP_EXIT(*perr);
             return (OS_FALSE);
    }
}
