/* Annotation-only carrier of pinned V2.93.01 Source/os_core.c.
 * The input is replayed over the real jointly enabled Multi/Names/Profile
 * headers. The contract covers every ordered public branch, not just live
 * objects. It is a conditional C/VC contract: the source/CPU/CSL environment
 * handoff at unmasked boundaries is not proved by an ordinary spatial frame.
 */
void  OSEventNameSet (OS_EVENT  *pevent,
                      INT8U     *pname,
                      INT8U     *perr)
/*@ With (platform: InterruptPlatformResources) (invocation: nat)
         (origin: TaskInvocationOrigin) (mask: Z) (frame: Assertion)
         (nesting type_byte name_old error_old: Z)
    Require perr != 0 && 0 <= nesting && nesting <= 255 &&
      data_at(perr, INT8U, error_old) * data_at(&OSIntNesting, INT8U, nesting) *
      interrupt_platform_running(platform, invocation, origin, mask) * frame *
      event_name_set_access(pevent, pname, &pevent->OSEventType,
        &pevent->OSEventName, nesting, type_byte, name_old)
    Ensure exists (error: Z),
      coq_prop(event_name_set_observation(pevent, pname, nesting, type_byte, error)) &&
      data_at(perr, INT8U, error) * data_at(&OSIntNesting, INT8U, nesting) *
      interrupt_platform_running(platform, invocation, origin, mask) * frame *
      event_name_set_access(pevent, pname, &pevent->OSEventType,
        &pevent->OSEventName, nesting, type_byte,
        event_name_set_final_name(pevent, pname, nesting, type_byte, name_old))
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR  cpu_sr = 0u;
#endif
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return;
    }
#endif
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {
        *perr = OS_ERR_PEVENT_NULL;
        return;
    }
    if (pname == (INT8U *)0) {
        *perr = OS_ERR_PNAME_NULL;
        return;
    }
#endif
    if (OSIntNesting > 0u) {
        *perr = OS_ERR_NAME_SET_ISR;
        return;
    }
    /*@ pevent != 0 && pname != 0 && nesting <= 0 &&
        event_name_set_access(pevent, pname, &pevent->OSEventType,
          &pevent->OSEventName, nesting, type_byte, name_old)
        which implies
        pevent != 0 && pname != 0 && nesting <= 0 &&
        data_at(&pevent->OSEventType, INT8U, type_byte) *
        event_name_set_after_type(&pevent->OSEventName, type_byte, name_old)
    */
    switch (pevent->OSEventType) {
        case OS_EVENT_TYPE_SEM:
        case OS_EVENT_TYPE_MUTEX:
        case OS_EVENT_TYPE_MBOX:
        case OS_EVENT_TYPE_Q:
             break;
        default:
             *perr = OS_ERR_EVENT_TYPE;
             return;
    }
    /*@ 1 <= type_byte && type_byte <= 4 &&
        event_name_set_after_type(&pevent->OSEventName, type_byte, name_old)
        which implies
        coq_prop(event_name_type_supported(type_byte)) &&
        data_at(&pevent->OSEventName, INT8U *, name_old)
    */
    OS_ENTER_CRITICAL();
    pevent->OSEventName = pname;
    OS_EXIT_CRITICAL();
    OS_TRACE_EVENT_NAME_SET(pevent, pname);
    *perr = OS_ERR_NONE;
}
