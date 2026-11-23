/* Annotation-only carrier for pinned V2.93.01 with native joint-profile headers.
 * This is a conditional C/VC contract. Ordinary framed cells do not discharge
 * the unmasked source/CPU/CSL environment handoff. A returned pointer is not a
 * permanent lifetime grant; only the actual StrLen call borrows its bytes. */
INT8U OSEventNameGet (OS_EVENT *pevent, INT8U **pname, INT8U *perr)
/*@ With (platform: InterruptPlatformResources) (invocation: nat)
         (origin: TaskInvocationOrigin) (mask: Z) (frame: Assertion)
         (names: NameResourceState) (chars: list Z)
         (nesting type_byte name output_old error_old: Z)
    Require perr != 0 && 0 <= nesting && nesting <= 255 &&
      coq_prop(event_name_get_request(names, pevent, pname, nesting,
        type_byte, name, chars)) &&
      data_at(perr, INT8U, error_old) * data_at(&OSIntNesting, INT8U, nesting) *
      interrupt_platform_running(platform, invocation, origin, mask) * frame *
      event_name_get_access(pevent, pname, &pevent->OSEventType,
        &pevent->OSEventName, name, nesting, type_byte, output_old, chars)
    Ensure exists (error: Z),
      coq_prop(event_name_get_observation(names, pevent, pname, nesting,
        type_byte, name, chars, error, __return,
        event_name_get_output(pevent, pname, nesting, type_byte, name))) &&
      data_at(perr, INT8U, error) * data_at(&OSIntNesting, INT8U, nesting) *
      interrupt_platform_running(platform, invocation, origin, mask) * frame *
      event_name_get_access(pevent, pname, &pevent->OSEventType,
        &pevent->OSEventName, name, nesting, type_byte,
        event_name_get_final_output(pevent, pname, nesting, type_byte, name, output_old), chars)
*/
{
    INT8U      len;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (0u);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {               /* Is 'pevent' a NULL pointer?                        */
        *perr = OS_ERR_PEVENT_NULL;
        return (0u);
    }
    if (pname == (INT8U **)0) {                   /* Is 'pname' a NULL pointer?                         */
        *perr = OS_ERR_PNAME_NULL;
        return (0u);
    }
#endif
    if (OSIntNesting > 0u) {                     /* See if trying to call from an ISR                  */
        *perr  = OS_ERR_NAME_GET_ISR;
        return (0u);
    }
    /*@ pevent != 0 && pname != 0 && nesting <= 0 &&
        event_name_get_access(pevent, pname, &pevent->OSEventType,
          &pevent->OSEventName, name, nesting, type_byte, output_old, chars)
        which implies
        pevent != 0 && pname != 0 && nesting <= 0 &&
        data_at(&pevent->OSEventType, INT8U, type_byte) *
        event_name_get_after_type(&pevent->OSEventName, pname, name,
          type_byte, output_old, chars)
    */
    switch (pevent->OSEventType) {
        case OS_EVENT_TYPE_SEM:
        case OS_EVENT_TYPE_MUTEX:
        case OS_EVENT_TYPE_MBOX:
        case OS_EVENT_TYPE_Q:
             break;

        default:
             *perr = OS_ERR_EVENT_TYPE;
             return (0u);
    }
    /*@ pevent != 0 && pname != 0 && nesting <= 0 &&
        1 <= type_byte && type_byte <= 4 &&
        coq_prop(event_name_get_request(names, pevent, pname, nesting,
          type_byte, name, chars)) &&
        event_name_get_after_type(&pevent->OSEventName, pname, name,
          type_byte, output_old, chars)
        which implies
        coq_prop(event_name_get_readable(names, name, chars)) &&
        data_at(&pevent->OSEventName, INT8U *, name) *
        data_at(pname, INT8U *, output_old) *
        event_name_get_name_bytes(name, chars)
    */
    OS_ENTER_CRITICAL();
    *pname = pevent->OSEventName;
    len    = OS_StrLen(*pname) /*@ where (name_get_spec) entry = name, names = names, chars = chars, frame = frame */;
    OS_EXIT_CRITICAL();
    *perr  = OS_ERR_NONE;
    return (len);
}
#endif
