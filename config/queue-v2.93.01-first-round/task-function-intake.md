# Queue dependency repair and Task verification intake

User scope confirmation: 2026-09-08. Continue the remaining nine Queue functions,
repair the MutexDel/model/annotation/proof dependencies, and include Task
function verification. Existing QInit/QCreate and historical accepted proof
artifacts remain unchanged. On 2026-09-08 the user additionally authorized an
independent OS_TCBInit C-level publication repair. The
[task-atomic-publication variant](../../source_variants/task-atomic-publication/README.md)
preserves the original checkout/profile and is not yet formal acceptance.

This is an intake/design note, not acceptance evidence. No Task VC or Task
function is currently claimed controller accepted.

## Source and configuration

Reuse the pinned source and macro/architecture selection in `profile.json`,
`os_cfg.h` and `app_cfg.h`; do not switch off Task features to avoid obligations.
Task Create/CreateExt, Delete, ChangePrio, Name, Query, Suspend/Resume,
one task-register slot, stack checking and APP/CPU hooks are enabled.
Task profiling, TLS and multi-event support retain the existing disabled values.

The main shared `task.v` uses a 68-byte **verification slice**. It is not the
complete selected `Source/ucos_ii.h::OS_TCB`. Query copies sizeof(OS_TCB), and
Create/stack/name/register operations access fields outside the old slice.
Their native layout, representation and ownership must be added with an
explicit source/ABI refinement; copying the old slice is not sufficient.
No new ARM layout result is claimed: the runtime diagnostic uses host pointers.
The separate `tests/task_publication/check-layout.sh` diagnostic passed against
the selected actual header types: host preprocessing plus GCC ILP32 freestanding
layout gives size 64, alignment 4 and all 23 field offsets. Direct 32-bit header
preprocessing is unavailable without 32-bit libc headers. This limited result
exposes concrete slice/native offsets but is not an ARM ABI or QCP proof.

The [native integration delta](task-native-model-intake.md) records all selected
field offsets, source publication stages, complete free-TCB ownership, idle and
reservation domains, exact delete-request encoding, and the single-owner
integration boundary. It is design material, not new formal acceptance.

## Public function inventory

All 14 definitions below were read in pinned `Source/os_task.c`. Guards are in
source order; exact symbolic error constants must retain their selected-header
values in each future annotation. The table records source analysis, not proof.

| Function (source line) | Ordered branches and concrete effect |
|---|---|
| OSTaskChangePrio (60) | Validate old/self and new priorities; reject occupied new slot, missing/reserved old slot; move priority-table entry, ready and linked event bits, then TCB priority/coordinates; schedule if OSRunning. |
| OSTaskCreate (219) | Reject out-of-range priority, ISR, occupied slot; reserve priority, initialize stack, call OS_TCBInit; schedule on success when running; clear reservation on allocation failure. |
| OSTaskCreateExt (347) | Same ordered guards/reservation; optional stack clear, actual port stack frame, extended TCB arguments; exact success/schedule and failed-reservation rollback. |
| OSTaskDel (450) | Reject ISR, idle, invalid priority, absent/reserved target; clear ready/event/flag links; clear delay/status; scheduling-lock window and hook; decrement count, clear captured priority slot, unlink and return TCB to free list; schedule when running. Source does not free the application stack. |
| OSTaskDelReq (613) | Reject idle/invalid priority; SELF reads current DelReq; other target rejects null/reserved then stores the delete-request code. A request does not delete the task. |
| OSTaskNameGet (688) | Priority, null name-output and ISR errors precede lookup; null/reserved target errors; return the stored name pointer and OS_StrLen result, not a copied string. Writable perr is required in this safety-critical-disabled profile. |
| OSTaskNameSet (770) | Priority, null name and ISR errors precede lookup; null/reserved target errors; store the supplied pointer, not string bytes; preserve a valid name lifetime for later reads. |
| OSTaskResume (846) | Reject priority >= lowest, null/reserved target, then not-suspended; clear only SUSPEND; add ready bits only when no pending reason and delay=0; schedule only on this ready path and when running. |
| OSTaskStkChk (916) | Priority/null-output guards; zero both output fields; reject null/reserved target or disabled stack-check option; snapshot bottom/size, Restore, scan zeros without an explicit size bound; return free count and unsigned size-minus-free. |
| OSTaskSuspend (1002) | Reject idle before invalid/non-SELF priority; resolve SELF/current priority; reject null/reserved entry; clear ready bit/group and set SUSPEND; call scheduler only for self. No publication-stage or ISR-rejection guard is present. |
| OSTaskQuery (1078) | Priority/null-output guards; resolve SELF; reject null/reserved; copy the complete selected OS_TCB into caller storage under critical section. |
| OSTaskRegGet (1146) | Priority and register-index guards; resolve SELF or priority-table entry; read indexed register, then write success. Unlike Query, no null/reserved TCB guard follows lookup. |
| OSTaskRegGetID (1209) | Under critical section, return table-size sentinel plus exhaustion error when full; otherwise return old NextAvailID and increment it. Success ID 0 must not be confused with failure. |
| OSTaskRegSet (1269) | Priority and register-index guards; resolve SELF or priority-table entry; write indexed register and success. No null/reserved TCB guard follows lookup. |

Initial internal targets are OS_TCBInit (`os_core.c:2022`), OS_TaskReturn
(`os_task.c:1327`) and OS_TaskStkClr (`os_task.c:1364`). TaskReturn calls the real
return hook then Delete(SELF) in this profile; it cannot be modeled as a normal
return that preserves the original continuation. StkClr writes exactly size
elements only when both CHK and CLR options are set, in selected growth order.
OS_Sched, OSIntEnter/Exit, initialization and the port stack/context routines
remain dependencies to connect, not implicitly verified helpers.

## Consolidated semantic work

1. Publication/lifetime: retained QFlush r4 already contains conditional abstract
   counterexamples. The [source diagnostic](../../tests/task_publication/README.md)
   now reproduces Suspend and Delete effects during publication, including a
   paired ISR Suspend case and a successful ChangePrio control. A stage label or
   final ready-bit guard alone does not repair this batch.
   The separate C variant now defers index publication until the list/ready/count
   commit; 12 original and 12 repaired source scenarios passed. Preserve the
   intentional hook-lookup error changes and remaining raw-pointer hook/register
   obligations when constructing its formal model.
2. Resumption: self-Suspend, Delete/Return and Pend must identify the original
   task invocation, not merely a reused numeric TCB ID. Environment actions and
   Restore windows must match source; no endpoint-only validity filters.
3. Native Task representation: complete selected TCB layout/fields, initialized
   versus uninitialized bytes, active/free/priority membership, stack/context,
   name and register ownership. Retain module/global split-update-merge and
   cross-module closure from the LOS-derived method, not LOS opaque assumptions.
4. Stack-check scan: establish an in-bounds nonzero stopping element and stack
   lifetime/access through Restore from the actual stack/port protocol. The C
   loop is not bounded by size. This is an open obligation, not yet a proved
   end-to-end defect.
5. Register APIs: determine the legitimate caller domain and its lifetime
   protection for non-SELF lookup. Do not silently promise a missing-task error
   the implementation never returns, or quietly assume all numeric priorities
   refer to live tasks.
6. MutexDel: retain r4's event-encoding/call-contract and cache-refresh root;
   repair the actual OSMutexDel_RefreshHighReady call site with controller-owned
   regeneration. The Task diagnostics do not discharge this independent root.

## Execution order and pipeline support

Prioritize OS_TCBInit, Suspend/Resume, Create/CreateExt and Delete/ChangePrio
because their lifetime/ready protocol blocks Queue. Then connect the remaining
Task functions and finish every remaining Queue function. Shared definitions
have one formal owner; separate case specs carry complete public semantics.
Do not spawn proof workers against the known-invalid old shared model simply
to raise a local Qed count. Independent source/branch audits can still proceed.

Controller now maps all 14 public functions and the three initial internal
targets under `annotated_C/src/task/` to `VC/code_proof/task/` and its `spec/`
subdirectory, using `Ucos2Verify.VC.code.task`. This fixes the previous generic
example fallback. It creates no proof and transfers no old acceptance.
The 17 positive mapping tests failed before the change; after the change the
full controller/tooling suite passed 364 tests in 26.95 seconds. Existing
Queue/Mutex/Sem mapping and acceptance gates are unchanged.

Task annotation work still requires a controller-created case/handoff with
exact write paths. This note does not widen the already-terminal QFlush r4
input or allow editing its protected other-case files. Preserve the r4 candidate
and passing evidence for authorized reuse; do not copy it into main as accepted.
