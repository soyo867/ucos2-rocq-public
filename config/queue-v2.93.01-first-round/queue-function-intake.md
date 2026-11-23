# Remaining Queue function intake

This is source/design input, not acceptance evidence or a replacement for a
controller run. The new standalone C files are verification candidates, not
completed proofs. QInit and QCreate already have their own accepted artifacts.

The September 5 sections below describe their recorded slice-model candidates.
For the ongoing native Task/Scheduler migration, use the September 8 section
at the end; neither the old Queue candidates nor the native shared candidate
have been accepted as proofs of that combined model.

## Source and common model

- Source: `Source/os_q.c` and `Source/ucos_ii.h` at the upstream commit recorded
  in `profile.json`; the read-only checkout used for inspection is
  `/tmp/ucos2-official-audit-20260802`.
- Reuse the existing profile: argument checks enabled, eight-byte event table,
  32-bit little-endian target, four QCBs, event-name/multi-event/trace disabled,
  both safety-critical macros undefined. Expand critical macros to the existing
  save/restore interface. Do not infer the target ABI from host syntax checks.
- A queued null pointer is a message, not an empty slot. In `queue_slots_model`,
  `Some 0` and `None` have different meanings. `None` owns stale/undefined storage;
  it does not mean that C cleared the slot.
- Retain zero-capacity states supported by `queue_fields_consistency_total`.
  Derive positive capacity from a nonempty/nonfull branch, not a stronger public
  precondition. `waitList <> []` implies that the queue is empty.
- Reuse event total-type split/merge, QCB representation, ring-buffer model,
  queue binding uniqueness, and the complete kernel invariant/frame. An updated
  QCB needs separate object-fold, residual-transport and validity/cross-module
  preservation arguments. Stable ring equations need not hold between writes.
- Operations with `perr` require its writable, disjoint cell: this profile has
  no safety-critical null-`perr` guard. Do not add one to the modeled behavior.
- For task operations, the current `OS_TCB` is the established verification
  slice, not the full upstream physical layout. Preserve this explicit scope
  limitation; it is not evidence of full ABI refinement.

## Ordered branches, effects and observations

| Function | Ordered behavior | Concrete mutation and public observation |
|---|---|---|
| `OSQFlush` | null event → 4; wrong type → 1; otherwise critical reset → 0 | Set In and Out to Start, Entries to 0. No message-buffer write, waiter wake, task/scheduler update or allocation/free. Preserve all non-target fields and buffer storage. |
| `OSQQuery` | null event → 4; null output → 9; wrong type → 1; otherwise query → 0 | Copy exact group/table, then head pointer if Entries > 0 (else 0), count and capacity into caller output. Kernel state and buffer unchanged. Loop invariant relates copied prefix to source and unvisited suffix to initial output. |
| `OSQAccept` | null event → perr 4; wrong type → 1; then critical nonempty → 0, empty → 31 | Return exact head, increment Out, decrement Entries, then wrap Out; preserve tail order. Errors return null. Consumed slot is not cleared. A null head with perr 0 is success. |
| `OSQPost` | null → 4; wrong type → 1; waiter → direct wake and 0; otherwise full → 30, enqueue → 0 | Waiter path writes message to selected TCB, updates wait/ready state, restores then schedules; no ring write. Enqueue writes old In, increments In, increments Entries, then wraps In; no scheduler call. |
| `OSQPostFront` | same ordered error/waiter/full branches as Post | Waiter path is direct delivery. Ring path moves Out to End if at Start, decrements Out, stores message, increments Entries. No scheduler call on ring path. |
| `OSQPostOpt` | null → 4; wrong type → 1; waiter path tests BROADCAST; otherwise full/enqueue | BROADCAST mask is 0x01, FRONT 0x02, NO_SCHED 0x04. Unknown bits are ignored, not rejected. Broadcast delivers the same pointer to every entry waiter; otherwise one waiter. NO_SCHED only controls scheduling after wake. Back enqueue wraps In before incrementing Entries, unlike Post. |
| `OSQPendAbort` | null/type errors → return 0 and perr 4/1; no waiter → 0 and perr 0 | Only opt exactly 1 broadcasts; every other option aborts one waiter. Return exact number removed, perr 14 if at least one; restore then schedule only after a wake. Queue contents/buffer unchanged. |
| `OSQDel` | null → perr 4; wrong type → 1; ISR → 15; then option switch | NO_PEND with waiters returns original event/perr 73. ALWAYS aborts all waiters, then recycles QCB and event; scheduler call depends on the entry waiting flag. Invalid option returns original event/perr 7. Success returns null/perr 0. No message-buffer free or clearing. |
| `OSQPend` | null → perr 4; wrong type → 1; ISR → 2; scheduler locked → 13; only then inspect queue | Nonempty dequeue matches Accept, but perr is written after Restore. Empty path records PendQueue/status/timeout, waits, restores, schedules, reacquires. OK returns exact TCB message; ABORT returns null/perr 14; timeout/default removes wait membership and returns null/perr 10. Then clear status, pend status, event pointer and message. |

## Cross-module obligations before proof dispatch

1. Queue wake uses the canonical `atomic_event_task_rdy_one` with `PendQ`
   and the actual message/status. The convenience `atomic_event_task_rdy` is
   mutex-specialized and is not a Queue contract. Normal null delivery and abort
   must be distinguished by pend status, not only pointer value.
2. The bitmap-selected canonical waiter and the priority-table TCB owner are
   separate observations. Derive their equality from entry validity/history;
   never bake it into a raw helper relation to hide a propagation gap.
3. Wake does not physically write the high-ready cache pair. Carry the existing
   raw ready-priority stage until the scheduler contract permits folding full
   representation, including locked/no-schedule paths.
4. Broadcast/abort/delete loops need exact removed/remaining waiter history,
   caller locals and frame, not only decreasing list length. Derive count range
   from distinct task/priority bounds; do not silently wrap the INT8U result.
5. Pend requires a real block/resumption protocol. Entry, post-wait, scheduler
   state and reacquired current task are not interchangeable. `timeout == 0`
   permits unbounded waiting; partial correctness is not a termination claim.
   `atomic_event_task_wait_kind` combines the caller's status/timeout setup with
   wait-list and ready-list effects; it is not the standalone C helper's write
   footprint. `OS_EventTaskWait` itself writes the event pointer and event/ready
   bitmaps, not the caller's prior status, pend-status or timeout assignments.
   Also permit resumption after ALWAYS deletion: the event may already be free
   on the ABORT branch, which does not dereference it. Only timeout/default calls
   `OS_EventTaskRemove` on the original event. Do not require the queue to remain
   live on every resumed return merely to simplify a postcondition.
6. Delete restores both object free-list invariants, keeps other objects and
   message storage owned, and performs no phantom QCB reset writes. Use the
   entry waiting flag for the later scheduler branch even after wait-list drain.

The helper footprints above were checked against the selected
`OS_EventTaskRdy`, `OS_EventTaskWait` and `OS_EventTaskRemove` definitions in
`Source/os_core.c`. `OS_EventTaskRdy` returns the decoded priority despite the
upstream comment saying "none"; its call to Remove clears the selected TCB event
pointer. Preserve suspension: removing the queue-pend status bit does not by
itself make a suspended task runnable. No Queue contract may replace these
concrete effects with an unconstrained scheduling result.

For each case, expand all return/call/loop-exit requirements before VC dispatch.
Classify all current VC shapes and their guard/state/resource differences.
Collect all independent semantic gaps, then use the controller's single batch
annotation repair; do not restart symbolic execution on the first local gap.

## Front-end adaptation boundary

The upstream Query copy statement `*pdest++ = *psrc++;` is rejected by the current
QCP parser. Its candidate normalization is `*pdest = *psrc; pdest++; psrc++;`.
The annotation owner must record the original statement and justify equal old
address read/write and final pointer values in the actual disjoint, nonvolatile
critical-section context. Existing MutexQuery uses this form but does not prove
QueueQuery's equivalence. Any such normalization must preserve public input
domain, branches, calls and memory effects and remain in the annotation round;
canonical generation and proof acceptance still apply to its exact bytes.

## Initial source check

On 2026-09-05, all nine main-worktree skeletons passed a token comparison against
their pinned upstream function signatures/bodies after only the declared feature
selection, disabled trace erasure and critical-macro expansion. All nine also
passed `cc -std=c11 -Wall -Wextra -fsyntax-only`. This is an initial source check,
not an ABI check, QCP result, Rocq proof or acceptance. Later annotation-round
normalizations must be reviewed separately; this check does not cover them.

## Shared-model audit during Post design (2026-09-05)

Source comparison exposed two independent shared-model defects before Post VC
dispatch. The annotation owner is collecting fixed Rocq diagnostics and the
remaining branch obligations into one repair batch; no shared file has been
changed on the strength of these observations alone.

| Owning definition | Source discrepancy | Scope of the required repair |
|---|---|---|
| `task.v::valid_task_prio`, consumed by `task_in_range` and `task_vaild_cond_prop` | The model requires `p < osLowestPrio`, whereas pinned `ucos_ii.h` defines `OS_TASK_IDLE_PRIO = OS_LOWEST_PRIO` and `os_core.c::OS_InitTaskIdle` creates that task. Both live-task and priority-table validity currently exclude it. | L2 task/global establishment and public-domain coverage. A mathematical state satisfying the present invariant is not evidence that OS initialization establishes it. Distinguish the complete task-priority domain from narrower application/PCP argument guards. |
| `atomic_ops_lib.v::atomic_sched` and scheduler representation consumers | The switch transformer uses unbounded `ctxSwCtr + 1`; pinned `ucos_ii.h` declares `OSCtxSwCtr` as `INT32U`, and `OS_Sched` increments that unsigned object. The maximum input therefore wraps to zero in C, not to 2^32. | L5 machine-integer refinement, with L1 typed-range/preservation obligations. Do not add a no-overflow public precondition or invent a stronger case-local scheduler contract. |

The priority-domain defect affects every case claiming the complete
`UCOS2_Verify_inv`, including Flush, Query and Accept even though they do not
schedule. The counter defect additionally affects branches using scheduling.
The other branches and their proofs remain useful conditional results, but
group acceptance alone does not close these model-adequacy obligations.

Keep current proof artifacts for lawful replay; defer a complete implementation
verification claim until the shared repair and its affected dependencies have
passed their controller checks. Authorize only exact owning paths after the
whole independently inspectable repair set is known. A changed shared semantic
version requires fresh dependent evidence, not inherited acceptance. Existing
QInit/QCreate formal files and historical evidence remain untouched; their old
checks must not be reported as checks of a future repaired model.

Post/Pend's independent source audits subsequently expanded this same batch:

- `event.v::mutex_fields_consistency` also excludes owner priority equal to
  the lowest priority, while the pinned mutex acquire path stores the current
  priority without that extra guard. This is a consumer of the task-domain
  repair, not permission to widen the separately checked PCP argument domain.
- `sched_in_range_preserved_by_sched_switch` in `mutex_func_sem.v` repeats the
  old counter expression in a theorem premise; it must follow the canonical
  scheduler correction rather than silently retain a different transformer.
- `sched.v` ties the full invariant's high-ready cache to the ready-list head.
  C Wait/wake operations change ready bitmaps without writing those cache
  globals, and locked/ISR scheduling can return without refreshing them. The
  existing raw/history predicates alone do not supply a public cross-API
  boundary and recovery interface. Do not invent cache writes to fold full
  representation; repair the scheduler/global boundary and its consumers.
- `OSTimeTick` clears the pending status bits on timeout while retaining the
  event bitmap membership and TCB backlink until cleanup. In contrast,
  `event_wait_entry_consistency` requires every listed task to still have a
  pending type. Model the timeout-before-cleanup phase and its legal wake/remove
  races, with a real task/ready timeout transition; the clock-only
  `atomic_tick_advance` cannot establish it.
- `task.v::encode_event_ptr` maps `Some eid` to the integer ID, whereas C Wait
  stores `pevent`, whose pool address is `event_addr sg eid`. In particular,
  ID zero is not a null event pointer. Correct the shared representation using
  one address owner available below task/event's import dependency; do not
  assume ID/address equality in a function-specific annotation. Multi-event
  execution remains outside the selected profile.

These entries record source-level discrepancies and repair scope, not a claim
that the shared repair has been implemented or accepted. The Post/Pend owners'
terminal reports must retain their actual diagnostic scope and any additional
independent findings before exact shared write paths are authorized.

## Consolidated shared repair batch (2026-09-05)

Post and Pend completed their independent pre-generation audits and passing
local case-lib checks. Both terminal reports remain blocked, with canonical
generation explicitly not run. Their findings are consolidated below; this
design note is not proof or controller acceptance evidence.

| Root cause ID | Shared repair and required source-facing interface |
|---|---|
| `PEND-L2-IDLE-DOMAIN` | Admit the real idle/live-task and saved-owner priority domain; keep application/PCP guards separate. Include Post's owner-payload consumer in `event.v` and its preservation theorem in `mutex_func_sem.v`. |
| `PEND-L1-EVENT-POINTER-ENCODING` | One slot-address owner below task/event; encode optional event references using the pool address, with source-valid non-nullness and injectivity. |
| `PEND-L4-TIMEOUT-PROTOCOL` | Distinguish active pending from expired-but-linked waiters. Preserve backlink/lifetime/uniqueness and suspension facts through timeout, wake/abort and unlink. |
| `PEND-L5-TICK-EXPIRATION` | Separate UInt clock wrap from ghost time; supply the precise task-expiration step and frame. Respect the enabled hook, OSRunning and tick-step gates and actual traversal up to idle, not an unconditional all-task countdown. |
| `PEND-L5-UINT-SCHEDULER-COUNTER` | Correct the canonical UInt switch increment and its direct preservation consumers without a no-wrap public precondition. |
| `PEND-L5-WAIT-FOOTPRINT-AND-RAW-CACHES` | Factor caller status/delay stores from the standalone Wait helper. Compose physical-cache history with logical readiness at a shared public boundary; Post's ISR/locked/no-schedule returns must re-enter later Queue APIs through that boundary. |
| `PEND-L5-RESUMPTION-AND-LIFETIME` | Bind a genuinely resumed call to its original task and local frame using source-backed labelled environment/schedule steps. OK preserves the delivered message, ABORT permits a freed/reused old slot without dereference, timeout requires the linked event for Remove. |
| `PEND-L3-QUEUE-RESOURCE-COMPOSITION` | Publish QCB and buffer ownership into the shared critical invariant, not a private frame across waiting. Reuse the existing Queue substate/ring model; prove focus, original/updated merge, binding uniqueness and exact physical-buffer frame. |

The last item is a shared composition issue, not merely a missing arithmetic
lemma: the current global/full/raw predicates own ECBs but not QCBs or message
buffers. A case-local resource wrapper for a nonblocking operation does not
establish the ownership transfer needed by Pend and concurrent Delete.

Main independently identified two additional direct consumers for the same
batch: `sem_pend_spec.v:2944-2950` explicitly applies the old optional pointer
encoder, and `mutex_post_spec.v:3124-3154` derives an unconditional active pend
type/non-ready fact from waiter membership. Migrate those dependencies as
required by the corrected shared definitions; do not retain a false statement
or restrict Queue behavior to keep an old proof passing. Old downstream checks
remain evidence only for their recorded model versions.

Use a new, precisely authorized annotation retry from Flush's accepted
annotation baseline to implement this batch and restore a complete source-valid
Flush contract. All Flush groups are terminal and their proof text is archived.
Keep Post/Pend case-local files isolated; this note and the pinned source supply
shared design context, not permission to import another run's case-lib proofs.
The controller handoff alone grants exact write paths. Check changed shared
owners/consumers with fixed tooling as well as the case-lib; a passing Flush
case-lib check alone does not cover an unimported changed consumer.

QInit/QCreate formal files stay unchanged. Preserve the declared TCB-slice,
disabled multi-event and external architecture refinement boundaries. Do not
claim termination, freeze the environment, erase unrelated global invariants,
or assume a post-invariant in place of proving operation preservation.

## In-flight shared-repair review (2026-09-05)

These notes concern the `q_flush-annotation-r4` candidate, not an accepted or
main-applied model. They refine the existing root causes without opening a
second repair batch or changing any handoff permission.

- `PEND-L5-TICK-EXPIRATION` / `PEND-L5-RESUMPTION-AND-LIFETIME`: pinned
  `os_core.c:990-992` clears the pending bits on the actual expiration step.
  The old Sem/Mutex resume observers returned pending-bit values 1/16 on
  timeout, and the old timeout relations retained the pending status. Update
  the observation consumers together with the real expiration relation;
  merely renaming that old relation an internal slice would not fix it.
  A one-tick mutation is still not a complete call-resumption execution.
- `PEND-L3-QUEUE-RESOURCE-COMPOSITION`: the old `q_flush_world` separates
  `UCOS2_Verify_inv` from an additional `q_flush_queue_storage`. Once the
  shared invariant owns QCBs and buffers, retaining that wrapper would own
  the same writable cells twice and make a successful-call precondition
  unsatisfiable. Extract the focused writable cells and readonly `R` from
  the global Queue resource, preserve a real residual, and merge the updated
  object back. Updating only the `QueueState` projection is insufficient.

For final shared-library checks, the r4 candidate's updated explicit import
graph covers all 22 writable owners through four upper-level targets:
`mutex_create_spec`, `mutex_del_spec`, `mutex_post_spec`, and `sem_pend_spec`
(all under `uC-OS2_verify/lib`, with `.v` suffix). The latter two now include
`sem_create_spec`, `sem_del_spec`, `sem_pend_abort_spec`, and `sem_post_spec`
through `mutex_func_sem`; those four Sem libraries need not also be compiled
as separate top-level targets when the final fixed evidence already covers
their exact updated sources. `mutex_post_spec` additionally covers
`mutex_annotation_slices` and `mutex_rdyatprio_spec`.
This is only a check-planning hint: after final edits,
confirm coverage using the fixed tooling's actual dependency evidence, check
the Flush case-lib as well, and add any uncovered or subsequently changed
consumer. It is not permission to reuse an obsolete passing check or to skip
the controller's acceptance checks.

### Task publication window relevant to Pend interference

For `PEND-L5-RESUMPTION-AND-LIFETIME`, pinned `os_core.c:2120-2135`
publishes the initialized TCB in `OSTCBPrioTbl`, restores interrupts, calls
`OSTaskCreateHook`, and only then re-enters the critical section to link it
into `OSTCBList`. The Create wrappers reserve the priority first
(`os_task.c:249-254,382-392`), but do not hold a scheduler lock across this
window. Distinguish traversal-safe linked tasks from allocated/table-visible
tasks; coverage of every allocated task by the tick chain does not yet hold.

The priority-based Query, Suspend, Resume and ChangePrio implementations
(`os_task.c:1102-1112,1032-1046,861-875,100-166`) do not test a publication
phase. Delete rejects ISR context (`469-470`), but its task-context path
(`487-548`) does not test that phase either. DelReq (`647-656`) only sets a
request flag; it does not cancel the in-progress creation. Final publication
(`os_core.c:2136-2144`) writes the links and unconditionally inserts the
TCB's then-current priority bits into the ready bitmap.

The selected configuration enables application/CPU hooks. The selected port's
`Ports/ARM-Cortex-A/ARMv7-A/os_cpu_c.c:146-153` calls `App_TaskCreateHook`
directly; its comment that interrupts are disabled cannot replace the actual
caller's Restore. Any restriction on accesses to an in-flight task therefore
needs an explicit source-backed calling/resource protocol or a declared
external refinement boundary, not an invented API guard. These are source
audit findings, not a proof of a reachable implementation bug or permission
to restrict the environment silently.

### Relocation encoding versus a stale scheduler cache

Pinned `os_mutex.c:293-297` documents an `OS_DEL_ALWAYS` calling assumption:
the owner is ready-to-run and is not pending on another object or delayed.
`OSMutex_RdyAtPrio` (`787-812`) updates TCB priority, ready bits, priority-table
and current-priority cells, but never Event wait bits. Tick expiration
(`os_core.c:990-1001`) can make a waiter ready before `OSQPend` removes its
Event membership (`os_q.c:511`). Do not derive an unlinked waiter or equality
of old/new Event encodings merely from readiness or post-state validity.
The documented calling protocol and its precise relation to this intermediate
state remain distinct from a source guard or an established preservation proof.

The r4 candidate consequently separates `UCOS2_raw_high_ready_cache_stage`
(Event encoding already uses the post Task view) from
`UCOS2_raw_ready_prio_stage` (Event bits still use the entry Task view).
Their transport requires `event_raw_encoding_agrees`; moving Sem wake
consumers to the first shape does not resolve MutexDel's missing transport.
This records the existing shared root cause and source footprint, not a new
public precondition, accepted proof, or end-to-end implementation-bug claim.

## First Queue batch against the native Task candidate (2026-09-08)

This is one consolidated continuation of the existing resource-composition and
resumption findings, not a new verification round. The inspected frozen shared
candidate is `task_tcb_init-20260908111228/task_tcb_init-annotation-r2`, under
`worktrees/`; its `queue_core.v` is also unchanged in r3 at this inspection.
The comparison targets are Flush annotation r4 in `q_flush-20260905101125`, and
Query/Accept annotation r2 in `q_query-20260905101753` and
`q_accept-20260905102531`. These are design references, not permission to import
another run's proof text or inherit its acceptance. The r3 owner was the
only shared Coq writer at the time of that audit. The current continuation is
Task annotation r4; follow the live controller/owner rather than the historical
round label, and do not modify its shared files from a Queue worker.

### One state and one owner for each Queue cell

The native candidate's `ucos2_verify_state_def.v` stores the logical QueueFields
in each event and exact ring snapshots in `EventState.publishedQueueBytes`.
Its top-level state has no `QueueState` projection. The independent QueueState
and `replace_QueueS` used by the old Flush r4 candidate therefore cannot simply
be carried into this candidate. Reuse the logical ring transformers, but adapt
their state update to the actual canonical event owner; do not introduce a
second authoritative queue map solely to keep old spec text compiling.

`UCOS2_native_inv` already includes `native_queue_storage_rep`. That predicate
owns the published QCB/buffer map and the whole free-QCB list. Query's old
`q_query_extra` and Accept's old `q_accept_payload` separately own the same
selected QCB/buffer; appending them to the full native invariant would duplicate
writable cells. Flush r4 already separates its non-Queue factor from a focused
Queue factor, but both factors refer to its older, different state model.

The shared interface required by all three functions is:

1. Focus a readable event, including the free/wrong-type cases. Only the actual
   successful type branch produces the queue lookup, qid, range and binding.
2. From the native global ownership, split the selected QCB/buffer and retain
   a structural residual containing all other queues, the free list and the
   non-Queue modules. Keep event-to-qid uniqueness and the selected physical
   snapshot alongside the spatial cells, rather than expecting ownership to
   imply those facts.
3. Provide original-value merge for Query/error reads and a distinct
   updated-value merge for Flush/Accept. Prove the new ring validity, event
   payload/binding validity, residual transport and native cross-module facts
   before folding the full invariant. Do not assume the desired post-invariant.

Representation/focus belongs in `queue_core.v` and `event.v`; the full-global
composition belongs in `ucos2_verify_inv.v` and its cross-module owner. The
ordered operations and caller-output predicates remain in the corresponding
`VC/code_proof/queue/spec` files. `native_queue_storage_task_sched_frame` only
covers Task/Scheduler replacement; it is not the missing Queue updated-merge.

### Logical removal is not a physical buffer write

`native_queue_slots_model` constrains occupied slots but retains initialized
values outside the FIFO. By contrast, `queue_slots_model` labels every
unoccupied slot `None`. For example, after accepting the only message from a
two-slot queue with snapshot `[Some p; None]`, C leaves that same snapshot in
memory although the logical queue is now empty. The unchanged snapshot meets
the native model, not the old empty-queue model with the same slot list. An
undefined-cell assertion can forget a value, but that is not an equality of
physical snapshots and is not evidence that C cleared the cell.

| Operation | Protected logical effect | Protected physical effect to preserve |
|---|---|---|
| Flush | In = Out = 0, messages = [] | Write only QCB In/Out/Entries; keep `publishedQueueBytes`, buffer ownership and all untouched QCB fields. No message-object free and no waiter change. |
| Query | No queue/event/task/scheduler update | Preserve the selected QCB and exact slots. Initialize only the caller's five output components: group, eight table bytes, head-or-null, count and size. |
| Accept | Remove one FIFO head, advance/wrap Out, decrement count | Keep In and all buffer cells, including the consumed slot; update only Out/Entries and the caller's `perr`. Empty/error paths retain the appropriate state and output ordering. |

Prove native slot preservation using `queue_flush_state` and
`queue_dequeue_front`; retain zero capacity and `Some 0` success. Existing ring
arithmetic and `queue_binding_unique_update_same_binding` are reusable
interfaces, not evidence that the native merges already exist. If an untouched
QCB field such as OSQPtr must retain a caller-selected exact value, carry its
read-only refinement through the focused stage; the canonical live-QCB undef
cell does not invent an initial value.

### Query bitmap observation and the call boundary

Native event rows use `encode_event_wait_tbl_at_or`; old Query output uses
`encode_event_wait_tbl_values`, whose rows use the older sum encoder. The
existing `encode_event_wait_tbl_at_eq_or` supplies a bridge only with NoDup,
priority uniqueness and the required ranges. Obtain these from the current
native validity, or use the canonical OR snapshot directly. Also expose the
eight native row cells as the actual byte-array slice consumed by the copy
loop; a type/array-length assertion alone does not establish output contents.

The old Query's `q_query_acquired_identity` is mathematically justified by its
explicitly state-preserving `interrupt_saved_cpu_sr` contract. That contract is
still present as a legacy interface in the native candidate. Neither the lemma
nor the saved scalar token proves that the native platform implements an
identity transition across the complete call interval.

Distinguish invocation entry, the pre-Save type read, the acquired protected
state, the protected operation endpoint and the resumed return state. For
Query, the output describes the protected read snapshot, even if an allowed
interrupt changes the queue after Restore. Likewise Flush/Accept's own effects
are exact at their protected endpoint, not an assertion that the environment
did nothing before return. The source/lifetime protocol must justify use of the
handle between the unprotected type check and acquisition. Do not invent a
source recheck, globally frozen environment or endpoint-valid filter.

The focused source audit makes this lifetime obligation concrete. In pinned
`os_q.c`, Accept reads type at 94, enters at 98 and loads the QCB at 99;
Flush uses 385/389/390 and Query uses 897/900/907. A task can pass the type
check and then be preempted by a task deleting that queue with NO_PEND.
The first task is not a pending waiter, so `OSQDel`'s wait-bitmap test does not
exclude this interleaving. The delete path at 288-305 frees the QCB and writes
the old `OSEventFreeList` into the event pointer. If that old head is NULL,
the resumed first-batch call obtains a NULL QCB and dereferences it; immediate
Create can instead reuse the same addresses for a different allocation.

The inspected Delete notes at 222-236 warn about handles, return checks and
application-owned buffer release/reuse, but do not establish an in-flight
nonblocking-call borrowing protocol. Updating a shared handle to NULL does
not update the preempted caller's already copied argument. Old entry validity,
state-indexed snapshots and state-preserving Save contracts do not establish
this native lifetime guarantee.

The required interface therefore distinguishes a stable allocation/ECB-QCB
binding and buffer lifetime from mutable contents: retain a valid borrow from
the successful type observation through the final protected access, but read
ring/waiter contents afresh at acquisition. The user has now approved using an
explicit caller/delete/reuse lifetime protocol for these six functions; see
the subsequent decisions in [the shared intake](task-native-model-intake.md#subsequent-source-and-queue-domain-decisions).
The application must establish the borrow, and the formal interfaces must
transport it; the original kernel does not enforce it automatically. This
selects conditional verification of unchanged Queue implementations, not an
implementation repair or unconditional safety under arbitrary deletion.
Null/output-null/observed-wrong-type branches remain, message payload ownership
is not acquired by this borrow, and deletion after the last protected access
need not be forbidden.

All three call Save/Restore but none calls `OS_Sched` directly. Their local ring,
output, localization and native-merge work can be completed independently of
Post's direct-wake/scheduler proofs. Whole-call native verification still needs
the shared, source-backed critical/resumption interface; a selected FPU/BSP
implementation must not be silently assumed. Preserve the earlier Query
post-increment normalization boundary and all ordered error paths.

The user has now approved explicit external-platform contracts without an
ARM/BSP implementation-proof claim; see the confirmed boundary in
[task-native-model-intake.md](task-native-model-intake.md). Queue continuation
must consume the resulting shared C-level interface, not reopen that user
choice or require a full platform proof before the first batch. Actual Queue
handle lifetime, protected snapshots and native resource merges remain its
own obligations; this confirmation does not declare them proved.

### Next dispatch and evidence scope

Keep the existing archive and QInit/QCreate deliverables unchanged. Once the
single shared owner has supplied and checked the affected native interfaces,
prepare each first-batch case against that exact shared version. Triage every
return/call/loop-exit and all generated targets, merge common missing atoms,
and perform the necessary canonical generation and controller checks. Do not
recompile old, unchanged proofs while these source/model interfaces remain
unsettled; old candidate Qed or old controller acceptance is not acceptance of
the native migration.

## Second Queue batch: shared native consumers (2026-09-08)

The read-only Post/PostFront/PostOpt audit confirms the ordered branches in the
table above and adds the following consumers of the same native repair. It did
not start a new run, change C/Coq files or recompile old proofs.

- **Native direct wake must preserve the physical cache.** The frozen Task r2
  `atomic_event_task_rdy_one` still normalizes high-ready fields; its own comment
  requires a legacy raw representation to distinguish that normalization from
  physical bytes. Reuse/factor its Task/Event update, but compose native wake
  with `native_sched_set_ready` so it keeps the actual entry caches, current
  selection and counter. This matters on NO_SCHED, ISR and lock-gated returns.
  Queue arguments are `PendQ`, `Some pmsg`, `PendOK`; `Some 0` is delivery, not
  abort. Prove native preservation from the real source steps, not by folding
  the legacy normalized state into the full native representation.
- **Wake changes Event but frames Queue storage.** The helper writes Dly, Msg,
  the Queue pending bit and StatPend, conditionally ORs ready bits, then Remove
  clears the Event row/group and TCB backlink. It writes no QCB/buffer, priority
  table or high-ready cell. A storage transport for the same live eid with
  unchanged QueueFields and published bytes is required: the existing
  Task/Scheduler-only frame lemma does not cover the changed Event waitList.
  Preserve both active and expired-but-linked waiters. Suspended waiters still
  receive/unlink without becoming ready; an already ready expired waiter makes
  the ready OR idempotent. The source mask only clears bit 0x04, so use the
  linked-phase premise to justify the abstract pending-type update.
- **Ring insertion updates logical contents and physical snapshot together.**
  After `queue_enqueue_back/front`, update the selected qid's bytes with
  `replace_Znth i (Some pmsg) slots`; i is old In for back, or
  `queue_retreat_index size oldOut` for front. `update_event_field_raw` alone
  preserves all old published bytes and is insufficient. A one-slot empty
  queue with stale value 7, followed by Post 9, demonstrates the mismatch:
  logical contents [9] cannot share the unchanged snapshot [Some 7]. Reuse the
  first batch's native focus/updated merge and ordinary mixed-array split/merge.
  The nonfull branch establishes positive capacity and bounded Entries + 1;
  do not add a positive-capacity public precondition.
- **Selection is a source-read bridge.** Use the real OSUnMapTbl, two nonzero
  Event bitmap reads, native priority table and priority-derived TCB fields to
  prove canonical waiter = actual table owner in the same protected snapshot.
  The relational helper's equations are not proof of those C reads. Its common
  bit-selection math should be shared with Scheduler, without a dependency
  from the shared layer into a function spec. The native linked-phase predicate
  still reuses `event_waitList_canonical` and its strict `< osLowestPrio` domain;
  reconcile this with the actual idle/caller protocol before a full-domain
  claim rather than inventing a Post guard or silently widening it.
- **Options and broadcast retain history.** Unknown option bits are ignored;
  FRONT does not change waiter selection, BROADCAST does not duplicate a ring
  enqueue, and NO_SCHED only suppresses the post-wake scheduler call. The
  broadcast loop has no intervening Restore/Sched. Track the entry waiter list
  as delivered prefix plus remaining suffix, same message, exact removals and
  Queue bytes frame. After Restore, retain delivery/publication history, not
  an unsupported claim that every TCB message or the live queue is unchanged
  at function return. Apply the common resumption boundary to the subsequent
  OS_Sched call as well.

For source normalization, `*pq->OSQIn++ = pmsg` performs the slot write and In
update before the next complete expression, but does not prescribe their
relative order within that expression. Prove any chosen split using their
disjoint cells. Post increments Entries before the following wrap check;
PostOpt's back arm wraps before the common Entries increment. Do not merge
these distinct intermediate annotation stages just because final queues agree.

### Shared lifetime-window delta for the second batch

The first batch's type-check-to-Save gap also gates every protected branch of
Post, PostFront and PostOpt. In the pinned `Source/os_q.c`:

| Function | Type check / Save / first protected read | Affected successors |
|---|---|---|
| Post | 658 / 662 / 663 | direct wake, full return, back enqueue |
| PostFront | 730 / 734 / 735 | direct wake, full return, front enqueue |
| PostOpt | 811 / 815 / 816 | single/broadcast wake, full return, front/back enqueue |

The first protected read is already `OSEventGrp`; the issue is not limited to
the later QCB dereference. One source-permitted interleaving is: A passes the
old Queue's type check; higher-priority B deletes its then-empty wait set with
NO_PEND (`:299-305`), recreates a Queue at the free-list heads (`:158`, `:165`,
`:175-177`) and pends on it (`:491-496`); A resumes and wakes B on the new
allocation instead of posting to the old object. Broadcast has the same
identity problem. NO_SCHED is checked after Restore (`:824-826`) and cannot
protect this earlier interval.

Use the same approved lifetime/borrow protocol as the first batch, not a
second per-function assumption: retain the allocation identity through the
last protected access, but acquire fresh mutable contents and waiter state.
Null and observed-wrong-type returns stay in the public contract; a type read
requires a readable ECB, not an assumption that every non-NULL input is a live
Queue. Keep the existing ring, single-wake/selection, broadcast and scheduling
proof groups; their local protected-state producers can progress independently
while whole-call composition depends on the common lifetime bridge. The
source audit itself is not a protocol proof; the subsequent user decision
selects the caller constraint but does not verify every application caller.
No Queue C repair, recompilation or reacceptance of old Queue proofs follows
from this note. Bind the chosen protocol through the next appropriate
controller handoff without rewriting frozen earlier contracts.
