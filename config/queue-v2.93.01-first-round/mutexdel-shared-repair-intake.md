# MutexDel dependency repair for the remaining Queue functions

## Latest scope extension (2026-09-09)

The user now requests complete Coq model support for **all uC/OS-II modules**
before the eventual all-function verification. Follow the
[whole-kernel foundation intake](../ucos2-v2.93.01-model-foundation.md).
The Task/Queue/Mutex batch below remains useful source evidence but no longer
defines the entire shared-model convergence scope. Preserve its frozen reports;
do not treat its ten-file additive-native request as authority for new module
files, global-record changes, or all-kernel acceptance. Finish live isolated
checks, converge the whole model, then migrate affected existing proofs.

This is the problem statement for a new controller-owned MutexDel repair run,
not acceptance evidence. User scope includes repairing MutexDel's shared
models, annotations and proofs, verifying Task functions, and completing the
current two Queue batches: OSQFlush/OSQQuery/OSQAccept, then
OSQPost/OSQPostFront/OSQPostOpt. The other intake files are not additional
functions in this active goal. Preserve existing main proofs and original
source/profile until a new final candidate is accepted and applied.

Current authorization update (2026-09-09): the user subsequently said
"允许修复" and has now requested migration of all previously completed
function proofs to the new Coq model. The earlier lack of approval for an
independent additional Mutex C repair is resolved. Preserve the original and
existing scalar-only variant; bind any new repair explicitly in a fresh
source-versioned run. This current intake update does not widen the frozen
`del_full-20260908090121` annotation r2 handoff or turn its blocked result into
acceptance. The later design-comparison text describes authorization at the
time of that comparison, not a renewed permission question.

The separately named [nested-priority candidate](../../source_variants/mutex-nested-priority/README.md)
now has an implementation patch and source-level regressions. It uses bounded
priority-table alias scans, records masked Pend demands, releases only the
selected ceiling and preserves ready membership when restoring a suspended
owner. The existing C/Coq formal targets are not changed or accepted by this
diagnostic candidate. Its README records the exact algorithm, whole-family
alias/lifetime obligations and the remaining waiting-task-priority-change
boundary; consume it through a fresh source-bound run, not this frozen r2.

### Current-model convergence before the remaining migrations

The 2026-09-09 continuation must use a fresh run initialized from current main.
The old `del_full-20260908090121` reports describe an earlier shared snapshot;
neither their path requests nor their partial repairs are current acceptance.
The newly applied native Task model already supplies creation lifetimes,
published Queue bytes, native ready encoders and physical cache observations.
Do not rebuild those features from the older repair proposal below.

The immediate annotation-owner task is a **pre-generation source/model audit**
for the already authorized nested-priority repair. Keep the initial target C,
case spec and shared formal files unchanged while identifying the exact
remaining shared write batch. Do not generate or compile the known-mismatched
old Delete candidate just to demonstrate the documented mismatch again.
Report all independent remaining causes and the minimal actual owner/consumer
paths in the existing terminal shared-repair request, using the controller's
pre-generation continuation contract. Main then authorizes the exact batch
and creates the repair attempt; this audit is not proof completion.

The repair candidate must bind the approved nested-priority source, not the
original or scalar-only algorithm. In the subsequent authorized repair attempt,
source migration includes the native 64-byte TCB interface and the exact
selected Delete implementation, with any verification naming/projection
differences made explicit. Preserve all ordered public errors, output writes,
NO_PEND/ALWAYS behavior and the stronger safety purpose of the repair. Do not
silently keep the 68-byte verification slice and call it native, or choose a
one-held-Mutex restriction instead of implementing the approved alias repair.
The two temporary read-only scan/relocation proof workspaces are not canonical
dependencies: use only their final applied implementation/specification once
accepted, with an explicit source/dependency binding. Until then, their current
reports are progress pointers, not callee proof authority.

Current audit priorities, all against the same source/model candidate:

- Replace the per-Mutex saved/current-priority equality with the permanent-slot
  and enabled-PCP alias relations described below; derive the scan results and
  preserve each source-ordered release/relocation/handover stage.
- Retain creator reservations, generation/invocation identity, idle priority
  63, active and expired-but-linked waiters, suspended owners and exact physical
  high-ready/current-cache observations. Do not add native TCB fields merely
  to remember facts already represented by the actual table and lifecycle.
- Check the real Task publication, priority-change, suspend/resume and deletion
  producers/consumers, and Queue publication, ring updates, wake/resumption and
  reclamation requirements before deciding whether a public state/interface
  must change. This is a shared-model requirements audit, not a claim that all
  those new C APIs have already been proved or must be proved in this run.
- Inspect both named relation users and proofs that destruct the full validity
  bundle. In current main these include Mutex Create/Post/Delete/relocation,
  Sem Create/Delete/Pend/Post and the native Task publication proofs. Also
  distinguish untouched frame consumers from actual writes; imports alone are
  not authorization to edit every sibling spec.
- Keep the accepted external platform/hook choice. Its parameterized client
  certificates still require source-backed instances and continuation/lifetime
  preservation; do not assume identity interference or demand an ARM/BSP proof
  that the selected claim explicitly excludes.

Finish already running isolated proof checks and retain their versioned results.
Do not launch the remaining bulk proof migrations against an intermediate
cross-module invariant solely to increase a completion count. Converge and
check the shared owner/consumer candidate first, then refresh/replay affected
cases against its final applied dependencies. Prefer additive proved interfaces
over repeated record/contract changes, but never weaken a needed invariant to
avoid its preservation obligations. Existing results remain evidence for their
bound versions, not automatic acceptance of the future shared candidate.

### Next native priority-relation interface

The read-only consumer audit below is a design requirement for the separately
bound nested-priority variant, not an added assumption, accepted theorem or
write authorization for an existing handoff. The helper run proves literal
table scans and relocation; it cannot establish these global facts by itself.

- Characterize a live task's permanent slot by its real `PTTask tid` entry and
  absence of any live enabled Mutex PCP claim at that index. Establish existence
  and uniqueness from Task publication and preserve them through each lifecycle
  producer; do not infer them from `task_current_prio_registered`, which only
  describes the current slot. This is a proposed relational interface, not a
  reason to add another native TCB field or fabricate a second Task state.
- Every other table alias for that task must belong to a live enabled Mutex
  owned by that same task and be numerically below its permanent priority.
  Current priority is the minimum actual alias; the permanent priority is then
  the maximum. The maximum/minimum helper interpretation must be proved from
  these facts, including why the literal no-match fallback is unreachable for
  a valid owner. Use `native_priority_index`, whose domain includes the idle
  priority, not legacy `valid_task_prio`, which excludes `osLowestPrio`.
- Keep acquisition/handover `mfOwnerOrigPrio` as Query's actual observation;
  it is neither a permanent-slot certificate nor the new release target.
  In particular, the existing `priotbl_consistency` reserved-slot clause and
  `mutex_owner_consistency` per-Mutex current-priority equality cannot justify
  nested releases. Existing `mutex_task_priority_alias_claim` also admits saved
  acquisition values, so it is not the required enabled-PCP alias relation.
- A qualifying Pend records an alias even when another Mutex already gives a
  stronger boost. Post/Delete release exactly their selected alias before the
  remaining-alias scan. Between those literal writes and relocation, use an
  explicit transient representation; do not pretend the full minimum-priority
  relation holds after every individual C store. Timeout alone does not release
  a latched alias. Ready membership and current/noncurrent scalar behavior
  remain separate source obligations.
- Retain native creator reservations and their invocation/lifetime ledger.
  Prove that their sentinel slots, live enabled Mutex PCPs and permanent task
  slots are disjoint. Audit TaskCreate/TCBInit publication, TaskChangePrio and
  TaskDelete as producers/consumers rather than treating a free-looking
  projection of a creator reservation as a physical free slot.

The owning unit is the Task/table representation and native lifecycle in
`task.v`, Mutex claims/transformers in `mutex.v` and `atomic_ops_lib.v`,
cross-module relations in `cross_module_invariants.v`, and their full/raw
composition in `ucos2_verify_inv.v`; Event wait encoding and scheduler frames
must be transported through their existing owners. The public Mutex specs and
all affected Sem/Queue/Task preservation proofs are downstream consumers.
Determine the exact writable file set in one controller-authorized batch before
formal edits. Do not overwrite the current Sem/Queue dependency snapshots,
remove unrelated invariants, strengthen public callers just to obtain closure,
or reuse the old per-Mutex acceptance for this new native relation.

## Target and source scope

Target `uC-OS2_verify/annotated_C/src/mutex/OSMutexDel_full.c`, including its
FirstSet8 and RefreshHighReady helpers. The target currently uses an explicit
verification TCB slice, not the full native OS_TCB. Keep this limitation visible;
do not silently identify the slice with the native layout. The original
executable token stream is fixed in this run: authorized repairs are annotation,
case spec and controller-authorized shared `.v` owners. Report any required
additional executable change with its exact source counterexample instead of
silently making it.

The original source/configuration context is pinned in the neighboring
`profile.json`; actual source checkout is
`/tmp/ucos2-official-audit-20260802`. Read the actual os_mutex.c, os_task.c and
os_core.c paths relevant to the mutation or caller protocol. The new
`uC-OS2_verify/source_variants/task-atomic-publication/` patch is separately
authorized and source-tested, but not a formal premise or a changed MutexDel
implementation. Do not import its test result as a lifecycle proof.

The user has since confirmed the documented Mutex owner-use protocol and
explicit external-platform contracts without an ARM/BSP implementation-proof
claim; the current Task r4 retry records that instruction. See
[the confirmed boundary](task-native-model-intake.md#confirmed-verification-boundary-2026-09-08).
This resolves the earlier choice of supported-use domain, not the actual
encoding/cache proofs. Keep the owner-not-pend/client-priority obligations
distinct from the ready-owner precondition at `OS_DEL_ALWAYS`; the latter is
not a global assertion that every owner is always ready. No new MutexDel C
change or old-proof acceptance follows from the scope confirmation.

## Current evidence and reusable source

The terminal QFlush repair candidate is at
`worktrees/q_flush-20260905101125/q_flush-annotation-r4/`.
Its report and reuse note are at
`reports/q_flush-20260905101125/rounds/q_flush-annotation-r4/`.
These paths are read-only references, never accepted input for this new run.
Do not edit their frozen files or transfer acceptance. Relevant candidate
text may inform a fresh derivation inside the new run's explicit write bounds.
Any carried mathematical statement must be checked against actual source and
current dependencies; only the controller may authorize shared writes or adopt
a candidate.

The QFlush candidate contains substantial Event address/encoding, Task/Sched
raw-stage and physical-cache, Tick/expired-wait, and global Queue ownership
repairs. Its fixed checks cover 21 of 22 authorized shared owners; the distinct
MutexDel check fails. Old main proofs passing against old shared definitions
do not settle this new repair task, so do not recompile them merely for status.

## Concrete root to repair

`R4-RAW-RELOCATION-ENCODING-AND-CACHE-CALLSITE`:

- The earlier QFlush r4 candidate's `UCOS2_raw_ready_prio_stage sg entry post` owns Event bitmap bytes
  encoded using `entry.TskState`, although Task/ready state already uses `post`.
- Existing `mutex_del_raw_stage_refresh_expose__g02_refresh_close` and
  `mutex_del_refresh_residual sg post` silently require Event encoding at `post`.
- Canonical transport is conditional on actual per-waiter encoding agreement.
  The current RefreshHighReady contract/callers do not establish that premise.
- The cache refresh must produce the actual updated physical high-ready cache,
  not just reuse an abstract endpoint or equate cache with logical selection.
- Delete's source Note 4 is a real caller-usage note; it does not by itself prove
  that a ready owner has no expired-but-still-linked event wait membership.
  Inspect the real timeout, wait cleanup, relocation and wake paths before
  claiming a source protocol or an implementation defect.

Inspect all uses and producers, not only the first failing helper. Prefer
source-correct mixed-index residuals and exact stage transport over adding an
assumption shaped like the failed VC. Raw behavior and full-invariant recovery
can be separate theorems, but the full public contract and frame must not be
weakened or replaced with unconstrained endpoints to claim success.

Current-candidate correction: in the Task r5 bytes inspected on 2026-09-09,
`UCOS2_raw_ready_prio_stage` and `mutex_del_refresh_residual` both use the
post-Task Event index. Do not repair that historical mismatch a second time.
The remaining transport obligation is earlier: `OSMutex_RdyAtPrio_raw_stage`
retains entry-indexed Event ownership, whereas
`OSMutex_RdyAtPrio_literal_stage` requires the post index. Its old
`debug_ready_tid_not_event_wait__relocation_semantics` producer assumes the
active-only wait relation. Establish native owner absence from both active and
expired-but-linked wait lists at this producer, then consume
`event_wait_priority_agreement` and the existing encoding bridge. If an
intermediate native stage intentionally keeps a mixed index, carry that index
explicitly until this transport, rather than adding only a refresh-call premise.

## Source audit: encoding and cache consumers

The independent read-only audit of the Task r2 shared candidate identified the
following concrete connections. These are repair obligations/proposals, not
checked lemmas or a terminal judgment on that still-changing candidate. A
single shared owner must integrate them; this note adds no writable paths.

For Event bytes, carry an explicit `encoding_tasks` through relocation and
refresh residuals until a transport theorem justifies changing the index.
The direct consumers are `mutex_del_refresh_residual`,
`mutex_del_raw_stage_refresh_expose__g02_refresh_close`, and the raw-to-full
recovery in `mutex_del_spec.v`. The minimal reusable producer is agreement of
`option_map curPrio (inUsedTaskStates tasks tid)` for every member of every
surviving Event wait list. Both bitmap encoders depend on this priority
observation, not complete TCB equality. Updating the old task-list head's Prev
field, for example, must not invalidate an otherwise valid encoding frame.

For a single priority relocation, prove that the changed owner is absent from
all surviving wait lists, or that its priority did not change. Absence from
the selected mutex's list is not sufficient. The existing
`debug_ready_tid_not_event_wait__relocation_semantics` uses the old active-only
wait relation: a native timeout can make a task ready while retaining its
Event link. A widened-domain trace (owner priority 20 boosted to 5, pending on
another Event, timed out without unlinking, then restored to 20 by Delete)
leaves the other Event's bit 5 unchanged. This trace violates the documented
owner-not-pend-other-event usage rule; it is not evidence of a C bug under
documented use. Any exclusion used for the public theorem needs the actual
source protocol/history argument. An ordinary expired waiter whose priority
does not change is a separate case and remains wakeable at its recorded bit.

For the high-ready cache, keep scalar and pointer writes separate from logical
ready-list changes. The existing verification `RefreshHighReady` already
performs both writes; this audit does not request another NO_PEND C repair.
Connect its residual, expose lemma, postcondition and full recovery to the
actual two stores. A logical-head theorem alone does not justify the pointer
loaded from the priority table: establish the bitmap decode and the table
lookup at that stage, without assuming the old physical cache is correct.

The pinned `OS_Sched` writes neither cache component when interrupt or scheduler
lock nesting prevents scheduling. With both nesting counters zero, it writes
the high-ready priority and then pointer even when no context switch occurs.
Therefore the enabled/no-switch branch of `atomic_sched` must preserve current
task/counter while allowing that real cache refresh, not require identity of
the entire old state. Preserve the profile distinction when reusing pure
record updates: native empty priority encodes as 0 and TCB addresses use 64-byte
stride; the historical verification slice uses 255 and 68-byte stride.

### Remaining current-priority counterexample under documented use

The confirmed owner-use protocol excludes the earlier other-event timeout
trajectory, but does not exclude a different task deleting the mutex. In the
pinned source, `os_mutex.c:387` calls `OSMutex_RdyAtPrio`, whose `:800` writes
`OSPrioCur = prio` unconditionally, even if `ptcb != OSTCBCur`.

A concrete source-level scenario is: O at original priority 20 owns M with
PCP 5; W at priority 10 waits on M, promoting O to 5; D at priority 2 runs,
locks scheduling and deletes M with ALWAYS. O is ready and never waits on
another event, and no client changes O's priority. The helper restores O to
20 but also sets `OSPrioCur` to 20 while `OSTCBCur` still denotes D at 2.
The subsequent scheduler call is gated by the lock. Refreshing the high-ready
cache does not repair the current-priority scalar.

The subsequent real-source Delete/wake/scheduler diagnostic additionally
reproduced two distinct paths. With no initial waiters, ALWAYS omits
`OS_Sched`, so even an unlocked return retains the original mismatch. With
initial waiters and scheduling enabled, the corrupted comparison requests a
spurious same-task context switch and increments the switch counter. The
conditional helper patch avoids those observations in the targeted fixtures.
Suspended and expired-but-still-linked waiters retain the source's distinct
ready-set behavior and NULL-message/abort writes. See the variant diagnostic
for the exact platform-stub and specified-state limits; these checks do not
replace the callee or scheduler proof.

Frozen Task r3 `atomic_ops_lib.v` contains
`atomic_task_set_curPrio_ready_owner_literal_exec_noncurrent_breaks_sched_current_consistency`
for the raw helper consequence. The source scenario supplies its noncurrent
premises; it is not an ARM/BSP assumption or a reason to reinstate the already
resolved user-choice blocker. The existing main `OSMutexDel_full.c:660` only
declares this helper with a contract and no body, so its caller proof must not
be described as a proof of the upstream helper implementation.

The minimal repair for this scalar defect is to update `OSPrioCur` only when
`ptcb == OSTCBCur`, preserving the other relocation writes. The main-tree
`annotated_C/src/mutex/OSMutex_RdyAtPrio_full.c:351-356` already contains that
conditional, under the separate `_full` function name and verification-slice
representation. Do not add the same repair again or equate the differently
bound implementations. Binding that existing repair to the pinned native
helper has now been selected with the user's approval. The separate
[native source patch and targeted diagnostic](../../source_variants/mutex-current-priority/README.md)
preserve the pinned original and reproduce/fix this specific scalar defect.
An exact callee-contract bridge, new controller source binding and affected
proof still remain; the source test does not supply them. Independent TCBInit
work can continue without treating the unrepaired original action as valid or
silently changing the current frozen handoff's executable source.

The pinned source narrows the repair's caller analysis. The ceiling rule in
`os_mutex.c:156-159` refers to tasks competing for the mutex, not every task in
the system; the deleting task D need not acquire M. The Delete contract at
`:285-295` requires a ready owner in ALWAYS, but does not require the caller to
be that owner, and the guards at `:331-349` do not reject scheduler locking.
`os_core.c:1711-1712` then gates scheduling on both nesting counters. This is
why the documented owner protocol does not eliminate the example above.

The static helper has two call sites in this source: Delete passes the event's
owner at `os_mutex.c:387`, while Post first checks ownership at `:669-672` and
passes `OSTCBCur` itself at `:677`. Thus the proposed condition preserves the
original Post helper path and the self-owner Delete path, and changes only the
noncurrent-owner scalar write. This is source-level impact analysis, not a
completed C proof. The eventual check must still cover both current/noncurrent
cases, unchanged Event wait bytes, exact ready-row/table updates, and the
independent high-ready refresh; it must not replace the helper by a broader
priority-change operation that also rewrites another Event's wait bitmap.

### Independent cases retained in the same repair batch

The source audit also distinguishes these obligations from the scalar fix;
none is discharged merely by adopting the conditional assignment above.

- The repaired NO_PEND caller also invokes the ready-at-priority helper
  (`OSMutexDel_full.c:1179`). The upstream ALWAYS ready-owner note is not a
  ready-owner premise for that added path. Suspending an inherited owner and
  allowing the last waiter to timeout and finish unlinking can leave a
  suspended owner with an empty wait list. Preserve this case when deriving
  the NO_PEND repair's effects; do not silently make every owner globally
  ready or change its executable body under annotation-only authority.
- The candidate `atomic_mutex_release_with_handover` still inserts its waiter
  into the ready list unconditionally and preserves the old message. Native
  MutexPost instead calls the EventTaskRdy path with a NULL message, which
  respects suspension and may encounter an already-ready expired-but-linked
  waiter. Reuse the exact wake producer, then compose the Mutex owner/count
  writes; a broad normalized high-ready state is not the physical cache.
- No-link ownership does not imply the current `mutex_task_restore_safe`
  relation for every other held Mutex. Nonblocking Accept permits O20 to own
  M1/PCP5 and M2/PCP3; W10 waiting on M1 can promote O to5 without making O a
  waiter. A per-Mutex invariant demanding the owner priority be only that
  Mutex's saved original or ceiling priority would reject the M2 state.
  This is a model/protocol obligation, not a source check that already exists.
  The current Task handoff lists `mutex.v` read-only; any necessary change
  must be requested with the consolidated owner/consumer repair scope.
- The same nested-owner example also invalidates the `PTReserved` clause of
  `priotbl_consistency`, reused by `native_priotbl_consistency`: a different
  held mutex can change the owner's current priority while this mutex's PCP
  remains reserved. Native owner and priority-table relations must be repaired
  together; changing only `mutex_owner_consistency` leaves the false premise.
  The low-byte saved priority is an acquisition-time observation, not an
  immutable task base priority or a proof that its table slot remains owned.
  The source's restoration helper overwrites the destination slot, so prove
  actual slot ownership from an established source/lifecycle protocol before
  claiming full-invariant recovery. A ghost reservation alone cannot make the
  real TaskCreate guard reject a physically free priority slot.
- Keep the following additional source-derived sequence in the same inventory:
  O20 inherits M1/PCP5, then Accepts M2/PCP3 with saved priority 5; another
  task deletes M1, restoring O20 and freeing slot 5; Create may now use slot 5;
  W4 pending on M2 promotes O to 3; O's Post of M2 restores 5 and overwrites
  the new task's table entry. The relevant source stores are `os_mutex.c`
  Accept's saved-current write, ALWAYS's PCP release and RdyAtPrio's destination
  write; `os_task.c` Create tests only the physical table slot for availability.
  The source-derived sequence was reproduced by the independent host API
  diagnostic described below; it is not an ARM or Rocq proof. It is distinct
  from the overstrong owner relation and from the
  current-scalar repair. Do not claim a general native restore-preservation
  theorem until its actual slot-lifetime premise has a valid implementation or
  explicitly selected caller protocol; do not invent one-held-mutex usage.
  A follow-up guard audit found no API guard or selected owner-use condition
  excluding this sequence. A concrete diagnostic must nevertheless preserve
  real task continuations: the existing `tests/mutex_current_priority/`
  `del_scheduler.c` fixture only supports the priority-2 same-task switch.
  Merely changing `OSTCBCur` and returning from another task's Pend would be
  an invalid execution, not evidence of this bug.

  The independent `tests/mutex_current_priority/nested_restore.c` fixture uses actual Create/Suspend/Resume and
  Mutex APIs with separate host task stacks. D2 creates M1/PCP5, M2/PCP3,
  O20 and W10, suspends W10, then itself. O accepts M1 and resumes W10;
  W10 pends M1, promoting O to 5. O resumes its original Resume call,
  accepts M2 (saving 5), and resumes D2. D2 deletes M1 ALWAYS, creates N5
  and W4, and suspends itself. W4 pends M2, promoting O from 20 to 3.
  O resumes its original Resume-D2 call and posts M2; W4 resumes its own
  Pend and observes the collision. Pend calls require unlocked, non-ISR
  context; O remains ready and never pends or calls TaskChangePrio. The
  expected results are both Accepts TRUE/NONE, Delete NULL/NONE, both
  Creates NONE, W4 Pend NONE and eventually W10 Pend PEND_ABORT.

  Before Post, assert `table[5]=N`, `O.prio=3`, `M2.saved=5`; afterward
  assert O and N are distinct active TCBs with priority 5 and `table[5]=O`.
  No fixture write may manufacture priority-table, ready or Event wait
  changes. Use the approved conditional-current Mutex variant and the real
  TaskCreate/OS_TCBInit chain; disclose host stack/context/CPU-status and
  initialization stubs. On 2026-09-09, the separate `run_nested.sh` reproduced
  the collision under host UBSan (exit 0, nine task switches, no sanitizer
  diagnostic), also checking both Pend returns and the owner's Post return.
  Startup uses actual static initialization helpers and API-created tasks,
  not the complete configured OSInit path. The original 24 cases were not
  rerun. This is not an ARM or Rocq proof and does not authorize an additional
  implementation patch.
- Task deletion has a separate resource-release usage requirement. Its source
  does not test for Mutex ownership or clear all Mutex owner references.
  Preserve that explicit lifecycle interface rather than inventing a TaskDel
  guard or deriving it from the owner-not-pend rule.

### Read-only comparison of additional implementation repairs

The 2026-09-09 source comparison did not implement or execute either candidate
repair below. The existing collision diagnostic and the subsequent Post-only
inheritance diagnostic described below exercise the scalar-only variant,
not either proposed nested repair.

- **Retain referenced priority slots:** keeping slot 5 non-NULL blocks the
  demonstrated TaskCreate reuse (`os_task.c:249`), but leaves `M2.saved=5` and
  hence the later restoration to an already released PCP. It does not justify
  leftover aliases after the last release, or a PCP subsequently used by a new
  owner through Post/handover (`os_mutex.c:674-703`). This is not a complete fix.
- **Propagate restoration references on release:** before destroying or
  replacing the old ownership, replace other held Mutex restore references
  to the released PCP with its restore value. This must cover successful
  Post and both successful Delete paths, including non-LIFO release when
  `owner.curPrio != released_pcp`; it cannot be conditional on actually
  executing the current-priority restore. Preserve no-change error paths,
  but remember that `OS_ERR_PCP_LOWER` can follow acquisition or handover.
  Disabled PCP 255 is not a table index or an executable restoration edge.

Propagation still does not establish full nested priority inheritance. A
separate trace, **now reproduced by the Post-only host diagnostic**, starts with O20 accepting M1/5
and M2/3 before either has a waiter, so both saved fields equal 20. W10 then
promotes O to 5 through M1, and W4 promotes O to 3 through M2. Post M2 restores
20; M1.saved is not 3, so propagation changes nothing, although M1's waiter
still calls for inherited priority 5. The relevant stores/guards are
`os_mutex.c:126-138,532-579,674-703`. This distinguishes a remaining inheritance
property from the executed table-overwrite bug: slot 20 still belongs to O,
so this trace alone is not evidence of a second memory/table overwrite.

The command `bash uC-OS2_verify/tests/mutex_current_priority/run_nested.sh
--post-only` completed on 2026-09-09 with exit 0 under host UBSan, nine real
scheduler-selected task switches and no sanitizer diagnostic. It contains no
Delete call and releases M2 before M1 (LIFO). After W4's Pend returns, the
fixture checks O ready at 20, M1 still owned by O, and W10 still linked and
pending on M1. W4 releases M2 and suspends; a ready priority-15 task then runs
before O can resume its original Post-M2 call. Both waiting tasks ultimately
return from their original Pend calls with `OS_ERR_NONE`, and O's first Post
returns `OS_ERR_NONE`. The owner never blocks on another Event or calls
TaskChangePrio. All scheduler, Task and Event mutations come from actual
kernel APIs; startup and host platform boundaries are the same as the earlier
fixture. This confirms an independent observable inheritance failure of the
current source variant, not a completed repair or a formal/ARM proof. The
default Delete/Post scenario and previous 24 tests were not rerun.

A complete design must separate owner base priority, acquisition observation,
mutable restoration target, outstanding inheritance demands and table-alias
lifetimes. It must not pretend the existing C computes the minimum of every
held PCP. A pool-scanning implementation would also need exact cross-Event
read/write frames and exclusion of free/partially initialized Events; review
MutexCreate's post-critical initialization (`os_mutex.c:243`) explicitly.
Changing saved fields changes the value exposed by Query (`os_mutex.c:753`),
so its observation contract must be selected, not silently treated as equal.
NO_PEND restoration must preserve suspended/non-ready owners; TaskChangePrio
and TaskDelete remain source-bound lifecycle consumers. No additional C patch
or public-contract change is authorized by this design comparison.

For the source-preserving Event-encoding/current-priority portion, keep one
shared writer for the following owner/consumer unit:
native owner/table relations in `cross_module_invariants.v`; backlink/no-link
and priority-observation transport in `event_wait.v` and `event.v`; the literal
current/noncurrent producer in `atomic_ops_lib.v`, `mutex_rdyatprio_spec.v` and
`mutex_func_sem.v`; stage/refresh/full-recovery consumers in `mutex_del_spec.v`
and `ucos2_verify_inv.v`. Preserve the old legacy relations and the current
read-only `mutex.v`. Acquisition snapshots must come from the actual
Accept/Pend/handover updates, and current priority must follow actual writes,
not an invented minimum-of-all-held-PCPs rule. Concrete source certificates
remain distinct from the TCBInit parameterized client theorem.

For the originally requested Event encoding repair, the useful producer is
owner absence from all live Event wait lists plus unchanged priorities for
other waiters. Consume it through `event_wait_priority_agreement`, its encoder
bridge and the actual raw-representation index transport. An ordinary
expired-but-linked waiter remains valid; do not restore the false implication
that every ready task is unlinked.

## Related source/lifecycle batch

`R4-SOURCE-RESUMPTION-LIFECYCLE-CLOSURE` remains independent: phase-labelled
traces need actual source parameter/state connections, complete action coverage,
the pre-scheduler Restore window, original invocation/lifetime identity,
Tick list establishment and endpoint derivation. The Task publication patch
removes tested indexed-but-unlinked interleavings only. Raw-pointer hooks,
unguarded task register APIs, native representation and full Create/scheduler
refinement remain explicit obligations. Do not hide them with validity filters
or no-op hook assumptions.

## Work and authority

Within each current handoff, finish all independent analysis and permissible
repairs in the same annotation attempt. Keep the ordered public return/branch
matrix, mutation footprint, missing-atom producers and exact downstream
consumers together. If shared files must change, return the complete minimal
set of writable owner/consumer `.v` paths and read-only dependencies with
source-backed reasons; do not stop at the first missing file. The initial
handoff does not authorize shared writes merely because this statement
identifies a known dependency.

Do not spend a full canonical proof cycle on the known-invalid old shared model.
Use focused fixed debugging for concrete new case-spec facts when useful;
report existing evidence as reference, not newly executed evidence. Controller
will authorize the exact repair batch and run canonical generation only once
the candidate's semantic premises are coherent. Generated files are never
hand-edited. Collect all independent semantic gaps before requesting retry.

Use the current LOS-derived split/update/merge and source-refinement method,
not LOS opaque/Admitted assumptions. Avoid unnecessary hashes, verbose copies
of this statement, repeated full dependency checks, or new parallel acceptance
layers. Complete proof acceptance still belongs to current controller evidence.
