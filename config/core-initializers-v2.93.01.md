# Core initializer source and composition scope

Chinese milestone records and writing summaries are maintained in
[internal-function verification progress](../docs/case_briefs/internal_function_verification_progress.md).

This batch follows the selected uC/OS-II V2.93.01 source at
`/tmp/ucos2-official-audit-20260802/Source/`, with the release binding already
recorded in `queue-v2.93.01-first-round/profile.json`. It is not a new BSP
implementation proof or a rewrite of that historical profile.

The three main intake slices were compared with the selected preprocessed
upstream function tokens on 2026-09-13 using the existing source-check token
helpers. All three comparisons passed, including the TCB declaration and
scalar aliases. GCC `-m32` syntax/layout diagnostics also confirmed eight
ready bytes, 20/200-byte ECB/node pool and 64/1408-byte TCB/node pool with a
256-byte priority table. These are source/layout diagnostics, not QCP/Rocq
acceptance or a proof of the ARM/BSP implementation. Final candidates still
need their own source boundary checks.

## OS_InitRdyList

The implementation is `os_core.c:1434`; declarations and the ready-table size
come from `ucos_ii.h`. The existing `OS_LOWEST_PRIO = 63` selection makes
`OS_PRIO` an unsigned byte and `OS_RDY_TBL_SIZE` eight. The standalone slice
retains the executable body and its write order, including internal linkage.
The incomplete `OS_TCB` declaration claims no TCB layout.

The function takes no arguments, returns no value and makes no calls. It writes
zero to `OSRdyGrp`, each of the eight `OSRdyTbl` rows, `OSPrioCur`, and
`OSPrioHighRdy`, then null to `OSTCBHighRdy` and `OSTCBCur`. The only loop writes
rows in increasing index order. No TCB object, priority lookup table, counter,
running flag, interrupt state, or other module resource is read or changed.

The contract should consume ownership of exactly those writable cells/array
and return their exact zero values, with an arbitrary disjoint caller frame.
Addresses in `StableGlobVars` must be tied to the actual C globals wherever
that model is used. Use the existing `UCOS2_C_Rules` Assertion instance and
QCP byte-array split/merge rules, not a duplicate array library. An initializer
must not assume an already valid running Task/Scheduler invariant.

`sched.v` already encodes absent priority selections as zero in
`sched_priority_byte` and defines `sched_boot`. A local postcondition can be
combined with the unchanged zero counter/false running cells to establish
`sched_raw_rep ... sched_boot`. Those extra cells come from `OS_InitMisc`,
which precedes this function in `OSInit`; they are not writes or unconditional
postconditions of `OS_InitRdyList`. `sched_boot_in_range` additionally needs an
empty used-task map. `OS_InitTCBList` runs afterwards, so that premise must be
supplied at composition time, not invented at this function's entry.

The current shared model is read-only for this function's annotation owner.
Its actual import closure is registered with the controller at intake. New
function-specific contracts/helpers belong in
`VC/code_proof/sched/spec/init_rdy_list_spec.v`. Any genuine model gap is
reported at its owning layer and batched with independent gaps.

## MemClr callers: outstanding address-bound obligation

The checked general `OS_MemClr` contract requires the address *after* all byte
increments to remain representable. `kernel_region_valid` permits a half-open
region ending at the address-space boundary; byte ownership alone proves the
last accessed byte exists, not that the subsequent pointer increment is
representable in the current QCP model. The Queue typed/byte view candidates
preserve alignment but do not discharge that additional address condition.

Before claiming the old QInit specialized clear contract is implemented by the
newly verified general function, establish the missing premise from a genuine
caller/platform allocation contract or handle it as a semantic contract gap.
Do not silently strengthen an old public Require, invent a concrete linker
address, or alter MemClr's last increment. Audit the same issue for TCB/Event
pool initialization together; it does not block the independent InitRdyList
proof, which does not call MemClr.

## OS_InitTCBList

`os_core.c:1591` clears the TCB pool and priority table, installs each next
link and the enabled default task name, terminates the final link, then writes
the used-list null root and publishes the free-list root. The selected source
has 20 application plus two system slots, a 64-byte TCB, 64 pointer entries,
and task names enabled. Thus the two clear lengths are 1408 and 256 bytes and
fit `INT16U`; the 21-iteration loop and final index fit `INT8U`.

The zero image, free images and abstract boot state already exist in `task.v`
and `task_storage.v`; use `tcb_init_free_image`, `task_boot_storage` and
`task_boot`, not a second TCB record. The actual C also clears padding and
the ready-flags field. Preserve all nonlink/nonname zero observations and
the string resource frame. This function does not initialize `OSTaskCtr` or
the task-register allocator; those belong to the preceding `OS_InitMisc`.
Only combine their unchanged zero cells at the boot-state consequence.

This is a new initialization contract, not a change to old TCBInit/Queue
public input domains. Its entry must explicitly cover writable pool/priority
bytes and the two roots, selected alignment/field-layout bindings, and the
representable final address for **both** MemClr calls. Call the exact proved
generic MemClr byte contract, or prove both sides of any specialized
consequence. A declaration returning a typed zero image is not itself that
proof. No startup-ready/global-running invariant may be assumed.

## OS_InitEventList

`os_core.c:1336` has a clear-and-link branch for more than one event, a distinct
single-event branch without clearing, and a disabled branch. This run selects
the existing ten-event, names-disabled profile: it clears 200 bytes, writes
UNUSED type and each next pointer, terminates the final pointer, then publishes
`OSEventFreeList`. It does not initialize Queue storage or publish live IPC
objects. Do not claim the same zero-field postcondition for the unselected
single-event branch, which never calls MemClr.

Use the existing `event_storage_rep`, `event_boot_image`,
`event_pool_initial`, pool partition and free-storage validity lemmas.
The case postcondition should retain all ten linked ECBs with exact zero
nonlink fields/padding and the published free root; unrelated globals and
Queue resources remain frames. Consume an explicit source-operation end
address bound and alignment/layout facts for the 200-byte MemClr call.
No new shared model or admission is authorized merely to make a byte-view
conversion succeed. Collect any genuine representation/call-contract gaps
with the independent TCB/Queue instances.

Run `init_event_list-20260913012101` is now `done`: all seven manual targets,
controller group/parent checks, final apply and final-check passed. The
main result links the actual generic MemClr call to ten complete 20-byte
ECBs and their free root; it does not claim Queue initialization or a running
global invariant. Twelve canonical auto admissions remain within the existing
tool trust boundary, not additional assumption-free kernel proofs. The
accepted executable tokens and static linkage match upstream. Complete ECB
declarations match after explicitly folding the selected table extent to
eight and resolving INT8U in the OS_PRIO alias; no live formal file was edited
to normalize this spelling.

## Preceding scalar initialization: OS_InitMisc

`os_core.c:1389` is the actual source of the unchanged zero cells needed by
the Ready/TCB boot consequences above. The selected time/statistics/register
configuration performs eleven zero stores in source order: OSTime,
OSIntNesting, OSLockNesting, OSTaskCtr, OSRunning, OSCtxSwCtr, OSIdleCtr,
OSIdleCtrRun, OSIdleCtrMax, OSStatRdy, and OSTaskRegNextAvailID. OSTime and
OSIdleCtr retain their actual volatile RAM declarations. The proof context
is serialized startup ownership, not an assumption of an already valid
running kernel or a proof that interrupts are physically masked.

It does not touch the ready table, TCB/ECB/Queue pools, CPUUsage, timer clock,
platform registers or system stacks. Consequently it cannot by itself
establish any whole running-module invariant. Run `init_misc-20260913032206`
is `done`: canonical QCP, fixed case-lib/interface checks, the unique manual
return proof, controller independent group/parent checks, final apply and
final-check passed. Both volatile declarations were retained. Its exact
eleven-cell postcondition and ten registered read-only dependencies supply
the genuine Task/Scheduler scalar frames for the completed InitRdyList and
InitTCBList consequences. Statistics cells are preserved in the result
without assuming unwritten OSCPUUsage is zero. There are no canonical auto
admissions in this particular case; it still does not prove whole OSInit.

## Next dependency frontier: waiting and waking

The selected source bodies at `os_core.c:1078`, `:1156` and `:1237` have been
read and placed in module-local standalone intake files for the next batch.
On 2026-09-13 all three matched the preprocessed upstream function tokens,
complete TCB/ECB declarations and six scalar aliases. GCC ILP32 diagnostics
also confirmed the 64/20-byte layouts and the exact event-pointer/bitmap
offsets. The first comparison caught a differently spelled but equal array
extent; the intakes now retain the upstream macro expression as well.
These checks are source correspondence, not completed function proofs.

The selected `os_cfg.h` has `OS_TRACE_EN = 0`, and the upstream `os_trace.h`
supplies empty `OS_TRACE_TASK_READY` / `OS_TRACE_TASK_SUSPENDED` defaults.
The Wait/Rdy slices bind those defaults explicitly; custom tracing is not
silently treated as an empty call. EventMulti remains disabled, with Queue
and Mbox enabled, so Rdy really does store its message argument.

- `OS_EventTaskRemove` removes the task bit, conditionally clears the group
  bit when the row becomes zero, then clears the TCB event pointer. It does
  not clear delay/status or make the task ready. Existing
  `event_clear_waiter_from_image` and field updated-merge interfaces match this
  footprint; full waiter-list/model consequences are a separate layer.
- `OS_EventTaskWait` links the current TCB to the event, inserts its event
  bits and removes its ready bits. Its caller prepares pending status/delay;
  this helper does not write those fields. Preserve current-task identity and
  use the existing insertion/removal transformers with a transient call state.
- `OS_EventTaskRdy` chooses a waiter with `OSUnMapTbl`, looks it up in
  `OSTCBPrioTbl`, clears delay, writes message/status/result, updates ready
  bits only when not suspended, calls Remove and **returns the priority**.
  The source comment says “Returns: none”, but the executable return controls
  the contract. Preserve the selected waiter/table-entry identity through
  the intermediate writes, and the exact status-mask/message/result effects.
  Existing `task_event_wake_before_remove` and `task_event_wake_single`
  explicitly separate the before/after-Remove stages. Multi-wait is disabled
  in this selected profile and must not be silently claimed as covered.

The callers supply the protected/shared ownership and waiter/ready relations;
these functions do not acquire a lock themselves. Do not equate a local byte
update or representation reconstruction with restoration of the entire kernel
invariant. Remove is a genuine dependency of Rdy, while Wait can be prepared
independently under the same stable model version.

For Remove, the low-level contract must permit the status/delay/message state
that Rdy has already written. It must not demand `task_linked_wait_phase` or
the entire kernel invariant merely to clear a bitmap and pointer. State the
exact row/group update and null pointer result with an arbitrary disjoint
frame; use the existing `event_remove_waiter_image_eq` and
`task_set_event_ptr_image_eq` for the abstract consequence under their actual
canonicality/priority premises. Full TCB/ECB split and updated-merge must keep
all unwritten fields and padding. This separates a reusable source-level
helper from the stronger validity theorem its caller later establishes.

### Rdy caller composition checkpoints

Remove run `event_task_remove-20260913020326` is now `done`: its three manual
targets, controller group/parent checks, final apply and final-check passed.
Three canonical auto admissions remain part of the existing tool trust
boundary. The C implementation is unchanged; final executable tokens,
complete TCB/ECB declarations and six aliases match the selected upstream.
Its six-cell contract and proved
TCB/ECB full-image split/updated-merge interfaces do not assume linked-wait
status at call entry. Keep that distinction when connecting the actual Rdy
caller to the callee now applied on main:

1. Decode the event bitmap, then establish the actual priority-table TCB
   identity. Existing `event_wait_priority_head_eq` and
   `event_wait_priority_table_entry` give the canonical nonempty consequence;
   a group byte alone is not a TCB ownership or identity proof.
2. Preserve the selected row and task coordinates through Dly/Msg/Stat/StatPend
   stores. Rdy updates the ready row indexed by decoded `y`, whereas Remove
   rereads TCBY; their equality needs the canonical task-priority image.
3. Test suspension on the **updated** status byte, as the C does. The source
   mask and result arguments are bytes; the typed `PendType`/`PendStatus`
   consequences require their actual argument-encoding premises. The raw
   contract must retain the exact bitwise effect and must not replace this
   test by whole-status equality with RDY. The existing
   `task_event_wake_before_remove_image_eq` is a typed consequence, not a
   theorem for an arbitrary mask without the encoding premise.
4. Instantiate the exact proved Remove contract from the current image and
   carry all other fields, padding and ready resources as disjoint frames.
   Reconstruct the new Event/Task images before restoring their cross-module
   relation at the caller boundary.
5. Return the originally selected priority. Do not reselect from the event
   bitmap after Remove; its head may already be a different task.

Run `event_task_rdy-20260913034227` is now `done`. Its accepted annotation and
complete triage cover seventeen canonical manual targets in eleven shapes.
The two independent groups are `selection_and_tables` (ten targets) and
`updates_and_remove` (seven). The seven-target group has returned completed:
all assigned proofs are Qed and final combined debug passed in 69.697 seconds,
with case_lib and unassigned blocks unchanged and no added helper/import.
Its delegated fresh group-check passed in the controller. The ten-target
selection/table group subsequently returned all Qed, passed its final
combined debug in 9.749 seconds and passed controller fresh review with no
errors. Neither group added helpers/imports. All seventeen targets passed
controller group acceptance, deterministic parent merge/full check, final
apply and final-check. Isolated symbolic-execution freshness, current source
and shared dependencies, exact target coverage and forbidden/structure scans
passed. Applied function tokens, complete TCB/ECB declarations and six aliases
match the selected upstream; GCC ILP32 diagnostics confirm the 64/20-byte
layouts. Twenty-eight canonical auto admissions remain in the existing QCP
tool trust boundary, not additional assumption-free kernel proofs. This is
the actual caller composition with Remove and exact source effects; arbitrary
byte mask/result inputs do not imply whole-kernel invariant preservation.
Fifteen exact read-only dependencies include the finally applied Remove
spec. No live shared model or accepted callee candidate was edited during
this audit. Semantic feedback will aggregate both groups if needed.

### Wait helper intake

Run `event_task_wait-20260913025852` has an independent annotation handoff
and fourteen exact read-only model dependencies. It does not depend on the
Remove proof. Its entry preserves the actual current TCB identity while the
caller-prepared status/result/delay remain untouched. The intended composition
uses `task_set_event_ptr_image_eq`, `event_insert_waiter_image_eq` and
`sched_remove_ready_encoding`; `task_prepare_event_wait` remains the preceding
caller operation, not an extra effect attributed to Wait. In particular,
`sched_ready_structure` can describe the intermediate bitmap structure without
pretending the already-pending task is still logically ready. The annotation
is accepted with three manual targets; all three are now Qed and have passed
controller group and parent verification, final apply and final-check. The
run is `done` and its result is on main. One canonical auto admission remains
in the existing tool trust boundary. Input-byte ranges needed after the OR
writes were retained during the same annotation attempt. The contract does
not add a lock acquisition or status/delay store absent from the C function.

## Following dependency frontier: OS_SchedNew

The standalone intake retains the selected `os_core.c:1751` function body,
static linkage and const `OSUnMapTbl` declaration for the existing 64-priority
profile. It reads the ready group, one of eight ready rows and the 256-byte
constant lookup table, then writes only `OSPrioHighRdy`. There is no call,
nonempty-ready guard, OSRunning guard, TCB access or interrupt-mask operation.
The other ready rows and all unrelated globals must remain unchanged.

The low-level contract should expose this exact lookup result under protected
ownership, including the canonical empty bitmap result zero. It must not
silently promise a valid selected TCB in that case. The stronger result that
the byte names the highest-priority ready task follows separately from the
canonical bitmap, nonempty ready list and task-priority correspondence.
`sched.v` already supplies `unmap_table_rep`, lookup split/merge,
`sched_rows_array_equiv`, `sched_selected_priority` and
`sched_selected_priority_eq_head`; reuse these rather than creating another
decoder, bitmap representation or scheduler record.

`OS_Sched` and `OSIntExit` subsequently read the priority table and write
`OSTCBHighRdy`. The intermediate postcondition of SchedNew therefore retains
the old high TCB pointer. The existing `sched_priority_written_rep` and
`sched_priority_written_physical_eq` describe this boundary. A proof of this
helper is not a proof of context switching or of the callers' platform
contracts. Interrupt exclusion/protected ownership must come from the actual
caller contract, not from an invented lock acquisition inside SchedNew.

Function-specific definitions belong in
`VC/code_proof/sched/spec/sched_new_spec.v`; shared models remain read-only
while dependent proof groups are live.

The source intake check on 2026-09-13 passed selected function-token equality,
both scalar aliases, static linkage, GCC ILP32 syntax, eight ready bytes and
the lookup/global types. The first diagnostic caught an equivalent but
differently spelled `OS_PRIO` alias; the intake now retains the upstream
`typedef INT8U OS_PRIO`. Controller module routing passed 38 relevant tests.
Run `sched_new-20260913024634` records ten exact read-only model dependencies;
its annotation and complete five-target VC triage were accepted. The single
`sched_new_lookup` group proved all five manual targets without new helpers;
controller group/parent verification, final apply and final-check have now
passed and the run is `done`. Five canonical auto admissions remain in the
existing tool trust boundary. This proves the exact lookup helper, not the
subsequent context switch or ARM/BSP implementation.

### Next caller composition checkpoints

The actual `OS_Sched` and `OSIntExit` bodies at `os_core.c:1702` and `:693`
have also been read. Both call SchedNew only after testing interrupt nesting
and scheduler-lock nesting, then load the priority table and write
OSTCBHighRdy. They increment the unsigned global context-switch counter only
when the selected and current priorities differ. The selected configuration
disables per-task profiling and TLS; it does not remove the actual context
switch operation.

Their entry/exit boundaries are not identical. OS_Sched enters its critical
section unconditionally and has no OSRunning test. OSIntExit first checks
OSRunning, then decrements a positive nesting count (leaving zero unchanged)
before testing whether it may schedule. Do not attribute this decrement or
running guard to OS_Sched or SchedNew. The OSIntEnter/Exit pairing protocol
and a valid nonempty ready set belong to the relevant caller contract, not
to a fictitious guard inside SchedNew.

The priority-table owner correspondence is therefore the first composition
obligation after the proven byte-selection helper. The context-switch and
critical-section operations remain explicit platform contracts; proving
these C callers must not be reported as proof of ARM/BSP implementation or
as a same-task uninterrupted return. This source audit does not yet prove
either caller, and does not alter any existing platform contract.

The two standalone source intakes now exist under `annotated_C/src/sched`
and `annotated_C/src/interrupt`. Their selected complete executable tokens,
including the actual `do { ... } while (0)` critical macros, match upstream;
aliases and GCC ILP32 scalar/table/pointer checks passed on 2026-09-13.
They retain the static SchedNew declaration. For the GCC syntax diagnostic
only, the selected upstream SchedNew body was supplied on stdin so that this
static declaration had a definition; that body was not inserted into either
QCP target and the diagnostic was not a callee or linking proof. TCB is
opaque in these slices because profiling is disabled and the selected C
bodies only manipulate its pointers. The existing sched/int_exit spec files
were unchanged at intake; adding their module-local controller routing passed
forty relevant tests without changing acceptance rules. OS_Sched now has run
`sched-20260913042243`, with an accepted annotation and 31 exact read-only
dependencies, including the finally applied SchedNew spec. Its full-call
case-lib and generated interface checks passed; complete ten-target/eight-shape
VC triage was accepted. Its single full-call proof group has returned all ten
manual proofs Qed with final combined fixed debug passed in 31.07 seconds,
no new helper/import and unchanged case_lib. Controller fresh review,
deterministic parent verification, final apply and final-check all passed;
the run is now `done` with ten manual targets and ten canonical auto
admissions under the existing tool/platform boundary. A report-only routing-audit status mismatch was corrected by its
owner without editing or rechecking the formal candidate. QCP required an
explicit `struct os_tcb;` before the existing opaque
typedef. The final candidate's selected function tokens and four aliases
still match upstream, and removing only those three declaration tokens makes
its complete preprocessed C stream equal to the original intake. No field,
layout or executable statement was added. This is a parser adaptation, not
an implementation or compiler-refinement proof. The
OSIntExit intake now has run `int_exit-20260913065528`: its annotation owner
completed the full candidate with 32 exact read-only dependencies, including
the finally applied Sched and SchedNew specs. Canonical QCP, fixed case-lib,
generated-interface and source/layout checks passed, and controller accepted
the annotation. Independent `int_exit-vc-checking-r1` completed auditing all 11
manual targets; the 15 canonical auto admissions are not manual proofs.
The ordinary-return projection and resource-explicit exception-transfer
contract remain distinct. All local transfer/cache/parked-stack consequences
are proved; assembly nonreturn/restoration, hook implementation and ownership
handoff remain explicit external obligations. No new shared model field or
C algorithm change was made. Sched's model is a reusable dependency,
not a fictitious C callee; OSIntExit actually calls SchedNew and OSIntCtxSw.
The subsequent all-target static triage found one case-local proof-policy
repair: six direct calls to two names from the canonical forbidden table in
os_int_exit_prefix_cells_merge. This is not a new C/spec/model semantic gap;
the checker completed all eleven targets/seven shapes and returned that one
batched repair. Controller created annotation r2, whose owner changes only
the affected proof body, preserving its statement and C/contract semantics.
The accepted seed is not edited in place. The r2 repair and fresh complete
11-target/eight-shape triage have since been accepted. All targets are L7;
the single `int_exit_full_call` group has completed all eleven proofs of the
complete call path, not just the masked prefix. Final combined debug passed,
with no new helper/import or case-lib change, and controller fresh review
accepted the group. Parent verification, final apply and final-check have
now also passed; the run is `done` with exact 11/11 manual coverage and the
existing fifteen-auto-admission tool boundary. Current target/dependency
bindings, isolated symexec freshness and structural/forbidden scans passed.
The selected C implementation is unchanged. The explicit exception-transfer
platform contract remains a trust boundary, not a proof of ARM/BSP assembly.
Its two guarded nesting equalities use the
nontrivial pure alternatives; the other spatial targets retain their actual
cells and frames. Annotation Checking now
requires an early read/scan of that same canonical table so future writable
owners can repair such calls before freezing their seed. Parent/final gates
and the forbidden set itself remain unchanged.

The platform is the selected ARMv7-A/GNU port, whose OS_TASK_SW expands to
OSCtxSw; it is not the Cortex-M/PendSV example in the skill reference. Reuse
the existing `InterruptPlatformResources`, `CriticalRegionResources`, actual
saved word/invocation and certified interval semantics where applicable.
The main `sched_spec.v` and `int_exit_spec.v` seed interfaces establish masked
preparation and conditional global reconstruction, not a concrete OSCtxSw/OSIntCtxSw
call or original continuation return. A destination cache-install theorem
does not fill that gap. The profile enables OS_APP_HOOKS_EN and
OS_TASK_SW_HOOK_EN: App_TaskSwHook is not selected to be empty by the two
creation-hook definitions. Source variants, callback behavior and returning
versus retired invocation paths must stay within the explicit platform
contract, without inventing a new empty hook or a whole-Task frame.

The context-switch skill reference was corrected at this actual composition
frontier: safeExec does not itself establish atomicity or platform refinement;
stack/TCB and original-continuation effects cannot be reduced to runTask.
The change removes over-general template claims and fixes Task reference
links; it does not amend live handoffs or validate another ISA's template.
The IRQ reference was also reduced to source-specific entry/resource/return
checks: it no longer prescribes OutsideCritical at every IRQ boundary, treats
mutable nesting values as stable globals, or offers ordinary-RAM MMIO and
unproved whole-handler atomic templates. Its relative links and scoped
whitespace checks passed; the existing missing-PyYAML validator limitation
remains explicitly recorded rather than retried or reported as success.

The further source audit distinguishes the two call continuations. In the
ARMv7-A/GNU no-VFP source, OSCtxSw saves the task-level call frame before
writing the outgoing TCB SP; OSIntCtxSw does not save its own C call frame.
The first-level exception wrapper saved the interrupted task's context and
TCB SP before moving to the exception stack and calling the ISR/OSIntExit.
Thus the interrupt switch path must model the actual control transfer, not
promise an ordinary return to this OSIntExit invocation with another task's
state. This inspection does not select a floating-point variant or prove
the port implementation. Inspect the chosen variant and its actual frame
contract before claiming such an implementation result.

For the current OS_Sched run, retain the existing source-prefix model
and compose the finally applied SchedNew contract. Save/Restore must retain
their exact saved word, invocation and full critical-region resource contract.
An explicit platform switch interface may be parameterized, but must expose
its guard, consumed Task/stack resources, hook effects, selected-destination
boundary and original-invocation return/retirement behavior. A cache-install
equality, arbitrary poststate, whole-Task frame or invented empty switch hook
does not implement this interface. Any new case-local relation must be stated
independently of its preservation certificate; prove the required certificate
or identify the missing source/platform premise. Do not modify live shared
models or claim ARM/BSP correctness to close that obligation.

## Independent Flag pool initializer

The internal helper frontier also includes `os_flag.c`, not only `os_core.c`.
`annotated_C/src/flag/OS_FlagInit.c` now retains the actual `:1142` function
and complete selected OS_FLAG_GRP declaration. The same existing profile has
five groups, 16-bit OS_FLAGS and enabled names. Selected source tokens, four
aliases and GCC ILP32 syntax/layout matched on 2026-09-13: each group is 16
bytes, the pool is 80 bytes, and Type/WaitList/Flags/Name offsets are 0/4/8/12.
The new module-local controller route passed the current 35-test routing
selection. These checks are source/tooling diagnostics, not a C/VC proof.

Run `flag_init-20260913043225` had its first annotation accepted with ten exact
read-only dependencies, including the proved generic MemClr spec. Complete
eight-target triage found four independent L7 targets and four affected by
one case-local address-vocabulary gap: the layout constrained the independent
SeparationLogic.field_address, but the generated arrow cells use
CNotation.eval_addr_expr. Controller reviewed the complete repair set and
created `flag_init-annotation-r2`. The owner corrected only the four actual
generated arrow-address bindings for the selected ABI in the existing
case_lib; controller accepted the new candidate. Fresh complete triage of
all eight targets/six shapes then found only L7 proof work, no upstream gaps,
and was accepted. The single flag_pool_initialization group completed all
eight manual proofs with six proved suffixed helpers. Controller fresh review,
deterministic parent verification, final apply and final-check all passed;
the run is `done` with exact 8/8 manual coverage. The final applied complete function/static signature,
struct/aliases and GCC ILP32 layout diagnostics passed against upstream.
There was no C algorithm change, new axiom or shared model write. The first
round's acceptance was not transferred to the repair. Nineteen canonical
auto admissions remain part of the existing tool trust boundary, not manual
proofs or an assumption-free whole-kernel result.
The final canonical QCP, fixed case-lib and generated interface checks passed;
all 357 initial non-comment C tokens and all registered dependencies remained
unchanged. The case-lib proves both byte-view conversion directions and the
exact initialized-image consequence to flag_initial/flag_inv.
The selected branch clears the pool, links consecutive free groups, sets
UNUSED type and the actual default name, terminates the last link and writes
OSFlagFreeList. Flag bits and all five padding bytes per group stay zero.
The unselected single-group branch never clears padding and must not inherit
that selected-branch claim. OS_FLAG_GRP remains independent of ECB resources.

Connect the actual 80-byte MemClr call to existing `flag_group_rep`,
`flag_initial_image` and `flag_initial`, with explicit alignment/layout and
representable end-address premises. Preserve the actual string literal
resources and arbitrary disjoint frame. Empty used/wait maps and a fresh
generation counter describe the startup abstraction; they are not extra C
stores or permission to erase a live wait-node map. This helper does not
prove FlagBlock/TaskRdy/Unlink or restore a running whole-kernel invariant.

## Timer allocation and release source intakes

The next independent Timer helpers are the actual static `OSTmr_Alloc` and
`OSTmr_Free` at `os_tmr.c:807/:839`, not guessed `OS_Tmr*` APIs. Standalone
source intakes retain their complete selected bodies, callback function
pointer typedef and OS_TMR declaration. Source-token/static-signature/type
comparisons and GCC ILP32 diagnostics passed on 2026-09-13: names are enabled,
the object is 40 bytes aligned to four, and both counters are 16 bits. The
three non-Timer scalar aliases also match. OS_TCB is opaque here and occurs
only in the source's original null pointer casts; neither helper dereferences
a TCB. The Timer routing selection passed 37 tests. Independent runs
`tmr_alloc-20260913045648` and `tmr_free-20260913045648` now register the nine
actual read-only Timer/field/helper dependencies. Alloc's annotation has been
accepted with three manual targets (two returns and one which-implies);
complete VC triage and all three manual proofs passed. No group helper or
case-lib change was needed. Controller fresh review, deterministic parent
verification, final apply and final-check all passed; the run is `done` with
exact 3/3 manual coverage. The final
applied function/static signature, full struct, callback typedef and scalar
aliases match upstream, with GCC ILP32 diagnostics passed. Its canonical QCP, fixed case_lib and export
checks passed, retaining the callback typedef and source body; the only
declaration adaptation is the diagnosed opaque-tag forward declaration.
Raw/configured framed consequences, exact modulo counters and private resource
transfer are proved in the case_lib. Eight canonical auto admissions are not
counted as manual proofs. Free's annotation and complete three-target VC
triage were accepted with no upstream repair item; its tmr_free_contract
group proved all three targets without helper/import or case-lib changes.
Controller fresh review, deterministic parent verification, final apply and
final-check all passed; the run is `done` with exact 3/3 manual coverage.
The final applied complete static function, Timer declaration, callback typedef,
scalar aliases and GCC ILP32 layout diagnostics match the pinned source.
Its raw/valid-pool derived specification proves the real residual frame and
configuration restoration; five canonical auto admissions remain within the
existing tool trust boundary. The new Timer ABI contract must bind the actual canonical
address vocabulary before relating it to timer_object_rep's numeric offsets,
using the Flag triage lesson without assuming a missing shared-model theorem.

Alloc returns NULL unchanged for an empty free root. Otherwise it advances
the root, zeros the detached object's next/prev links, increments used and
decrements free counters, and returns that object. The correct model endpoint
is `timer_allocate` plus the transferred `timer_private_rep`, not an already
published `TimerObjectState`. Its ghost invocation/generation identify the
allocation lifetime and are not additional C stores. All other object fields,
wheel, time, semaphore handles and Task resources remain untouched.

Free writes UNUSED state, option/period/match/callback/argument zeros, the
actual default name, zero prev, old free root as next and the new free root;
it updates the two counters in the opposite direction. It retains Type,
Delay and all padding, as `timer_free_image` records. It neither removes a
wheel member nor invokes a callback or acquires exclusion. The stronger
`timer_release_preserves_validity` requires the actual used object to be
non-running; the running Delete caller first executes Unlink. Do not require
unused old links to be zero, silently remove the wheel in Free, or call a
private allocation a published timer. Counter effects follow unsigned
16-bit arithmetic; absence of wrap under a valid 16-slot pool must be derived
from its count/partition facts, not inserted as an unexplained assumption.

### Running-object unlink composition

The actual `OSTmr_Unlink` at `os_tmr.c:1054` now has a standalone source intake
and run `tmr_unlink-20260913073058`, with nine exact read-only Timer dependencies
and an independent annotation owner. The complete static function, OS_TMR and
OS_TMR_WHEEL declarations, callback typedef and three aliases match the selected
source. GCC ILP32 diagnostics passed: a spoke is eight bytes (First at zero,
16-bit Entries at four and two padding bytes), and the seven-spoke table is
56 bytes. Module-local routing passed 36 related tests. These are intake
diagnostics, not annotation acceptance or a completed function proof.

The helper computes Match modulo seven, distinguishes the actual head pointer
from the non-head branch, repairs predecessor/successor links, writes STOPPED,
clears the target links and decrements the selected spoke's 16-bit count. It
does not free the object, alter Timer time/free counters, call a hook or acquire
exclusion. The full public Delete source confirms its running branch calls
Unlink before Free; stopped/completed branches call Free directly. This is a
real interface-composition checkpoint, not a new public Delete proof.

Existing timer_unlink preservation and scan-footprint interfaces are reused.
In particular, changing a predecessor's Next can affect a retained traversal
cursor; module validity alone does not imply scan continuation. The Timer
skill now records the source-backed distinction between private allocation,
publication, unlink and recycling, and requires actual neighbor/callback
footprint reasoning. This documentation change does not expand live handoffs
or introduce shared-model edits; scoped whitespace checks passed.
The owner completed the full raw/configured candidate with twelve proved
case-lib lemmas. Canonical generation, fixed case-lib, generated export and
the forbidden-name scan passed; controller accepted the annotation and
`tmr_unlink-vc-checking-r1` completed all ten manual-target audits. Twenty-three
canonical auto admissions retain the existing tool boundary. Independent
triage found that the r1 size fact, although propagated, bound
`sizeof_struct_type`, while the actual emitted expression uses
`sizeof_alias_type`; both field functions similarly bound `FET_struct`
instead of the emitted `FET_alias`. GCC layout agreement cannot establish
equalities between these independent Coq parameters. Controller created
annotation r2 to repair both case-local vocabulary bindings together,
preserving the numeric ABI, complete resources and C implementation; no
shared-model write is required. This lesson is recorded in the state-abstraction
skill. An empty pure alternative in entail_wit_2 cannot
serve as evidence for that spatial rewrite; the full spatial branch is to be
proved. This distinction is now also recorded in the VC-checking skill,
without editing canonical targets or transferring acceptance. Annotation r2
and fresh complete ten-target triage have now been accepted: nine raw-source
targets and one configured-contract consequence are independent proof groups.
The raw group completed all nine proofs with final combined fixed debug and
no helper/import or case-lib changes. The configured consequence and twelve
suffixed helpers also completed after repairing two forbidden direct proof
calls; only the final compliant bytes were accepted. Both controller fresh
group checks, deterministic parent verification, final apply and final-check
passed. The run is now `done`, with exact 10/10 manual coverage and the
existing 23-auto-admission tool boundary. Current targets, shared dependencies,
isolated symexec freshness and structural/forbidden scans passed. The selected
C implementation and ABI remain those of the audited upstream intake; no
shared-model field was added. This proves the real raw/configured unlink
interfaces, not the complete public Delete or arbitrary traversal stability.

## Tick caller source intake

`tick/OSTimeTick.c` preserves the selected complete `os_core.c:937` body,
including the tick hook, volatile OSTime, all stepping cases, the idle-priority
sentinel, and one Save/Restore interval per processed task. On 2026-09-13 its
function tokens, complete TCB declaration and eight aliases matched the pinned
preprocessed source. GCC ILP32 diagnostics confirmed the 64-byte TCB, relevant
field offsets, eight ready rows and volatile time type. A diagnostic initially
used 24 rather than 20 for OSTCBNext's expected offset; correcting that test
expectation required no C edit. The updated module-local routing selection
passed 38 tests. Run `time_tick-20260913062313` is now registered with thirty
exact read-only model dependencies and its new module-local case_lib; it is
assigned to its independent annotation owner, with no annotation or
function-proof acceptance yet. The handoff preserves all source branches and requires explicit hook,
continuation and cursor-stability premises rather than assume an atomic scan.

The hook precedes the counter update. The 32-bit counter advances even when
OSRunning is false or stepping says WAIT. ONCE advances to WAIT; an invalid
step byte resets to DIS. The task scan stops at the idle priority, not NULL,
does nothing for delay zero, and decrements only a positive delay. On expiry
it clears PEND_ANY, writes the exact pending result, and inserts into ready
bits only when the resulting status is not suspended. It does not remove
Event bits or Flag nodes, clear event pointers, deliver a message or call
OS_EventTaskRemove/Rdy. Existing tick_task_update/tick_task_step and linked
timeout phases represent these intermediate states; the waiting caller owns
later registration cleanup.

The selected ARMv7-A port's OSTimeTickHook calls App_TimeTickHook and increments
its private OSTmrCtr; at the selected 100/10 tick-rate threshold it resets that
counter and calls OSTmrSignal. Neither that hook nor its signaling effects are
proved by the current intake. The hook may be entered with interrupts enabled
or disabled. Do not replace it with an empty call, confuse OSTmrCtr with the
ghost tickCtr or Timer's OSTmrTime, or claim the whole scan is atomic. Cursor
and next-TCB lifetime, list/sentinel stability between critical intervals and
hook/ISR environment effects need explicit source-backed caller protocols.
The source permits ticker-ISR and high-priority-task callers; any restriction
to one calling mode must be stated rather than silently assumed.

The first Tick annotation audit completed the independent clock/step, task
scan, full pure invariant/TCB merge and private 16-bit counter consequences;
its final version-bound case-lib check passed. C stayed unchanged and no VCs
were generated. The owner returned one aggregate source-only request for
the existing canonical `sem/spec/sem_post_spec.v` and
`event/spec/event_wake_spec.v`, retaining explicit hook/serialized-caller,
mask-outside-read, cursor lifetime and ISR-versus-task continuation obligations.
Controller reviewed that terminal result and created `time_tick-annotation-r2`
with 32 read-only dependencies and no shared write paths; the new owner is
complete. Its full C annotation generated successfully, covering all clock,
step and scan branches: 97 interface obligations, including 31 manual targets.
The current-version fixed case-lib check and owner whole-target review passed;
controller accepted annotation r2 and started independent
`time_tick-vc-checking-r1` for all 31 manual targets. That full triage returned
two repair causes together: missing exports in the actual generated goal's
import closure, and loss of the old UInt delay range before overwriting its
cell on all five positive-delay loop paths. The truncated new value's range
does not bound the old mathematical value. Annotation r3 repairs both in C
annotations only, preserving all 31 targets, executable C, public contract,
case_lib and shared models. Its canonical generation, fixed case-lib check
and actual new-goal export smoke passed; controller accepted r3. The next
independent `time_tick-vc-checking-r2` completed in a fresh owner session
after a temporary runtime thread limit. Its complete target and unsigned-write
audit confirmed the r3 fixes and found one remaining independent issue:
`partial_solve_wit_5_pure` loses old OSTime's nonnegativity at the pre-increment
split. A post-write unsigned range cannot establish the old sign needed for
`unsigned_last_nbits` versus `Z.rem`; old value -2 is a counterexample to the
weakened VC premises, not an execution from the original typed UInt cell.
Transporting the already available old-value lower bound suffices for this
equality. No additional issue was found in delay, step, status/ready bytes or
the separately contracted private hook counter. Controller reviewed that
complete feedback and created annotation r4. Its new owner has made a two-line
C annotation repair and regenerated all 31 manual targets once; the missing
sign fact is present in both pure alternatives and the post-write checkpoint.
Case_lib, shared models, executable C and public contract are unchanged.
The fixed case-lib check and actual generated-goal export smoke passed;
controller accepted annotation r4. Independent `time_tick-vc-checking-r3`
completed all 31 targets across 17 shapes with no new semantic repair, a
passing fixed interface check and passing diagnostics. Controller accepted
its group plan and started `time_tick-vc-proving-r1`: `clock_and_step` (12),
`traversal_and_return` (12), and `task_update_backedges` (7), with no inter-group
dependencies. All three groups have passed controller fresh review in isolated
group worktrees, giving 31/31 accepted manual targets. Deterministic parent
merge, whole-function verification, final apply and final-check have all passed;
the run is now `done`, with eight formal files applied to main. Isolated
canonical symexec freshness, current shared dependencies and the full manual
structure were checked. The 66 canonical auto admissions remain an explicit
tool/auto trust boundary, not manual proofs. The
explicit supported calling mode is an already-open, IRQ/FIQ-masked
ISR region with nonzero nesting, and the application hook class permits its
own resource work plus ordered canonical semaphore posts. It is not a proof
of arbitrary kernel-mutating callbacks or an unmasked concurrent scan. The
existing global invariant supplies the running idle-tail fact; no new public
idle-tail premise was added. The r1 mathematical candidate is preserved,
not accepted as a C proof.
The added read-only bootstrap registration route passed 40 related tests;
three additional acceptance-state/path checks passed after extending coverage.
It first binds requested unchanged bytes without editing old input/report,
retains the ordinary generated-source and proof gates, and rejects dependency
drift or an attempt to obtain shared write permission. No unnecessary shared
model edit or second semaphore/wake implementation was introduced.
