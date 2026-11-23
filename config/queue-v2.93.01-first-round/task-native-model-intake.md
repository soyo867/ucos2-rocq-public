# Native Task / Scheduler model integration

## Latest whole-kernel scope and progress (2026-09-09)

The user extended the model task from Task/Queue to every uC/OS-II module.
The [whole-kernel foundation intake](../ucos2-v2.93.01-model-foundation.md)
now governs the remaining shared-model convergence; later sections retain the
history of earlier bounded runs, not an exemption for missing enabled modules.
The selected configuration already enables Flag, Memory and software Timer.

SemQuery run `sem_query-20260909110506` is now controller `done`: all sixteen
manual targets passed group, parent and final checks. Thus five of the sixteen
previous Mutex/Sem/Queue functions have current intermediate-version results
(SemAccept, SemSet, SemPost, SemQuery, QCreate), not final whole-model acceptance.
Native Mutex helper run `mutex_priority-20260909114354` has all twenty-five
manual targets accepted at group, parent and final level, is final-applied,
and is controller `done` (twenty-six auto/tool-trust obligations remain within
the existing claim boundary). The source-only `del_full-20260909131500` r1 report
collected nine causes but remains blocked, including missing OS report audit
fields. Its diagnoses are navigation, not acceptance or authority to widen
the frozen handoff. No queued old proof migration is launched merely to count
more successes on this intermediate model.

Source/design audit, 2026-09-08. This file is not proof or acceptance evidence,
does not authorize formal writes, and does not change the selected configuration.
Use the pinned source in `profile.json` and the separately authorized
[atomic-publication patch](../../source_variants/task-atomic-publication/os_core.patch).
The current MutexDel annotation r2 remains an independent, fixed-C attempt.

The native target is now
`uC-OS2_verify/annotated_C/src/task/OS_TCBInit.c`. On 2026-09-08,
`python3 uC-OS2_verify/tests/task_publication/check-tcb-source.py` passed its
complete preprocessed function/TCB/scalar-alias comparison against the patched
selected source, plus GCC freestanding ILP32 syntax/layout. This is intake
evidence only, not formal acceptance or validation of external hooks.

## Confirmed verification boundary (2026-09-08)

The user has explicitly approved verification of the kernel C code under
precise external-platform contracts and the documented Mutex owner-use
protocol. Controller retry `task_tcb_init-annotation-r4` records that confirmation
in `prior_failure_summaries[0].reason`. Its pending shared-path authorization
was created just before the confirmation, so that authorization's older reason
still describes the choices as unresolved. That is historical context, not a
new approval gate. Frozen r1-r3 inputs, reports and checked candidates remain
unchanged; the confirmation does not inherit their acceptance or widen paths.

- External contracts cover the actual critical-protection and low-level
  call/switch/return guarantees consumed by the C proof. ARM instruction,
  exception-entry and BSP implementation correctness are not claimed proved.
  Keep assumptions explicit at interfaces or theorem parameters; this is not
  permission for a new Coq axiom/admission or an assumption that all kernel C
  operations preserve the global invariant. Saved interrupt values, permitted
  environment effects and the returning invocation must still be connected
  where the current function uses them. Do not model these calls as empty.
- The Mutex owner must not pend on another event, and clients must not change
  its priority while it owns the mutex. `OS_DEL_ALWAYS` additionally requires
  a ready owner when there is one. The latter is a call-site obligation, not
  evidence that every owner is always ready under every kernel operation.
  Preserve actual API error branches and distinguish client misuse from
  documented-use behavior. Wider defensive misuse handling is a separate
  implementation/claim extension, not an unresolved choice in this round.
- The selected four creation hooks and repaired `OS_TCBInit` executable body
  remain fixed. Continue toward the main function's complete specification,
  assertions and canonical VCs using its actual dependencies; independent
  Scheduler work remains required, but a whole ARM/BSP proof is not a
  prerequisite. Any new blocker must identify a concrete remaining source or
  proof obligation, not repeat the two already answered scope questions.

The local LOS reference uses this kind of interface boundary in
`../LOS_Verify-capability/annotated_C/src/task/los_task_LOS_TaskDelete_concur.c`
(lines 13-32, paths relative to the main repository root): `LOS_IntLock` and
`LOS_IntRestore` have explicit critical-resource contracts. Its
`lib/Los_Rules_lib.v` supplies the abstract STS. These are method references,
not evidence that the ARM/BSP implementations or exact saved-register return
behavior have been proved, and not substitutes for this function's contracts.

### Subsequent source and Queue-domain decisions

The user subsequently confirmed "我同意 你可以自行决策" after the distinction
between repaired-source verification and a conditional original-source claim
was explained. The selected decisions are now:

- Bind the already-existing conditional-current Mutex helper repair to the
  pinned native source through the separate
  [mutex-current-priority variant](../../source_variants/mutex-current-priority/README.md).
  This is an intentional implementation correction, not original-source
  equivalence or retroactive acceptance of the `_full` verification slice.
- Verify the six Queue targets under an explicit caller/environment lifetime
  protocol: from the successful type observation through the last protected
  access, the same Queue allocation is not deleted or reused. Mutable queue
  contents and wait sets may change before acquisition; NULL and observed
  wrong-type paths remain. Application callers must establish this protocol;
  the kernel does not gain a new runtime lifetime check by model declaration.

These are no longer unresolved user choices. Frozen r4 input and prior reports
are unchanged: any new executable binding or expanded shared write scope must
be consumed by a supported controller transition and new source version.
Continue independent authorized r4 work without importing the new variant as
an already-proved environmental action.

## Controller intake scope

The first formal target is `OS_TCBInit`, case `task_tcb_init`, using the complete
native target above. Preserve its executable tokens; only annotation and the
case spec are initially writable. Shared owners require the controller's exact
authorization. This run develops the common Task/Scheduler foundation needed
by the remaining Task and Queue functions; a separately named, disconnected
toy publication model is not a replacement for integrating those consumers.

The internal entry contract must be derived from Create/CreateExt's priority
reservation and actual stack/argument ownership. Cover both free-head success
and exhaustion (return 66), full private initialization, both hook calls, final
publication, Restore interference and exact return 0. Keep rollback with the
public wrapper that actually performs it. Existing native and verification-slice
clients must have explicit layout bindings and proved preservation, not a
silent global offset replacement or an incompatible second copy of the state.

Start with a single-owner, complete shared-owner/consumer analysis. If the
initial write boundary is insufficient, return one exact minimal shared repair
request with the source-backed model delta; do not generate known-invalid VCs
or stop at the first missing atom. Complete any independently useful permitted
case work without importing old acceptance. The user has now selected the
official empty creation hooks and requested an extensible contract; see the
[new Task hook binding](../task-native-v2.93.01/README.md). Existing r1/r2
handoffs predate that choice and are not rewritten. Consume the choice through
a new controller-bound source/claim version before using its concrete effect;
keep independent kernel representation/publication work moving meanwhile.

Read-only, non-acceptance references for the overlapping independent gaps are
`reports/del_full-20260908090121/rounds/del_full-annotation-r2/agent_report.json`
and the candidate under
`worktrees/q_flush-20260905101125/q_flush-annotation-r4/`. The MutexDel r2 owner
is terminal blocked and its attempt was controller-reviewed as blocked; it is
not a live writer. Do not alter its existing NO_PEND C repair or infer that the
reported broad-callee model mismatch establishes a new implementation bug.

## Exact representation delta

The selected upstream `Source/ucos_ii.h:560` declares 23 fields. Existing
`tests/task_publication/check-layout.sh` evidence is host preprocessing plus GCC
ILP32 layout, not ARM ABI or QCP acceptance. Its 64-byte, alignment-4 result is
an input to a future source/layout bridge, not permission to replace just
`task.v::sizeof_OS_TCB = 68`.

| Native field | ILP32 offset | Current shared slice / model obligation |
|---|---:|---|
| OSTCBStkPtr | 0 | Missing; initialized by the port stack result, later written by context switching |
| OSTCBExtPtr | 4 | Missing; preserve the supplied pointer, not ownership of arbitrary extension contents |
| OSTCBStkBottom | 8 | Missing; stack allocation and lifetime belong to the actual caller/port protocol |
| OSTCBStkSize | 12 | Missing; count of OS_STK elements, not bytes |
| OSTCBOpt | 16 | Missing; exact 16-bit option value |
| OSTCBId | 18 | Missing; public 16-bit task ID is not the pool slot TaskID |
| OSTCBNext / OSTCBPrev | 20 / 24 | Slice offsets 28 / 32; establish active-list and free-list topology |
| OSTCBEventPtr | 28 | Slice offset 12; keep object identity distinct from layout |
| OSTCBMsg | 32 | Slice offset 24; preserve exact pointer observation |
| OSTCBFlagNode | 36 | Missing although flags and deletion are enabled |
| OSTCBFlagsRdy | 40 | Missing; OS_TCBInit does not initialize this field on every reuse |
| OSTCBDly | 44 | Slice offset 4; exact 32-bit delay value |
| OSTCBStat / OSTCBStatPend | 48 / 49 | Slice offsets 1 / 2; preserve all selected status bits |
| OSTCBPrio / OSTCBX / OSTCBY | 50 / 51 / 52 | Slice offsets 0 / 8 / 9 |
| OSTCBBitX / OSTCBBitY | 53 / 54 | Slice offsets 10 / 11; priority-derived encoding |
| OSTCBDelReq | 55 | Slice offset 36; native request encoding is 63, not boolean 1 |
| OSTCBTaskName | 56 | Missing; pointer identity and readable string lifetime are different obligations |
| OSTCBRegTbl[0] | 60 | Missing; selected table size is one 32-bit register |

The old representation also owns two multi-event pointer cells even though
`OS_EVENT_MULTI_EN = 0` in this profile. It cannot be used as a physical subheap
of the native TCB by reinterpreting its base address. Native padding at offsets
42--43 and byte-copy behavior also need a representation: TaskQuery invokes
`OS_MemCopy(..., sizeof(OS_TCB))`, not a field-by-field abstract observation.
Do not promise particular padding bytes without the memory/initialization model.

`OS_InitTCBList` (`os_core.c:1591`) initially clears the whole TCB pool and
links its free nodes. Later deletion does not recreate zeroed TCBs. A reusable
free-TCB predicate must own all field/padding storage with the values left by
the previous lifetime; `store_free_task_nodes`, which currently owns only Next,
cannot establish writes to the other native fields during allocation.

The raw-to-published bridge must also preserve the definedness of fields that
creation does not write. In the r2 candidate, an arbitrary free image can have
`TCBFlagsRdy = None`; initialization leaves that value unchanged, whereas
`task_native_image` of a published task always has `Some tcbFlagsRdy`. Those
images cannot be equated. Establish the needed retained-field observation from
pool clearing and source-correct recycling, or represent its genuine unknown
state in the published observation. A lemma starting from an already complete
`TaskAbstractState` does not cover an arbitrary free image. Pre-hook contracts
likewise must not demand completed active-list links before the commit writes
Next/Prev; distinguish hook-readable coordinates from final image assembly.

Keep three notions separate: pool slot, application OSTCBId, and lifetime of an
allocation. Reuse of the first two is not identity of the original invocation.

### QCP address calibration (N1)

An isolated probe using the native declaration and the required forward tags
was run on 2026-09-08 with the canonical one-shot driver, 32-bit/little-endian
selection, `QCP_demos_LLM` include/SLP and `uC-OS2_verify` SLP. The final probe
completed symbolic execution (rc 0); its generated obligations were inspected,
not Rocq-accepted. No function in a formal worktree was edited for this probe.

- `return sizeof(OS_TCB)` with result 64 generates
  `sizeof("os_tcb") = 64`. QCP does not reduce the named size to the numeric
  native profile. `CNotation.v` declares named sizes as parameters.
- A priority read whose contract owns the canonical arrow-field cell generates
  the same `&(ptcb # "os_tcb" ->ₛ "OSTCBPrio")` on both sides, with `v = v`.
  In contrast, an address-return probe requiring byte offset 50 generates
  `&(ptcb # "os_tcb" ->ₛ "OSTCBPrio") = ptcb + 50 * sizeof(UCHAR)`.
  Neither numeric byte coverage nor an unrelated `field_address` definition
  proves this equality: QCP arrow notation uses opaque `eval_addr_expr`.
- For `ptcb->OSTCBRegTbl[0] = 0u`, a scalar `data_at` contract normalized its
  address differently from the write's `pointer_offset(..., 0, sizeof UINT)`
  and symbolic execution failed to obtain write permission. Using the existing
  `UIntArray.full` interface from `int_array_def.h` succeeded without changing
  that C statement. The generated post retains the exact
  `replace_Znth 0 0 l` update; its split obligation uses the ordinary array cell
  and residual. This is a usable annotation/representation route, not evidence
  of an implementation defect or of the whole initialization loop being proved.

The next native candidate should use one canonical C-facing address vocabulary
and reuse the existing field-list split/original-merge/updated-merge structure.
LOS `lib/task.v::used_complete_task` and `store_used_task_map` illustrate direct
arrow fields and symbolic structure strides; they do not supply a proved
numeric ABI bridge. The native numeric layout, complete field ownership,
padding, `OS_MemCopy`, pool-array indexing and assembly's TCB offset 0 must remain
explicitly connected obligations. Do not drop those consumers, add per-function
layout assumptions, or call `native_tcb_layout_covers_exactly_64_bytes` a C/ABI
refinement theorem. Any shared representation repair belongs to the sole
controller-authorized owner after the current live check, not a second writer.

## Source-driven publication stages

These are proposed semantic interfaces, not new assumed invariants or theorem
names. More than one creator may be interrupted, so a single global boolean
`initializing` is not an adequate representation.

1. **Reserve priority.** Create/CreateExt changes a free slot to the reserved
   sentinel under critical protection. Bind the reservation to the creator's
   invocation; no TCB has necessarily been allocated yet. Other occupied
   priorities, mutex reservations and already published tasks are framed.
2. **Detach private TCB.** OS_TCBInit removes one free-list head while protected,
   transferring complete node ownership to this invocation. It is absent from
   the active/free collections and ready bitmap, but accounted for by a pending
   allocation entry. Failure leaves the reservation for the wrapper to release.
3. **Initialize and call hooks.** The selected fields are initialized outside
   that critical section. Track actual saved interrupt state, private storage,
   initialized fields, reservation ownership and possible source interference.
   Next/Prev are not the published list links yet; FlagsRdy is not reset here.
4. **Commit while protected.** The repaired source writes new Next/Prev, old
   head Prev, list head, ready group/table and task count, then publishes the
   priority-table pointer. Use intermediate spatial stages for these individual
   writes; only the completed transition restores the published invariant.
5. **Restore and return.** Successful publication is a historical event. Once
   interrupts are restored, another legal operation may suspend or delete the
   new task. Do not strengthen return into “the task is still ready/live”.
   The caller's original invocation must itself be the one that resumes.
6. **Rollback.** On no-free-TCB failure the public wrapper clears its own
   reservation; it does not return an allocated node or free the application
   stack. Exact error returns and non-target frames remain part of the spec.

Hook source boundary: the selected ARMv7-A `os_cpu_c.c` delegates Create/TCBInit
hooks to App_TaskCreateHook/App_TCBInitHook because APP hooks are enabled.
The user-selected implementations are the official empty definitions from
`Cfg/Template/app_hooks.c`, recorded in the separate Task hook binding above.
This does not update old frozen profiles/handoffs or prove the new instance.
The TaskCreateHook comment says interrupts are disabled, while the OS_TCBInit
call is after Restore; use the actual call path, not that comment. Separate
the generic effect/frame/commit-safety contract from its concrete empty
instance, and preserve environmental interference. Custom hooks require a
new source binding and their own contract proof, not an unconditional no-op
assumption.

### Interrupt interface audit (N8)

The pinned GNU ARMv7-A port uses `MRS; CPSID IF; DSB; BX` for Save and
`DSB; MSR CPSR_c; BX` for Restore, in A32 code. These two routines agree in
the no-VFP, D16 and D32 files; this does not select an FPU/context-switch
configuration or verify those other routines.

Do not interpret arbitrary 32-bit values as valid complete CPSR transitions.
Ordinary MSR does not write the T execution-state bit. IRQ writes require
privilege; FIQ writes also depend on NMFI and security/virtualization controls.
Mode changes have separate legality conditions. See
[ARM DDI0406C.d, B1-1153, CPSRWriteByInstr](https://documentation-service.arm.com/static/5f8daeb7f86e16515cdb8c4e).
Likewise, normal MRS reads execution-state bits as zero; the source's A32
execution condition matters for an exact-word specialization. See the
[ARM assembler MRS reference](https://developer.arm.com/documentation/dui0588/b/ARM-and-Thumb-Instructions/MRS--PSR-to-general-purpose-register-).

Keep the mathematical IRQ/FIQ observer, its platform conditions, the actual
saved local token and the source-to-architecture boundary separate. A proved
bitmask identity is not proof that the processor admits that write. Establish
the selected execution conditions, or state the existing hardware-interface
limit explicitly; do not silently choose a boot/security setting or add an ISA
axiom. DSB, exception return and original-invocation resumption remain distinct
from these direct-value lemmas.

The whole call also includes `BX LR`. A formula for CPSR immediately after
`MSR CPSR_c` is not automatically its value after returning to a Thumb caller.
Bind the saved R0 word at the actual MRS and preserve the IRQ/FIQ observations;
carry the return continuation/interworking relation separately. Do not select
ARM-only callers merely to make the existing A32-stage lemma sufficient.

The independent 2026-09-08 source audit also found these concrete consumers:

- `os_cpu_c.c::OSTaskStkInit` ignores `opt` in its executable body. It selects
  the frame using the linked `OS_CPU_ARM_DRegCntGet`: 0/16/32 double registers
  produce 16/50/82 words (64/200/328 bytes), respectively. With the selected
  32-bit scalar width and byte addresses, returned SP is
  `align_down(ptos + 4, 8) - frame_bytes`.
  Do not infer the smaller optional-FP frame described only by its old comment.
- `OSCtxSw` writes the outgoing stack and the native TCB's `OSTCBStkPtr`, then
  invokes `OSTaskSwHook`, rereads the actual high-ready pair, updates current
  selection and restores the incoming frame. It cannot frame the entire native
  Task state. `OSIntCtxSw` relies on the outgoing SP save in exception entry.
- All switch variants invoke `OSTaskSwHook`, which dispatches the unselected
  `App_TaskSwHook`. Exception dispatch additionally depends on the BSP's
  `OS_CPU_ExceptHndlr`; tick/delete/return paths have their own App hooks and
  timer effects. The two selected creation hooks do not fix these implementations.

The three context variants may share a parameterized interface where the
source supports it; none is selected by this audit. The confirmed C/Coq claim
uses explicit external-platform contracts, without claiming implementation
proof of these variants. Do not replace the required interface with an
endpoint-validity or live-invocation filter. A returning trace must recover
the same saved continuation/lifetime; deletion and non-returning traces must
remain representable. The already proved value equations remain reusable,
but do not become instruction-refinement proofs by this scope confirmation.

### Critical-resource interface repair boundary

The r4 acquire obligations cannot be closed just by unfolding the existing
STS. `ucos2_rules_lib.v::UCOS2_CS_C` fixes only `StableGlobVars`, while
`Rocq/SeparationLogic/CriticalSTS.v` uses a single `unit` token for critical
exclusion. Neither definition establishes native validity or transports a
particular priority reservation/invocation generation. The corresponding LOS
Lock contract explicitly lends `task_inv` and its Restore contract requires
that invariant back; the STS declaration alone does not derive that memory
contract.

Keep the next repair separated into three connected obligations: the logical
native invariant borrow/return protocol with source-client preservation;
key-wise reservation/private-allocation framing across other operations; and
the selected platform's original-continuation guarantee connected to the Task
invocation ledger. The r4 `NativeCriticalResources` and
`NativePlatformResources` records currently leave these connections abstract.
Existing `native_task_reserve_other_priority` and
`native_task_retire_preserves_pending_resources` are useful local frame facts,
not proofs for every environment action. Supply the missing concrete
interpretation/composition proofs; do not add a blanket platform assertion
that all kernel clients preserve the invariant, or demand a whole ARM/BSP
implementation proof before continuing the C/resource reasoning.

The controller-reviewed r4 candidate now has full main-function annotations
and a successful final fixed round check, but no accepted VC proofs. Its
successor r5 retains the same 25 shared writable paths and four read-only
dependencies. The bounded next milestone is a compositional TCBInit client
theorem, not an assertion that every native kernel client already implements
the required interfaces:

- Acquire lends the complete global invariant through an interpreted logical
  resource protocol, separate from the CPU saved-mask contract.
- A priority/invocation/origin-keyed Pending or Private(slot, generation)
  resource agrees with the reservation ledger; private bytes are held
  separately. Same-continuation coherence connects the external return to the
  original active invocation, rather than relying on copied token fields.
- TCBInit itself must prove detach, private initialization and publication
  preservation. Error 66 returns its Pending ownership to the wrapper; success
  consumes the reservation and records publication without promising that the
  new task remains live after subsequent interference.

The real Create caller and other API source certificates remain explicit
linking obligations. Existing Mutex/Queue counterexamples are not erased by a
parameterized client theorem, and a record containing desired conclusions is
not their proof. These interfaces fit the current project-owned Task,
interrupt, rules and global-invariant files; they do not require weakening the
full invariant, changing the core CSL library, or opening other C/profile files.

### TCBInit delivery boundary audit (2026-09-09)

The read-only review of annotation r5 and the current proving r2 distinguishes
the compositional function claim from its eventual native-kernel instance:

- `task_tcb_init_entry` already requires native validity, a live invocation
  and that invocation's pending priority reservation. The spatial Pre also
  requires the platform-running and critical-outside resources; TCBInit does
  not establish these entry resources for an arbitrary caller.
- Detach, private initialization and publication are actual proved updates.
  `task_tcb_init_published_result` obtains post-validity from the commit
  preservation theorem; the publication proof reconstructs the written list,
  priority table, ready bytes and task count before merging the spatial
  invariant. These local steps do not assume their own valid post-state.
- Success describes the last release's publication snapshot, not perpetual
  liveness of the new task after interference. Error 66 retains the pending
  reservation and rollback guard; the caller must perform the rollback.
- Save/Restore remain explicit platform/CSL callee contracts. The concrete
  region interpretation, source-trace coverage, continuation restoration,
  real Create caller and the other native clients are linking obligations.
  The four creation-transformer certificates are not certificates for every
  Task API: `NativeRetire` retires an invocation, not a C TaskDelete proof.
- The selected empty/forwarding hooks match their direct frame effects, but
  six hook obligations in canonical `task_tcb_init_proof_auto.v` remain on
  the existing auto/tool-trust side, not kernel-Qed manual proofs. Neither
  custom hooks nor an admission-free whole-kernel result is claimed.

Known invalid Mutex transitions prevent the corresponding native client
certificates; they do not by themselves prove every TCBInit entry false. A
Boot state with no used events, initialized free images and one pending
reservation provides a static pure-state construction argument. No complete
spatial-Pre inhabitance or actual source-startup/platform-instance theorem was
established by this read-only audit. Keep that distinction visible in delivery;
do not replace the missing instance with identity-only interference or a
transition guard that merely demands a valid endpoint.

## Shared invariant changes required by real source

- **Reservation provenance.** Current `cross_module_invariants.v` interprets
  every PTReserved slot as a mutex reservation. Native creation introduces a
  second, disjoint cause bound to the creator's original invocation. The
  pending-resource ledger must survive deletion of that creator: the C delete
  path does not reclaim another invocation's reservation or detached TCB.
  Separate historical resource ownership from permission to resume, and do
  not let address reuse revive a retired invocation. Extend the
  ownership relation and prove both operation families preserve it; replacing
  the branch by True would lose the protocol.
- **Priority domains.** `task.v::valid_task_prio` and
  `stable_glob_vars.v::valid_priority_index` use `< osLowestPrio`. A full kernel
  contains idle priority 63, and Create's actual guard is `prio > 63` despite
  its nearby comment. Separate native table/task domain from per-API and mutex
  PCP guards; do not globally loosen all uses of the old predicate.
- **Pool and list closure.** Current task validity has free-list NoDup and
  used/free disjointness, but no complete partition including initializing
  nodes, exact active-list traversal, next/prev symmetry or count/cardinality
  equation. Bind each published node to exactly one list occurrence; exclude
  privately initialized nodes from public lookup and ready membership.
  OSTimeTick traverses until the idle-priority node rather than until NULL, so
  the post-initialization list protocol must establish a reachable final idle
  sentinel and preserve it. Bootstrap stages before idle creation are distinct
  from the running-kernel invariant.
- **Exact field encoding.** `OSTaskDelReq` writes OS_ERR_TASK_DEL_REQ = 63
  (`ucos_ii.h:286`, `os_task.c:656`); `task.v::encode_bool` currently maps true
  to 1. Add a source-correct delete-request encoding rather than changing all
  unrelated boolean encoders. Model Name, Register and Stack query outputs from
  their actual fields, with the complete memory ownership described above.
- **Ready state versus cached selection.** A physical high-ready cache is not
  automatically rewritten when a task's priority, suspension or ready status
  changes. Keep logical ready ordering, actual bitmap bytes, current context,
  and possibly stale high-ready cache distinct until the actual selection
  writes execute. Updated logical selection alone cannot discharge refresh.
  Native bootstrap also needs an exact spatial encoding: the pinned
  `OS_InitRdyList` writes both priority scalars as zero and both TCB pointers
  as NULL. The historical `sched_current_consistency` forces a missing current
  task to have `curSchedPrio = None`, while `store_sched_state` and
  `sched_raw_rep` encode that priority as 255 and task pointers through the
  68-byte `tcb_addr`. Consequently the new native pure predicate cannot simply
  reuse those historical spatial predicates. Bind native pointer layout and
  actual bootstrap scalar bytes explicitly without changing the old slice's
  claim. For cache refresh, `OS_SchedNew` writes only `OSPrioHighRdy`; its
  caller `OS_Sched` then writes `OSTCBHighRdy`. A mathematical transformer
  updating both is a completed two-write stage, not either individual write.
- **Lifetime and invocation.** Source interference must preserve the original
  invocation across Restore/schedule, or explain why it cannot return. A reused
  TCB address is insufficient. Establish tokens at allocation/entry, transport
  them through each source action, and retire them at deletion/return; do not
  add validity only as an endpoint filter.

The two unguarded Register APIs and the unbounded StkChk scan remain separate
public-domain/source obligations in `task-function-intake.md`. They cannot be
made safe by the publication patch or by claiming every in-range priority is
live. Similarly, native flags are enabled: owning FlagNode/FlagsRdy bytes does
not prove the missing flag-module lifecycle protocol.

Mutex documented-use boundary: `os_mutex.c` explicitly forbids an owner from
pending on another event or having its priority changed by clients, and Del's
ALWAYS note requires a ready owner. The inherited shared model admits a wider
defensive cross-object domain; the user has now selected documented use for
the current claim. An owner/other-event timeout trajectory in the wider domain
is not a counterexample to documented use. Conversely, a source comment is
not a proof that every modeled environment action establishes/preserves the
protocol. Make the appropriate caller and environment obligations explicit
and prove their required transport. This does not remove the independent Task
representation or physical cache refresh obligations.

### Native scheduler source bridge audit (2026-09-08)

The frozen Task r2 model contains native ready/cache/table representations and
the corrected unsigned switch counter, but this does not yet prove the C
selection sequence. Source `os_core.c:1702,1751` executes:

`Save -> nesting gates -> bitmap lookup -> write OSPrioHighRdy -> priority-table lookup -> write OSTCBHighRdy -> compare priorities -> optional switch -> Restore`.

- `native_sched_raw_rep` owns the ready group and eight OR-encoded row cells;
  `native_store_prio_tbl` owns the 64 native-pointer entries. Expose the chosen
  row and table cell with reversible splits. The address `g_OSUnMapTbl` alone
  is not the read resource or contents of the real 256-byte constant table
  (`os_core.c:47`, declaration `ucos_ii.h:778`).
- On a nonempty valid ready set, prove the two lookups produce the head's
  priority and the table produces that head's native TCB pointer. Reuse
  bit-disjointness, division/remainder and priority-registration facts. The
  legacy `mutex_del_first_set8` defaults to 7 on zero, whereas the real lookup
  table returns 0 at index 0; a bridge must retain its nonzero premise. Do not
  make the lower scheduler module import a higher MutexDel spec to reuse it.
- Both cache writes occur in the enabled branch, including no-switch. Carry
  the intermediate state after the priority write and before the pointer
  write. Equality of old/new final values can simplify a state equation, not
  remove these source steps. Native `None` and `Some 0` priority observations
  encode the same scalar byte, so byte equality does not imply option equality.
- The actual switch test is `OSPrioHighRdy != OSPrioCur`, not `<`. A blocked
  current task at priority 5 and a ready head at priority 20 still require a
  switch. Relate the abstract guard to this byte comparison using the actual
  current observation, head readiness and priority uniqueness, not a stronger
  invented C guard.
- The native candidate's `atomic_sched` still returns whole-state identity
  for empty-ready, missing-current and missing-lookup cases. C has no such
  tests: an all-zero bitmap selects priority 0, then reads table slot 0; its
  pointer is NULL only if that slot is actually free. Likewise
  `native_task_idle_tail` establishes list position and idle priority, not
  idle readiness. Close these cases through source-established caller/boot
  protocol or an accurate source transition; do not assert nonempty ready
  merely from idle-tail or equate bootstrap initialization with scheduling.

The array, two-write and comparison bridges can be developed independently of
FPU/BSP selection. Protected execution, the real context-switch footprint and
return of the original invocation remain the separate N8/N6 boundary. This
audit records unclosed consumers; it neither changes source/configuration nor
claims a new implementation bug.

## Owner and consumer plan

One annotation owner must receive exact controller authorization before changing
shared definitions. The following is a design map, not an allowlist:

| Owner | Responsibility |
|---|---|
| stable_glob_vars.v | Selected task/table domains and additional actual global addresses such as task-register allocation state |
| ucos2_verify_state_def.v | Complete Task observations, pending publication/reservations and lifetime identities; preserve semantic projections |
| task.v | Native representation, complete free storage, list/pool/priority relations, split/original-merge/updated-merge |
| sched.v | Ready representation, cache phases and actual current-context relations |
| cross_module_invariants.v | Task/mutex reservation provenance, wait/ready relations and preservation |
| event_wait.v, event.v, tick.v | Wait membership, encoded bytes and timeout/cleanup transport |
| atomic_ops_lib.v, ucos2_verify_inv.v, ucos2_rules_lib.v | Source action composition, global framing and invocation-aware Restore/schedule interfaces |
| error_codes.v | Selected Task error constants when introduced; do not copy drifting numeric encodings into each case |
| Each Task/Queue/Mutex case spec | Exact ordered public semantics and consumers of the shared interfaces, not duplicate shared definitions |

The r2 MutexDel audit determines its additional exact consumers. The archived
QFlush r4 candidate is a source of proposed repairs, not current acceptance.
Do not overwrite accepted reports or mechanically copy that tree into main.

Current-main constructor audit: literal TaskAbstractState construction occurs
in atomic_ops_lib.v, mutex_func_sem.v, mutex_rdyatprio_spec.v,
mutex_post_spec.v, mutex_del_spec.v and sem_pend_spec.v. Literal global Task
construction additionally occurs in mutex_create_spec.v,
sem_pend_abort_spec.v, event.v, task.v, cross_module_invariants.v and sched.v.
Adding fields without transporting them in these updates would drop unrelated
state or leave the consumers ill-typed. Prefer canonical field-update/frame
interfaces; inspect the selected retry baseline again for its own consumer
delta instead of treating this main-snapshot list as complete authorization.

Before any main application, distinguish the native profile from the historical
68-byte verification slice in source/version bindings. A genuinely proved
layout-parametric interface may support both; a boolean label without a
representation/refinement theorem cannot. A new native Task C target must be
created through controller intake. Its integration cannot silently alter the
fixed executable tokens of the current MutexDel attempt or inherit old proof
acceptance. Reuse unchanged mathematical proof text through the existing
controller mechanism and fresh-check changed consumers only as required.

### Compatibility consumers before main application

The 2026-09-09 read-only comparison uses the Task annotation r5 candidate and
current main HEAD, not historical acceptance as evidence for either version.
At the time of that comparison the candidate remained isolated. Its TCBInit fixed group check imports the
current Task goal/auto/manual and case spec; the case spec imports the shared
Mutex/Sem specs, but neither it nor their library closure imports the existing
Mutex/Sem manual modules. Passing that check therefore covers the required
shared specs, not migration of those old manual proofs.

Keep three distinct issues in the eventual consumer repair batch:

- **New record/frame obligations:** `TaskAbstractState` adds `taskGeneration`
  and `taskNative`; global Task state adds `taskLifecycle`; global Event state
  adds `publishedQueueBytes`. Candidate shared transformers mostly carry
  these fields unchanged. The direct manual-sensitive sites include
  `VC/code_proof/mutex/post_full_proof_manual.v:863` (old Task destructuring)
  and `:1139` (explicit reserved-table record without a lifecycle field).
  The Queue follow-up also found
  `VC/code_proof/queue/spec/q_create_spec.v::q_create_event_state`: its Event
  record must account for `publishedQueueBytes`; its success-state and
  `q_create_proof_manual.v` return/merge steps are actual consumers.
  Check the intended field/frame equality in the new version; this source
  inspection is not a claim that a compiler has rejected the old text.
- **Actual shared transition changes:** candidate `atomic_ops_lib.v::atomic_sched`
  refreshes the high-ready cache even on its applicable no-switch branch and
  wraps `ctxSwCtr` modulo 2^32. This is not merely record plumbing. Relevant
  consumers include Mutex Post's handover validity, Mutex Del's waiter-map
  frame, and Sem Post/PendAbort/Del's Task/Event/interrupt frame reasoning.
  Candidate shared preservation lemmas may allow existing proof bodies to
  replay, but preserving those properties is not equality of the entire old
  transition or a native `OS_Sched` source-refinement proof.
- **Pre-existing main consistency debt:** current main `event_wait.v` already
  has the four-part `event_wait_object_consistency`, including reference
  backlink consistency. `VC/code_proof/sem/accept_proof_manual.v:279` and
  `VC/code_proof/sem/set_proof_manual.v:492` / `:882` still use the older
  three-part decomposition and closure step. The r5 `sem_create_spec.v`
  adaptation does not cover these manual consumers. Do not misattribute this
  existing mismatch to a newly added r5 conjunct.

QueueCreate needs two distinct claims, not a field-only shortcut. Framing
`before.publishedQueueBytes` may preserve its legacy projection contract, but
does not establish native creation: the new Queue needs its physical buffer
snapshot registered while other Queue entries are framed. The existing
`q_create_world` / success world supply `PtrArray.full start size buffer` as
a snapshot source. Native publication needs a creation-specific storage merge,
not `native_queue_storage_frame` (which forbids adding a Queue), and must
transfer rather than duplicate the standalone QCB/buffer ownership into
`native_queue_storage_rep`.

The QueueInit review found no direct Task/Event record construction or
destructuring and no change to its consumed local clearing/free-list
definitions. This does not turn its local proof into a native initializer:
the empty published-bytes map and complete global pool partition remain
separate producer obligations. Do not edit or rerun that unchanged local
proof merely to complete a compatibility checklist.

The legacy `UCOS2_Verify_inv` / `task_inv` interfaces still describe the
verification slice; the new native interfaces do not automatically grant old
clients a native layout or source certificate. Before treating a shared-model
application as a compatible integrated result, discharge the affected consumer
obligations through their authorized case paths. Preserve old accepted bytes
and versioned results; do not silently overwrite another case's manual, inherit
its acceptance, or rerun an unrelated unchanged old version. This note is
static impact analysis only: no old Mutex/Sem compilation was performed.

Verification order: representation and private-allocation split/merge;
reservation/detach/init/commit/rollback; complete publication preservation;
invocation-aware source resumption; MutexDel's independent encoding/cache
closure; then the two Queue batches. Run canonical symbolic execution only once
the independent source/model deficits have a coherent candidate. Whole-target
VC triage remains mandatory before deciding the next annotation repair batch.

## Authorized completed-function migration (2026-09-09)

The user has authorized repair and now set the active objective to adapting
all previously completed function proofs to the new Coq model. This resolves
the earlier pending permission for the affected case specs/manuals and the
separate Mutex implementation repair. Exact formal write paths still come
from fresh controller handoffs; frozen old reports and accepted worktrees
remain unchanged.

Controller `final-apply` for `task_tcb_init-20260908111228` has applied the r2
merged candidate and its 22 changed shared semantic files to main. Its
required isolated canonical freshness and fixed full Rocq final check have
passed, and the controller has recorded `done`. This closes the scoped
TCBInit delivery, with the trust and linking limits stated above. Old case
results are versioned evidence, not acceptance of this newly applied model.

The migration scope found in the current main proof files is:

- Mutex: Accept, Create, Delete, Post, Query and RdyAtPrio (the internal
  priority helper). Delete has 85 closed manual bodies, but its historical
  controller run remains pre-final after a separate fast-apply operation;
  this discrepancy must not be reported as controller `done`.
- Semaphore: Accept, Create, Delete, Pend, PendAbort, Post, Query and Set.
- Queue: Init and Create.
- Task: TCBInit, with 19 completed manual targets and controller final delivery.

MutexPend still contains admissions and is not a previously completed
function. This inventory does not make unfinished Queue/Task APIs completed.

For each existing function, retain its ordered public input/output contract,
carry every new field that is outside its mutation footprint, and prove the
new affected invariant/transition obligations. Compile success after adding
record fields is not by itself semantic compatibility. In particular,
QueueCreate must account for new published buffer storage, and the confirmed
nested Mutex restore collision cannot be hidden by a stronger unsupported
precondition. Keep native and legacy layout/callee claims distinct.

Start independent SemAccept/SemSet case migrations without shared-model
writes. Their known wait-reference backlink obligations can be repaired in
their own proof groups; annotation owners first audit the entire current
function and seed against the new dependencies. Reuse explicitly allowed
historical proof text only as a method hint. Other cases remain in scope,
including necessary replay of source-sensitive scheduler consumers. An
unchanged local QInit theorem is not rerun merely for this inventory; its
actual dependency/claim coverage must determine whether further checking is
needed.

Fresh migration runs are `sem_accept-20260909091253`,
`sem_set-20260909091336`, `q_create-20260909091708`,
`sem_post-20260909094925`, `sem_query-20260909110506`,
`sem_create-20260909113304`, `sem_pend_abort-20260909121312`,
`sem_del-20260909121753` and `sem_pend-20260909121937`. Their current
controller reports, not this note, determine completion. SemAccept, SemSet and
QueueCreate have accepted current VC plans and independent proof groups.
SemAccept, SemSet, SemPost and QueueCreate have passed group acceptance, independent parent
verification, protected main application and isolated final checking; all four
controllers now record `done`. SemSet's first parent merge rejected five
manual-proof scan locations using the canonical forbidden `derivable1_trans`;
there were no unsolved targets or semantic blockers. Controller created
proof-only round r2 against the same annotation and target set, preserving the
old artifacts and staling their acceptance. Its seven proofs were replayed
with direct structural steps, and r2 passed every fresh group/parent/final gate.
Its C implementation/annotation remained unchanged; two proved suffixed helpers
were added to the existing case spec.
SemPost annotation has been accepted without C/spec edits; fresh proof work
completed all nine targets and twelve helpers, and controller group acceptance
passed. Independent parent verification, protected final application and isolated
final checking also passed; its nine manual targets are delivered against the
current post-TCBInit shared model, with nineteen canonical auto/tool-trust
obligations. Its C implementation and annotation remain unchanged. SemQuery's unchanged C/spec
and sixteen-target plan are accepted; its two independent proof groups (five
copy-loop targets and eleven event/return targets) have both returned completed.
Controller accepted both groups after independent fresh checks; deterministic
parent merge and full verification are running. SemCreate's
ordered free-Event detach, private initialization and exact publication audit
passed annotation acceptance without C/spec changes; VC checking is prepared.
SemPendAbort is prepared with the current eighteen read-only shared
dependencies, including exact broadcast cardinality, suspended/expired waiter
behavior, entry-anchored cache ownership and Restore-before-scheduler order.
SemDel and SemPend are also prepared, not yet proved: the former must discharge
all live Event-reference closure before reclamation, and the latter must justify
the same task's blocking/resumption and literal final status stores without
assuming a suspended task can return from the scheduler. Each registers its
current eighteen shared dependencies read-only; none authorizes sibling or
main shared-model edits. These prepared runs remain queued while the known
cross-module repair batch is brought to a coherent source/model candidate;
they are not silently counted as completed or restarted on old dependencies.
QueueCreate's accepted annotation carries
the same successful buffer into publishedQueueBytes and its separately proved
native-storage consequence. These four completed migrations do not complete
the remaining twelve previously completed Mutex/Sem/Queue functions, nor do
they certify a future changed cross-module invariant.

The scoped delivery counts are 6 manual `Qed` targets plus 11 canonical
auto/tool-trust obligations for SemAccept, 7 manual `Qed` targets plus 13
canonical auto/tool-trust obligations for SemSet, and 8 manual `Qed` targets
plus 25 canonical auto/tool-trust obligations for QueueCreate; SemPost adds
9 manual `Qed` targets and 19 canonical auto/tool-trust obligations. The auto modules still
use the existing generated `Admitted` interface implementation; their fresh
canonical binding is not a claim of kernel-checked proof for those obligations.
No admission was added to the manual or case-spec proofs. SemAccept and SemSet
retain their explicit critical-section contracts and verification-slice scope.
QueueCreate retains its external
Save/Restore and wait-list initialization contracts, and its native-storage
consequence does not identify the legacy Event/TCB representation with a fully
proved native global invariant or ARM/BSP implementation.

The separate Mutex nested-priority source candidate and executed regressions
are documented in [its source-variant README](../../source_variants/mutex-nested-priority/README.md).
They do not modify these runs' shared snapshots. Source binding and the full
alias/invariant/caller adaptation still require a fresh authorized semantic
batch; neither a host regression nor one ready group is overall completion.
Native helper run `mutex_priority-20260909114354` now binds the repaired
RdyAtPrio and its two actual priority-table scan dependencies as the next
Mutex proof prerequisite. It does not replace completion of the six previously
proved Mutex functions or certify their old verification-slice artifacts.
Its annotation has passed controller acceptance after preserving byte ranges
across bitmap writes and correcting an `InsideCritical` import collision.
The twenty-five nonsplit manual targets passed full VC triage with no upstream
gap, and the three-group plan (eleven scans, nine field/encoding targets and five
bitmap/return targets) is accepted. Controller has accepted all eleven scan
targets; the field/encoding and bitmap/return groups are running. This is not
whole-helper or public Mutex completion.
Its annotation r1 and run-init main baseline use the registered module-local
`VC/code_proof/mutex/spec/mutex_priority_spec.v` and
`Ucos2Verify.VC.code.mutex` route. The prior `mutex_priority-20260909111451`
was initialized before that route was registered; changing its r2 handoff
could not repair the immutable run-init baseline. Its owner froze the draft,
and the new run permits only those exact C-annotation/spec paths as advisory
references. This is a corrected binding of the same helper task, not another
proof target or transferred acceptance.

Following the user's concern about repeated model adaptation, fresh run
`del_full-20260909131500` now binds current main and twenty-eight exact read-only
shared dependencies. Its annotation owner is performing the pre-generation
audit specified in the current convergence section of
`mutexdel-shared-repair-intake.md`: identify all remaining source/model causes
and the actual shared owner/consumer write set without editing formal files or
regenerating the known-mismatched old Delete candidate. The approved eventual
source choice is the native nested-priority repair, not an unannounced
one-held-Mutex restriction or identification of the legacy and native layouts.
Main will review that current request and use the normal controller-authorized
continuation. Existing live proof checks finish on their isolated versions;
remaining bulk migrations wait for the shared candidate instead of repeatedly
adapting against a knowingly intermediate cross-module invariant.
