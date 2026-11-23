# Mutex nested-priority repair candidate

This is a separately named implementation candidate for the repair authorized
on 2026-09-09, not a controller-accepted proof or an edit of an earlier result.
Apply `os_mutex.patch` directly to the pinned `Source/os_mutex.c` selected by
[profile.json](../../config/queue-v2.93.01-first-round/profile.json). It includes
the conditional-current scalar correction; do not stack the scalar-only patch.
The original checkout, scalar-only variant, native intake target and all existing
formal source bindings remain unchanged.

## Concrete algorithm and observations

The source already retains a task's permanent priority-table entry while adding
lower-numbered entries for Mutex inheritance. This candidate uses those actual
entries, not the saved low byte of another Mutex, to select priorities:

- `OSMutex_BasePrio` scans the real bounded table and returns the greatest index
  containing the owner's TCB. Under the alias/lifetime invariant below that is
  its permanent task priority, not its current inherited priority.
- `Pend` compares the waiting task with this base. It additionally records a
  qualifying Mutex ceiling alias when a different held Mutex already supplies
  an equal or higher effective priority. The new guard excludes ceilings that
  are not numerically below the base. Thus recording a masked demand cannot
  redefine the permanent slot.
- Successful Post or Delete first releases only this Mutex's enabled ceiling
  slot (reserved for Post, free for Delete). `OSMutex_EffectivePrio` then selects
  the least remaining table index containing that owner. Restoration never
  follows the stale acquisition-time low byte into another task's slot.
- `OSMutex_RdyAtPrio` preserves the owner's actual ready-bit membership. A
  suspended/non-ready owner is relocated but is not made ready. Only relocation
  of `OSTCBCur` changes `OSPrioCur`. The helper does not mutate Event wait lists;
  its owner-use contract must establish their absence for the owner.

The two scans use `INT16U` indices and the inclusive `OS_LOWEST_PRIO` bound.
The selected profile has 64 entries. Neither the disabled ceiling tag 255 nor
an out-of-range entry is indexed by release. A scan's literal fallback is the
current priority; proving the permanent slot exists must make that fallback
unreachable for a valid owner. The fallback is not error recovery or a closure
assumption.

Create, Accept and Query executable bodies are unchanged. In particular, the
low byte remains the actual acquisition/handover priority snapshot exposed by
Query. No native TCB/ECB field, structure size, configuration constant, public
error code, no-change error guard or additional scheduler call is introduced.
Pend's contested-owner behavior and both release paths intentionally change;
this is not equivalence to the defective source.

## Invariant and integration obligations

These are obligations for the next authorized shared-model owner, not added
Coq assumptions or proof claims:

1. Every live task has one permanent table slot. All additional aliases are
   lower-numbered enabled ceilings of live Mutexes owned by that same task.
   An enabled ceiling remains either reserved or an alias of its actual owner;
   the permanent slot is not a Mutex ceiling or a private creator reservation.
2. The current effective priority is the least of the permanent slot and its
   outstanding recorded inheritance aliases. Acquiring another Mutex preserves
   this fact while taking a separate current-priority observation. Release
   removes only the released alias, including non-LIFO and noncurrent cases.
3. The owner does not pend on another Event, its priority is not changed by
   TaskChangePrio while it owns a Mutex, and its TCB is not deleted/recycled
   before all ownership is released. NO_PEND does not require a ready owner.
   TaskCreate/TCBInit, TaskChangePrio and TaskDelete remain real lifecycle
   consumers; a ghost reservation cannot replace a physical table entry.
4. The stored demand is latched by an actual qualifying Pend, not defined as
   “every Mutex currently held” or “every presently linked waiter”. Like the
   original source, timeout does not immediately remove an inherited ceiling.
   TaskChangePrio can change a *waiting* task's priority without re-running the
   Mutex promotion code. A blanket all-live-waiter inheritance theorem therefore
   needs its separate source/call-contract analysis; these tests do not prove
   that stronger claim or silently prohibit such calls.
5. Model the changed C order: slot release, remaining-alias scan, optional
   ready-preserving relocation, then wake/owner/count/free-list stores. Reuse
   exact EventTaskRdy semantics, including NULL message, suspension and
   expired-but-still-linked waiters. Refresh of high-ready caches belongs to
   the real scheduler call, not these helpers.

The current `mutex_owner_consistency`, `priotbl_consistency` and restore helpers
still use legacy per-Mutex original/PCP equalities. They do **not** model this
algorithm. Their replacement must preserve a coherent single Task/Event state,
source initialization and alias lifecycle, rather than adding a one-held-Mutex
precondition. The whole current Mutex family and any affected already-proved
consumers require a fresh controller-bound semantic version. Do not overwrite
the active Sem/Queue workers' shared snapshots or relabel their evidence.

## Executed host regressions

The following commands execute the actual patched source with the existing
host `ucontext` fixture, separate saved call stacks and interrupt-status values:

```sh
bash uC-OS2_verify/tests/mutex_current_priority/run_nested.sh --repaired
bash uC-OS2_verify/tests/mutex_current_priority/run_nested.sh --repaired --post-only
bash uC-OS2_verify/tests/mutex_current_priority/run_nested.sh --repaired --masked-demand
bash uC-OS2_verify/tests/mutex_current_priority/run_nested.sh --repaired --no-pend-suspended
```

All four exited 0 under host UBSan on 2026-09-09, without sanitizer diagnostics:

| Trajectory | Observed repaired result |
|---|---|
| Delete M1, reuse its slot for N5, then Post M2 | O returns to 20; N remains the unique task at 5 and retains table[5]; actual Pend abort/success and Post continuations complete |
| LIFO Post with two outstanding boosts | Releasing PCP3 retains O5 while M1 still has waiter 10; ready task 15 does not overtake O |
| Lower ceiling demand arrives while O3 is suspended | Pend records M1's masked PCP5 alias; explicit Resume and later Post retain O5 |
| Suspended owner; last waiter times out and unlinks; NO_PEND | Owner moves from 5 to 20 while remaining suspended/non-ready; only later explicit Resume readies it |

`bash uC-OS2_verify/tests/mutex_current_priority/run.sh --nested-repaired`
also passed the four existing helper and eight Delete/wake/scheduler cases
against this new variant under UBSan. This checks current/noncurrent cache
behavior, ready-table updates and ordinary/suspended/expired waiters without
rerunning the unchanged original and scalar-only versions of those 12 cases.

The scalar-only mode remains available without `--repaired`; it reproduces the
two original nested failures, the masked-demand failure and the original native
NO_PEND missing restore. The NO_PEND negative is **not** execution of the distinct
already-patched `_full` verification slice. That slice's suspended-owner concern
and the new native repair must not be conflated.

Startup uses actual static initialization helpers and API-created tasks, not
complete OSInit. Creation hooks, stack setup and low-level switches have explicit
host contracts; the timeout trajectory additionally uses a no-effect host tick
hook. This is not the ARM timer/BSP implementation. All kernel Task/Event/table
mutations in these trajectories come from kernel APIs. Host ABI is not an ILP32
layout proof. No QCP VC, Rocq proof, full interference coverage or formal acceptance
is implied by these successful regressions.

## Native helper intake and parser check

[OSMutex_Priority.c](../../annotated_C/src/mutex/OSMutex_Priority.c) contains
the actual three static helpers and selected complete native TCB, without
invented external callee contracts. It is a new intake, not a replacement of
the old scalar-only helper target or an accepted formal dependency yet.

```sh
python3 uC-OS2_verify/tests/mutex_current_priority/check-native-source.py --variant mutex-nested-priority
python3 uC-OS2_verify/tests/mutex_current_priority/test_native_source.py
```

The positive check passed complete preprocessed function/TCB token comparison,
eight scalar aliases, GCC freestanding ILP32 size/alignment/field offsets and
global types. All nine source-checker negative tests passed, including rejection
of lost ready membership, changed maximum/minimum scans and the three original
guard/layout mutations for both variants. The unchanged scalar-only intake's
positive check also still passes. These checks consume source bytes directly
without new SHA-256 scans.

QCP MCP parsed this intake successfully with explicit Arch32/little-endian,
the `QCP_demos_LLM` include/SLP and `uC-OS2_verify` SLP, and logical path
`Ucos2Verify.VC.code.mutex`; the diagnostic session was then closed. The current
backend policy is parse-only because of its known interactive regression.
No disabled interactive command was used. Parsing shows that these C constructs
can enter the front end, not that annotation, symbolic execution, global
invariant closure or any of the three helpers has been proved.

The current controller intake is `mutex_priority-20260909114354`, binding this
C file and the current Task/Scheduler dependencies read-only. It must first
prove the three exact native helpers (including the literal no-alias scan
fallback) and their full physical frame. Global alias/minimum interpretation
and public Delete/Post composition remain separate required work, not extra
guards inserted into the helpers. Its current controller report, not this
README or the existence of the run, determines proof progress and acceptance.

The preceding `mutex_priority-20260909111451` was initialized before its
controller source route was registered. Its r2 handoff corrected the module
paths, but the immutable run-init main baseline still named generic example
paths and could not support final application. That configuration is not a
semantic VC gap or proof evidence. The corrected run binds all eight proper
module-local final targets from initialization and explicitly permits only the
old owner's frozen C-annotation/case-spec drafts as non-authoritative references.
No old baseline or report is rewritten, and all required generation/checks must
be performed against the corrected run's own sources.
