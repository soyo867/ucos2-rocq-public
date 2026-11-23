# Mutex current-priority source variant

Variant ID: `mutex-current-priority`. On 2026-09-08 the user authorized the
choice after distinguishing a repaired implementation from verification of
unchanged source under a caller protocol. This is source-repair material,
not a controller-accepted C proof or a change to any sealed earlier result.

Base: the exact uC/OS-II revision and configuration selected by
[the existing profile](../../config/queue-v2.93.01-first-round/profile.json).
Only `Source/os_mutex.c::OSMutex_RdyAtPrio` is patched. Keep the pinned checkout
unchanged; apply the patch to a temporary copy for diagnostics and bind the
chosen variant explicitly in the next applicable controller source version.

## Exact effect and reuse

Update `OSPrioCur` only if the helper's `ptcb` is `OSTCBCur`. Preserve every
other TCB, ready-bitmap and priority-table write in its original order. This
is the same condition already present in the separate verification target
`annotated_C/src/mutex/OSMutex_RdyAtPrio_full.c`; do not insert it twice or
mistake that target's old verification-slice proof for a native-layout proof.

The change is intentional, not equivalence with all original executions:
restoring a noncurrent owner's priority no longer overwrites the current
task's priority scalar. The source's Post call passes `OSTCBCur`, so the new
condition preserves that helper path; Delete can pass another task. A
scheduler lock can keep the original mismatch visible through Delete's return.
With no initial waiters, Delete does not call the scheduler at all, so the
mismatch can also survive an unlocked return. When initial waiters exist and
scheduling is enabled, the original mismatch can cause an unnecessary
same-task switch and different switch-count/hook observations.

## Remaining proof obligations

- Bind the actual static native helper to the callee contract used by Delete
  and Post. The external declaration in `OSMutexDel_full.c` is not that proof.
- Cover current and noncurrent ready owners, exact bitmap/table updates and
  untouched Event wait bytes. Keep current selection separate from the
  independently refreshed high-ready cache.
- Keep the documented owner-use protocol explicit. The upstream ALWAYS
  ready-owner requirement does not automatically cover the repaired NO_PEND
  branch with a suspended owner. This patch does not fix that separate case.
- Retain the handover/suspension, nested-owner and lifetime obligations in
  [the shared repair intake](../../config/queue-v2.93.01-first-round/mutexdel-shared-repair-intake.md).
  Do not turn them into invented executable guards or silently claim that
  all native kernel operations now preserve the global invariant.

The source patch, any host diagnostic and the existing `_full` artifact are
distinct evidence. Formal acceptance still requires the current source-bound
QCP/Rocq checks and controller review; no unchanged old proof is recompiled
merely to describe this variant.

## Targeted source-execution diagnostic

Run `bash uC-OS2_verify/tests/mutex_current_priority/run.sh` from the repository
root. The runner checks the pinned revision and clean relevant sources/config,
applies the patch only to a temporary copy, and includes the actual original
or patched static helper with the selected native declarations. It does not
replace the helper with a handwritten implementation.

On 2026-09-08 both variants completed four cases each under host UBSan with
exit status 0 and no sanitizer diagnostic: current/noncurrent owner crossed
with same-row/cross-row priority restoration. The original run explicitly
expects and reproduces the noncurrent scalar mismatch; the repaired run
requires current-pointer/priority consistency. Both check exact ready rows,
group and priority-table values, and unchanged high-ready pair, nesting
counters and context-switch count. This first fixture calls the helper
directly; it does not execute Delete or Post.

The second fixture, `tests/mutex_current_priority/del_scheduler.c`, executes
the actual `OSMutexDel(OS_DEL_ALWAYS)`, `OS_EventTaskRdy`,
`OS_EventTaskRemove`, `OS_Sched` and its real lookup table from the pinned
`os_mutex.c`/`os_core.c`. Only Save, Restore and context-switch entry have
explicit host stubs. Eight cases per source variant cross scheduler
locked/unlocked with no waiter, ordinary pending waiter, suspended waiter,
and already-ready timed-out but still linked waiter. Both variants completed
with exit status 0 and no UBSan diagnostic on 2026-09-08. Together with the
direct helper fixture, the runner executes 24 cases.

- Original-source expectations reproduce the wrong current scalar at the
  first Restore, its persistence when there is no scheduling, and a spurious
  same-task switch request/count increment when the scheduler does run.
  The repaired-source expectations exclude those effects in these cases.
- Both variants check exact ready rows/group and priority-table bytes,
  deletion/free-list results, the source's NULL-message and pend-abort writes,
  suspended non-readiness, idempotent ready-bit insertion for an expired
  linked member, and an unrelated Event/waiter's unchanged representation.
- The initial high-ready pair already selects the current task. The final
  equality check does not prove whether the two cache stores occurred;
  their actual enabled/disabled control flow is read from `OS_Sched` and
  remains a distinct formal bridge obligation.

These are specified-state host execution diagnostics, not a proof of state
reachability, all Delete branches, Post, interleaving coverage, the platform
stubs or ARM ABI. The context-switch stub records the request and assigns the
selected current pair; it does not run the real stack switch or App hook.
No native Task publication variant is needed for the exercised call chain;
unrelated `os_core.c` code is discarded at link time. The pinned source and
old accepted artifacts remain untouched.

## Independent nested-restore counterexample

Run `bash uC-OS2_verify/tests/mutex_current_priority/run_nested.sh` separately;
it does not rerun the earlier 24 cases. It uses the approved conditional-current
Mutex variant, unchanged pinned `os_task.c` and `os_core.c`, and actual
Create/Accept/Pend/Delete/Post/Suspend/Resume calls. Host `ucontext` stacks
preserve each blocked C continuation and its saved interrupt-status state.
The fixture never fabricates TCB, priority-table, ready or Event wait updates.

On 2026-09-09 the diagnostic reproduced a distinct remaining bug under host
UBSan, exit 0 with no sanitizer report: an owner acquires M2 while inherited
at priority 5; deleting M1 restores the owner to 20 and frees slot 5; a new
task occupies that slot; a later M2 promotion and Post restore the owner to 5
and overwrite the new task's table entry. Both different TCBs remain in the
active list with priority 5. Nine real scheduler-selected host context switches
also check the original Pend/Post continuations, including the deleted M1's
waiter returning `OS_ERR_PEND_ABORT` and M2's waiter returning `OS_ERR_NONE`.

This test succeeds by observing the counterexample, **not** by establishing
kernel correctness. Owners stay ready, never pend another Event and never
invoke TaskChangePrio; the documented owner-use protocol does not exclude
this sequence. No additional implementation patch has been selected here.
The conditional-current fix therefore must not be described as repairing all
nested-Mutex priority-table/lifetime behavior.

Startup uses the real static initialization helpers and API-created tasks,
not full configured `OSInit`. Stack setup, empty creation hooks, interrupt mask
and context switching are explicit host contracts. The runner uses the host
compiler ABI, not `-m32`, and makes no 64-byte TCB-layout claim. This is a source/API
counterexample from that initialized state, not ARM/BSP execution, complete
boot reachability, a formal proof or a change to any sealed verification result.

### Post-only inheritance counterexample

Run `bash uC-OS2_verify/tests/mutex_current_priority/run_nested.sh --post-only`
to select the independent no-Delete scenario without rerunning earlier cases.
O20 first accepts M1/PCP5 and M2/PCP3, so both saved priorities are 20. W10
then pends M1 and promotes O to 5; W4 pends M2 and promotes O to 3. O releases
M2 first (LIFO), but the actual Post restores O to 20 despite W10 still waiting
on M1. After W4 releases M2 and suspends, a ready priority-15 task runs ahead
of O; the original Post-M2 continuation later returns `OS_ERR_NONE`.

On 2026-09-09 this diagnostic exited 0 under host UBSan with nine task switches
and no sanitizer diagnostic. It checks M1's owner, live wait bitmap and Task
backlink, both original Pend returns, and the owner's original Post return.
The same source/configuration and explicit host startup/context boundaries
apply. No task calls Delete or TaskChangePrio, and the owner never pends another
Event. This is an observed priority-inheritance failure, not a second table
overwrite, an ARM/Rocq proof, or a nested-inheritance repair. The existing
scalar-only patch and all formal source bindings are unchanged.

## Native source target for the caller proof

The separate [OSMutex_RdyAtPrio.c](../../annotated_C/src/mutex/OSMutex_RdyAtPrio.c)
intake retains the source's static helper, the approved conditional-current
write and the complete selected 64-byte TCB. It has no invented callee contract
and does not modify or reuse the acceptance of `OSMutex_RdyAtPrio_full.c`.
It is not yet a controller-bound proof dependency of Delete or Post.

The narrow source diagnostic is:

```sh
python3 uC-OS2_verify/tests/mutex_current_priority/check-native-source.py
python3 uC-OS2_verify/tests/mutex_current_priority/test_native_source.py
```

The positive source/layout check and all three negative tests passed. The
checker compares the complete preprocessed helper and TCB, seven
scalar aliases, static linkage, ILP32 size/alignment, the five touched field
offsets and all five referenced global types. Negative fixtures independently
change the current-pointer guard, the priority field type and the priority-table
extent; each is rejected at the corresponding check. It reuses the Task source
token helpers, reads the candidate once, performs no SHA-256 scans and writes
only its own disposable diagnostic copies. `--target <candidate.c>` supports
checking a future controller-owned candidate without editing it.

QCP MCP also parsed this intake successfully with `arch=32`, `endian=little`,
the canonical `QCP_demos_LLM` include/mapping and the `uC-OS2_verify` mapping
to `Ucos2Verify`; the case logic path was `Ucos2Verify.VC.code.mutex`. Its
current backend policy permits load/parse only and disables interactive
check/proof/step/symbolic. The diagnostic session was closed after parsing;
no canonical VC generation or proof result is claimed from that call.

The native contract must follow the helper's actual boundary:

- Clear the old ready-row bit and conditionally the old group bit; update
  priority/coordinates; set the new ready bits; then write the new priority
  table cell. The helper does not clear the old table alias.
- Update `OSPrioCur` only for `ptcb == OSTCBCur`. Do not conflate this scalar
  with `OSPrioHighRdy` or `OSTCBHighRdy`, which the helper never writes.
- Preserve all other native TCB bytes and Event wait bytes. Any Task-indexed
  Event bitmap transport is a separate proved relation, not an Event write.
- The caller supplies critical protection and the real internal pointer/index
  domain. The helper neither calls Save/Restore nor schedules. Readiness,
  suspension and owner-use closure require their own source-backed conditions;
  this target does not fix the separate NO_PEND suspended-owner case.

Next, bind this concrete body and its native representation to the appropriate
new function run and prove the callee/caller composition. GCC preprocessing and
host layout are not ARM execution, QCP/Rocq acceptance or evidence that those
remaining obligations have already been discharged. The earlier 24 execution
diagnostics were not rerun for this source-intake addition.
