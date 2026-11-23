# OS_TCBInit atomic-publication source variant

Variant ID: `task-atomic-publication`. User authorized this independent C-level
repair on 2026-09-08. The pinned upstream checkout, original configuration
profile and previously accepted QCP/Rocq artifacts are not modified.

This directory contains a proposed source repair and its design, **not** a
controller-accepted verification result. The patch is applied only to a
temporary source copy by the [diagnostic runner](../../tests/task_publication/run.sh).

## Exact change

Base: uC/OS-II V2.93.01, upstream commit
`bfc6120f20cb27a927a9fc5dd667f9e455495777`, `Source/os_core.c::OS_TCBInit`.
Use the existing `queue-v2.93.01-first-round` configuration without changing
feature flags. No function other than OS_TCBInit is patched.

Remove the separate critical section that publishes `OSTCBPrioTbl[prio]`
before `OSTaskCreateHook`. Put that assignment in the final critical section,
after active-list insertion, ready-bit insertion and `OSTaskCtr++`, before
the ready trace hook and Restore. Keep initialization and both creation hooks
in their original relative order and interrupt-mask context.

The caller's priority reservation now remains in force throughout initialization
and the creation hook. APIs which check NULL/RESERVED cannot obtain this TCB
through the priority table until its list and ready state are committed. The
removed intermediate Restore eliminates the indexed-but-unlinked window.
No additional lock duration is placed around arbitrary application hooks.

## Intentional observable compatibility change

For the tested previously unoccupied target priority and this configuration:

| Creation-hook action | Original | Variant |
|---|---|---|
| Suspend(new priority) | Succeeds, followed by inconsistent final ready insertion | `OS_ERR_TASK_NOT_EXIST`; creation commits normally |
| ChangePrio(new priority, unused priority) | Succeeds and creation uses the changed priority | `OS_ERR_TASK_NOT_EXIST`; original reserved priority is retained |
| Delete(new priority) | Succeeds against a TCB not yet in the active list | `OS_ERR_TASK_DEL`; creation commits normally |

These are the existing Task API guards and error codes, not newly invented
returns. Applications which intentionally operate on the new task by priority
inside `App_TaskCreateHook` must be adapted. This patch is not claimed to be
behaviorally equivalent for all old hooks.

After publication, Suspend remains allowed and leaves the task linked but not
ready. OS_TCBInit may therefore return after legitimate environment steps;
its concurrent postcondition cannot promise unconditional readiness at return.
Allocation failure still returns `OS_ERR_TASK_NO_MORE_TCB`; the public Create
wrapper remains responsible for clearing its priority reservation on failure.

## Evidence on 2026-09-08

```sh
bash uC-OS2_verify/tests/task_publication/run.sh
```

The runner tested original and repaired source, **12 scenarios per variant**,
with exit status 0 and no UBSan diagnostic. The original Suspend/Delete
counterexamples remain reproducible. The repaired cases reject precommit
lookups and preserve the full fixture's active/free disjointness, doubly linked
active list, task count, priority index and ready/status correspondence.
The IRQ tests execute actual OSIntEnter/OSIntExit around the injected action;
one acts before commit, another immediately after commit. Saved masks 0x40,
0x80 and 0xc0 are separately preserved, as is the ordinary unmasked case.

This is host source-execution evidence, not universal interleaving coverage,
an ARM interrupt/ABI proof or QCP/Rocq acceptance. See the diagnostic README
for the fixture and architecture boundaries.

## Formal integration obligations

1. Model `reserved -> private initialized -> published` with allocation
   ownership. The private TCB is removed from the free list but not indexed or
   linked; the global model must retain the reservation and frame rather than
   pretend that every allocated TCB is already a live task.
2. Creation hooks receive the raw pointer. Moving table publication does not
   prevent them from directly changing fields or exporting that pointer.
   Specify and connect the actual hook implementation's ownership/lifetime and
   field-update contract; do not infer unrestricted-hook safety from these tests.
3. `OSTaskRegGet/Set` do not guard a NULL/RESERVED lookup in the original source.
   This patch does not make those calls safe during creation. Their valid caller
   domain or a separately justified repair must be addressed explicitly; do not
   claim that all Task APIs now reject unpublished tasks.
4. Prove final commit preservation from the complete selected TCB layout and
   task/scheduler state. The historical 68-byte verification slice is not the
   native full OS_TCB layout.
5. Connect both public Create callers, rollback, port stack construction,
   scheduler/resumption and allowed ISR operations. The current test enters at
   OS_TCBInit, not at these public wrappers or OSInit/OSStart.
6. Keep MutexDel's independent event-bitmap transport/call-site and high-ready
   cache obligations in the same repair batch. This publication patch does not
   discharge them or retroactively validate old Queue/Task proofs.

Future formal work must use a controller-created case/handoff that explicitly
identifies this variant, includes its actual executable target in the source
binding and authorizes the exact shared semantic owners. Existing sealed
QFlush r4 artifacts remain untouched; this README is not write authorization
for that terminal attempt and cannot substitute for final-candidate-apply.
