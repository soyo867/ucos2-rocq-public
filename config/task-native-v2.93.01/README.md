# Native Task creation-hook selection

The user selected the official empty application creation hooks on 2026-09-08
and requested that custom hooks remain easy to integrate. This is a new Task
source selection, not a rewrite of the historical Queue profile or an accepted
verification artifact.

[hook-source-binding.json](hook-source-binding.json) fixes the existing header
configuration and the official V2.93.01 source commit. Both CPU and application
hook switches remain enabled. [creation_hooks.c](creation_hooks.c) contains the
two selected function definitions with unchanged executable tokens; its opaque
TCB declaration does not assert a replacement layout. The real port wrappers
still dispatch `OSTCBInitHook -> App_TCBInitHook`, followed by
`OSTaskCreateHook -> App_TaskCreateHook` at the existing target call sites.
This selects these two functions only, not every application hook in the OS.

Run the narrowly scoped source/dispatch diagnostic:

```sh
python3 uC-OS2_verify/tests/task_publication/check-hook-source.py
```

It checks the selected definitions against the immutable release, the enabled
wrapper dispatch and the exact base configuration, then performs a freestanding
ILP32 syntax check of the selected definitions and wrappers. It does not execute
old Task tests, generate VCs, establish ARM semantics or provide Coq acceptance.

## Stable interface for later custom implementations

Keep three separate pieces in the formal integration:

1. The kernel's required hook contract: ownership of the same private allocation
   and invocation, preservation of its priority reservation, safe post-hook
   coordinates/fields for the actual commit, and explicit kernel/application
   resource frames. Preserve the source's ordering and the distinction between
   original `prio` and values reloaded from the TCB after the hooks.
2. A source-specific hook effect relation and its proof that it meets that
   contract. A parameterized theorem is not an extra global axiom: the concrete
   function theorem must discharge the instance's obligations.
3. The source-constrained environment relation. The empty bodies have no direct
   shared effect, but an enabled interrupt may still intervene. Do not conclude
   that all global state is equal across the entire call/Restore interval.

The selected empty bodies are the first concrete instance. For a custom hook,
use a new source/profile version and prove its effect/frame obligations. If it
satisfies the existing interface, reusable Task lifecycle lemmas remain useful;
refresh the affected concrete call/VC evidence under the new version. If it
publishes or frees the private node, changes priority/addressing fields, blocks,
or changes resource ownership, first check whether the existing kernel commit
can support that behavior. Extend the contract and preservation proof only when
the actual source supports it; do not promise arbitrary hooks are safe.

## Integration status

The source selection is authorized; its generic contract and concrete instance
are not yet fully proved. The running r2 worktree retains its frozen handoff.
The next appropriate controller transition must bind this choice and consume
its source evidence before N7 is marked closed or a final function claim uses
the empty-hook effect. No handoff/report is patched in place, and no old
acceptance is transferred by this document.

## Candidate-source integration

The controller already binds the target C translation unit in `source_version`.
In the next appropriately authorized annotation round, place the two selected
App definitions and the two unchanged port forwarding definitions in that unit,
using its native TCB declaration. Keep the executable `OS_TCBInit` body unchanged.
The canonical whole-file run can then generate obligations for both the hooks
and their caller; the isolated probe is not a substitute for that integration.
The frozen retry context must explicitly record the user's hook selection;
neither the existing r2 input nor an old report is rewritten.

Check the actual candidate, not merely the main intake:

```sh
python3 uC-OS2_verify/tests/task_publication/check-tcb-source.py --target <round-worktree>/uC-OS2_verify/annotated_C/src/task/OS_TCBInit.c
python3 uC-OS2_verify/tests/task_publication/check-hook-source.py --target <round-worktree>/uC-OS2_verify/annotated_C/src/task/OS_TCBInit.c
```

The first check compares the native TCB, scalar aliases and complete repaired
function body; the second compares all four hook definitions and their caller's
call order with the selected release. They are source diagnostics only. The
candidate's contracts, private-resource frames and interrupt interference still
need their ordinary QCP/Rocq proofs and controller acceptance.

The QCP frontend requires explicit `struct os_event;` and
`struct os_flag_node;` declarations before the opaque typedefs in the intake.
These forward declarations do not introduce a layout or change a function body.
A separate probe with `struct os_tcb;` and the four original hook bodies passed
canonical 32-bit/little-endian symbolic execution on 2026-09-08; it generated
six simple empty-frame obligations, not a proof of the native Task call contract.

The current controller's generated-coverage diagnostic was also applied to that
four-function probe: it collected all six `VC_Correct` obligations across both
App hooks and both port wrappers, with no missing or mismatched declarations.
Collection is not filtered to the main `target_function`. All six probe
declarations are in the canonical generated auto file and currently contain
`Proof. Admitted.`; none is a kernel-Qed result. Thus the probe establishes
whole-unit coverage compatibility only, not a source-to-Coq proof of the hooks.
The concrete integration must retain the actual hook contracts and the existing
tool-trust disclosure; do not patch generated output or treat auto membership
as an assumption-free theorem.

The new candidate-input diagnostics were exercised on the isolated native unit:
both positive checks passed, and separate mutations of an App hook body, the
caller hook order and an `OS_TCBInit` assignment were each rejected at the
corresponding source comparison. No formal worktree was edited for those tests.
