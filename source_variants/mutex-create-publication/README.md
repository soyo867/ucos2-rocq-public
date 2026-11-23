# MutexCreate: finish initialization before restoring interrupts

This additive implementation variant records the lifecycle-enhancement scope
authorized by the user on 2026-10-08, with the requested documentation. It
builds on `mutex-del-revalidate` and its earlier nested-priority patch; none
of those frozen implementations or proof checkpoints is changed.

## Exact change and intended property

After allocating the ECB, Create now retains its original saved critical
section while writing Cnt, Ptr, optional Name and the real wait-list fields.
It writes `OSEventType = OS_EVENT_TYPE_MUTEX` last, then restores the original
mask. Trace and error-output stores retain their original position outside
the critical section. The error guards, failure rollback, signature, layout,
PCP constants, and successful final field values are unchanged.

For the selected single-core interrupt discipline, another task cannot now
run in this allocation/initialization interval. A Del protected type read
cannot observe the Create slot with a published Mutex type while those
initialization stores are still pending. This is a C order/masking repair,
not a ghost label or a new public proof precondition. It relies on the
existing platform mask contract, not a proved ARM/BSP implementation.

The tradeoff is a longer bounded interrupt-masked section: the wait-list
initializer and the above fixed field stores are now inside it. No measured
latency bound, SMP safety or protection against arbitrary memory access by
DMA/nonmaskable handlers is claimed. Selected tracing remains the existing
configuration; custom hooks require their own actual resource contract.

## What this does not fix

Raw `OS_EVENT *` does not encode an object generation. After a complete
delete/recreate at the same address, an old pointer can still name the new
Mutex, including just after Create restores interrupts and before it returns.
This variant does **not** claim to reject that ABA case or complete the
authorized lifecycle work. Generation-aware handles or another enforceable
reuse protocol need separate implementation/compatibility treatment. No
unproved caller restriction is silently substituted for that work.

The original raw-pointer APIs are retained in this increment. Historical
Create proofs of unmasked private stores and the partial enhanced Del proof
are not proofs of this new source. Its current-source Coq publication/call
composition and whole-function canonical checks remain to be integrated.

## Reproduction

```sh
bash uC-OS2_verify/source_variants/mutex-create-publication/prepare.sh \
  UPSTREAM_GIT NEW_OUTPUT_DIRECTORY selected
bash uC-OS2_verify/source_variants/mutex-create-publication/prepare.sh \
  UPSTREAM_GIT ANOTHER_NEW_OUTPUT_DIRECTORY full
bash uC-OS2_verify/tests/mutex_current_priority/run_create_publication.sh UPSTREAM_GIT
```

Both profiles retain pinned V2.93.01 source and original headers. `selected`
keeps Multi/Names/Profile disabled; `full` enables all three together. The
source preparer applies declared patches with zero fuzz and records exact
inputs. Preparation and host regressions are not QCP/Rocq acceptance.

The host fixture uses compiler function-entry/exit instrumentation, without
rewriting kernel bodies, to observe the real Create/WaitListInit order. Its
separate task stacks reproduce a stale Del before WaitListInit in the
baseline; the enhanced version defers that task until initialization is
complete. It deliberately retains the post-publication ABA outcome.
