# Mutex Delete: revalidate the type under interrupt masking

This is the minimal C implementation enhancement authorized on 2026-10-08.
It is an **additive patch** on the pinned V2.93.01 source, following
[`mutex-nested-priority`](../mutex-nested-priority/README.md). Neither that
earlier patch nor its historical proof artifacts are changed.

## Change and scope

`OSMutexDel` retains its original early type check and ISR check, in that order.
Immediately after `OS_ENTER_CRITICAL()` it reads `OSEventType` again, before
reading the wait group, count, owner or priority table. If the object is no
longer a Mutex, it restores the saved interrupt status and returns the original
pointer with `OS_ERR_EVENT_TYPE`, using the existing trace-exit hook.

The second check is necessary even when the first passed: a different task
could have deleted the object before this call masked interrupts. Previously
the suspended call could recycle the ECB again, corrupting the free list and
possibly the priority table. The new check applies before both `OS_DEL_NO_PEND`
and `OS_DEL_ALWAYS`; it is distinct from the earlier owner-priority repair.
No type layout, public signature, error code, configuration value or priority
restoration algorithm is changed. Successful noninterfered execution is unchanged;
the new rejection path intentionally changes execution under interference.

This is **not** a general stale-pointer or ABA repair. If an ECB is deleted and
recreated as a different Mutex at the same address before the check, the raw
pointer and type byte cannot identify the old instance. The same limitation
includes an object still being privately reinitialized: Create restores IRQs
before writing its type, count, owner and wait list. A visible Mutex type alone
does not prove that all those writes have completed. Object-lifetime coordination
remains necessary for these cases. No application protocol is added
to the public proof precondition by this patch. The interrupt-masking argument
is for the selected single-core port, not an SMP lock or an arbitrary hook/ISR
implementation proof.

## Reproducible source input

```sh
bash uC-OS2_verify/source_variants/mutex-del-revalidate/prepare.sh \
  UPSTREAM_GIT /tmp/ucos2-del-revalidated-source
```

The output must not already exist. The existing source preparation tool reads
the exact upstream Git objects, applies the declared five patches with zero
fuzz, retains the original headers/macros, and archives the actual profile and
patches in `verification-input/`. The profile keeps Multi/Names/Profile disabled
and the selected ARMv7-A ILP32 configuration. Preparing source is not QCP or Rocq
verification. Later annotation overlays must target this newly prepared source,
not mutate the frozen r29 source or reuse its acceptance.

## Regression and proof boundary

Run the actual-source host diagnostics with:

```sh
bash uC-OS2_verify/tests/mutex_current_priority/run_del_revalidate.sh UPSTREAM_GIT
```

The fixture switches independent host call stacks just before the simulated
Save masks interrupts, so the competing Delete runs between the early check
and the protected read. It does not edit the kernel function or insert an
assumption excluding that interleaving. The runner compares the earlier
nested-priority implementation with the enhanced implementation and also checks
the existing priority/wake/scheduler regressions.

On 2026-10-08 the runner passed: eight double-delete and two Sem-reuse
interleavings were rejected by the new implementation, while the baseline
reproduced their corruption. Ordered errors/mask restoration and the existing
priority regressions also passed. The tests retain two same-address new-Mutex
cases as explicit ABA limitations. See the [regression report](../../../reports/kernel-model-20260927/source-input/mutex-del-revalidate-20261008/README.md).

These are deterministic host regressions with explicit platform stubs, not an
ARM/BSP proof or exhaustive concurrency verification. The old r29 168/171 manual
checkpoint still describes the old source. New canonical obligations, the new
error path, and the remaining Save/Restore/scheduler resource interfaces require
fresh proof integration before the enhanced whole function can be called proved.
