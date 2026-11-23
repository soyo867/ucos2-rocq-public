# Flag Post critical-section type revalidation

This is a **partial source repair**, not a completed Flag API verification.
It applies to the pinned V2.93.01 `Source/os_flag.c` used by
`config/timer-v2.93.01` (upstream commit
`bfc6120f20cb27a927a9fc5dd667f9e455495777`). The original prepared source is
read-only; apply the patch only to a fresh candidate copy.

## Confirmed implementation fault

Original `OSFlagPost` reads `OSFlagType` before entering its critical section.
A task may be preempted after that check; another task can successfully execute
`OSFlagDel(group, OS_DEL_NO_PEND, ...)` while the group has no waiter.
Delete reuses `OSFlagWaitList` as a free-group successor. The resumed Post then
writes flags and interprets that successor as an `OS_FLAG_NODE`.

The existing selected layout has five groups. With four allocated groups, the
remaining free group is the last pool slot. Post reads `OSFlagNodeWaitType`
outside that slot and outside the array. Both SET and CLR paths were reproduced
by compiling and executing the real Flag source with AddressSanitizer:
`global-buffer-overflow`, `READ of size 1`, `OSFlagPost`, source line 933.

The current host regression has 32-byte groups, 40-byte nodes and WaitType
offset 34: slot 4 causes a read two bytes beyond the 160-byte pool. This is a
host result, not an ARM execution claim. The selected ARM32 layout separately
has 16-byte groups and offset 18, giving the analogous `base+82` read beyond
the 80-byte pool. The injected preemption is an explicit C test fixture before
masking; no assertion is made that this verifies the ARM/BSP interrupt wrapper.

## Exact repair and behavior

After the actual `OS_ENTER_CRITICAL`, valid SET/CLR operations re-read the type
before touching flags or the wait list. A deleted/non-Flag group is rejected
with a matching `OS_EXIT_CRITICAL`, `OS_ERR_EVENT_TYPE`, and zero return.
The original pre-critical NULL/type checks remain. Invalid `opt` still reaches
the original `OS_ERR_FLAG_INVALID_OPT` branch, including after an intervening
deletion. No public signature, record layout or configuration changes.

The repair was authorized after the user required genuine implementation
evidence, and requested repairing and proving confirmed bugs. It is not based
on a failed VC or an invented separation-logic premise.

## Reproduction and current evidence

Use the existing selected prepared tree as SOURCE and a new OUTPUT directory:

```sh
python3 uC-OS2_verify/tests/flag_lifetime/run.py \
  --source-input "$SOURCE" --output "$OUTPUT" \
  --patch uC-OS2_verify/source_variants/flag-post-revalidation/os_flag.patch
```

The runner compiles original and patched C, archives the fixture, and saves
the exact compiler/runtime argv, stdout, stderr and return codes in `run.json`.
Current execution evidence is
`reports/wsl-verification-20261027/flag-lifetime-revalidated/run.json`.
Original SET/CLR runs reproduce the overflow; patched runs reject the deleted
group and preserve the free chain. Normal SET/CLR and invalid-option behavior
are checked separately.

## Outstanding lifecycle work

This type check cannot distinguish an old object from a newly created object
at the same address. The regression deliberately retains three **known gaps**:

- Delete/Create before Post's first protected action lets it write the new group.
- Delete/Create before Post's final protected read lets it return the new group's flags.
- Post wakes a Pend, then Delete/Create reuses the group before Pend resumes;
  delayed consume modifies the new group's bit.

Those cases have `outcome = known lifecycle gap reproduced`; their expected
execution result is not a successful safety claim. Do not call this patch a
full ABA/lifecycle fix, silently require no concurrent reuse, or replace real
protection with ghost generation alone. The separate Pend abort double-unlink
repair remains in `source_variants/flag-abort-cleanup`.

Formal adoption still requires a versioned source decision, appropriate real
lifecycle repair, actual safeExec contracts, canonical QCP generation and all
Rocq/controller checks. Existing accepted Flag functions and reports are unchanged.
