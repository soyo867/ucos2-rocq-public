# Statistics sampling repair candidate

This is a separately retained variant of `Source/os_core.c` in the V2.93.01
revision bound by `config/queue-v2.93.01-first-round/profile.json`. It changes
only `OS_TaskStat`; the pinned original remains unmodified. This is a C
implementation repair, not an annotation adjustment or an accepted proof.

The original task divides `OSIdleCtrMax` by 100, then self-suspends once if the
result is zero. Suspension may return after a legal resume; it is not a
nonreturning branch. The subsequent sampling division can therefore use zero.
The variant rechecks the condition after each such resumption. Each sampling
iteration also captures the sample and divisor in the existing critical
section and handles a zero divisor without evaluating division, including if
calibration was restarted while the task was delayed.

The original signed 8-bit cast of the idle ratio also permits invalid CPU
percentages: ratio 229 produces 127, and ratio `UINT32_MAX` produces 101 under
the selected signed representation. The variant compares the full unsigned
ratio with 100 before conversion. Ratios through 100 give `100 - ratio`;
larger ratios give zero and recalibrate from the same sampled counter. The
division result is not narrowed before this comparison.

Run the source regression with:

```sh
bash uC-OS2_verify/tests/statistics_sampling/run.sh
```

It compiles the actual original and patched `os_core.c` with the pinned
configuration and UBSan. Fourteen runs cover normal, boundary, excess,
signed-narrowing, maximum-counter, resume-after-zero and repeated-zero-
calibration cases. The two original zero-divisor runs must fail with the
specific UBSan division diagnostic; an arbitrary crash is not a passing test.
The other original runs assert their actual results, including the values
outside 0–100, instead of silently treating them as repaired behavior.

The fixture supplies explicit delay/suspend-resume/CPU/hook observations; the
recalibration scenario calls the actual `OSStatInit`. It stops at the first
statistics hook or the second zero-calibration suspension. It is not a real
ARM/BSP, scheduler, idle-loop timing or full system boot proof. Counter wrap,
clock accuracy, callback effects, and the initialization/calibration lifecycle
still need their own model contracts. The numerical repair does not prove
that the sampled ratio accurately measures physical CPU load.
