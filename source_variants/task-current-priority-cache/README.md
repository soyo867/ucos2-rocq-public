# OSTaskChangePrio current-priority cache 修复

固定 uC/OS-II V2.93.01 提交
`bfc6120f20cb27a927a9fc5dd667f9e455495777`，使用统一
`config/timer-v2.93.01/profile.json`。在 profile 三项兼容补丁之后，依次应用
`task-idle-protection`、`mutex-nested-priority`、`task-transition-safety`，最后
应用本目录 `os_task.patch`。本补丁与已审查 source v1 逐字相同。

唯一新增执行体位于五个 TCB priority stores 后、原 Restore 前：

```c
if (ptcb == OSTCBCur) {
    OSPrioCur = newprio;
}
```

当前目标同步缓存，非当前目标保留缓存；条件使用真实 TCB 身份。原 guard、
错误码、ready/Event 更新及 ISR/非 ready 目标的已批准调用域保持原有含义。
补丁不把等待任务变成 ready，也不保证其他写入者从未留下旧错配。它可能改变
后续 Scheduler/IntExit 是否切换，因此不承诺切换计数或 hook trace 等价。

修复依据是已完成的固定源码/配置/协议推导，见
[实现审查](../../../reports/flag-api-active-successor-20261101/pend-scheduler-priority-review-20261102.md)。
[源码重建](../../../reports/task-change-priority-cache-20261102-direct/source/README.md)
保存固定 Git 对象、22 文件对照和最小差异；没有新增 C 运行回归。
[完整当前证明审计](../../../reports/task-change-priority-cache-20261102-direct/proof/final-proof-audit.json)
覆盖 63 manual、150 generated-auto、449 条声明查询。
[交付说明](../../docs/case_briefs/task-change-prio-c-delivery.md) 保留 generated-auto、
抽象平台和共享消费者边界。这是独立直接迁移，不改变旧 controller 状态。

本目录只包含这一项 cache 修复；不代表全部已发现问题、其他 source variants
或整个内核均已修复。共同 Task/Mutex/Flag 配方另见
[linked-kernel-v1](../../../reports/task-change-priority-cache-20261102-direct/source/linked-kernel-v1/README.md)。
