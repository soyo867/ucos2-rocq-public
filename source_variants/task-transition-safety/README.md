# Task 当前任务身份与 Idle 优先级保护

2026-10-17：两项最小 C 修复已通过独立源码 review 和真实原/修复实现对照。
本目录固定修复源码及可重建回归，不宣称完整 Suspend/ChangePrio API 已证明。
后续正式函数输入须应用本补丁、重新生成当前 VC，并证明受影响语句及调用。

## 已确认问题与最小修复

1. Mutex 继承后，一个当前任务可同时由永久槽 20 和有效优先级槽 5 指向。
   原 Suspend(20) 仅用参数与当前有效优先级数值判定 self，实际 lookup 却选中
   当前 TCB；清 ready、置 SUSPEND 后漏调 OS_Sched，返回到已挂起任务。
   补丁在受保护 lookup 与 NULL/reserved 检查后，以 `ptcb == OSTCBCur`
   重算 self，原有写入和错误分支不变。已批准 owner-use 允许挂起 owner，
   该反例没有在持锁时 ChangePrio/Delete 或 Pend 另一 Event。
2. 原 ChangePrio 接受 SELF，解析成 Idle 后没有重复保护。ISR 打断真实 Idle
   loop 时可把优先级 63 改成 5，破坏真实 Tick 以 63 为尾哨兵的遍历，导致
   NULL TCB 解引用。补丁在 SELF 解析后、内核写入前拒绝 Idle，Restore 后返回
   已有 INVALID(42)。先前的 new-slot-occupied 检查和错误优先级保留。

两者由源码逻辑、API 建立的可达状态、原版错误执行和修复对照共同支持，
并非为了关闭 VC 而修改 C。原 SELF/effective-priority、非当前重复挂起，
以及其他未经过新增 guard 的原分支均保留；没有增加公开参数或平台假设。

## 固定输入与回归

固定 V2.93.01 提交为 `bfc6120f20cb27a927a9fc5dd667f9e455495777`。
先使用统一 `config/timer-v2.93.01/profile.json`，保持 MultiEvent、EventNames、
TaskProfile 关闭；双方随后显式应用已有 Idle 保护与 Mutex nested-priority
变体，修复方再应用本目录 `os_task.patch`。原始头文件和其他函数保留。
准备工具的 manifest 只描述共同 profile，额外实现 patch 的完整顺序以本脚本
为准；不把该 manifest 冒称为已经绑定额外补丁的 formal acceptance。

从仓库根执行，输出目录必须不存在：

```sh
bash uC-OS2_verify/source_variants/task-transition-safety/run.sh \
  "$UPSTREAM" "$NEW_OUTPUT_DIRECTORY"
```

harness include 真实 prepared 的 os_core/os_task/os_mutex 实现。实际 TaskCreate、
Mutex Accept/Pend 建立继承 alias，修复后的 Suspend/Resume/Post/Pend 完成同一次
调用的返回路径，共 7 次 context switch。Idle 反例通过真实 Idle loop 的 Restore
注入 ISR，再调用真实 Tick；原版预期 UBSan rc1，修复版 Tick/IntExit 正常返回。
guard 前后用 memcmp 比较 TCB 和 ready rows，并比较 ready group、检查 priority
table 的 5/63 两槽；其他表槽不变另由新增 guard 在所有 table store 前返回推得。
两版真实 Task C 均通过 ILP32 syntax 检查；16 个 Task 函数中仅两体改变，
其余 14 个及其余 native source/header 文件逐字相同。

host ucontext、保存状态、StackInit 和若干 hook 是明确的诊断 port 边界。
fixture 执行真实静态初始化 helper、TaskCreate/OSStart，未完整执行 OSInit 或
启用的全部 Statistics/Timer 启动任务；不宣称端到端启动或 ARM/BSP/ABI 已证明。
未穷尽 ISR、生命周期、宏配置或异常内存状态。selected C 层完整证明仍须独立交付。

独立 review 与原始反例保留在
`reports/kernel-model-20260927/source-input/task-api-20261016/task-transition-repair/`，
尤其 `source-review.md`、`run-3/`；永久脚本回放证据位于同目录
`permanent-run-1/`。此次源码修复不继承任何旧函数的 acceptance。
