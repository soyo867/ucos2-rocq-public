# uC/OS-II V2.93.01：全部源码函数到模型的映射

本清单配套 [详细模型设计](ucos2-v2.93.01-model-design.md) 与 [总体要求](ucos2-v2.93.01-model-foundation.md)。
覆盖原始 `Source/os_*.c` 的 **126 个函数定义**，不是已证明数量，也不是 VC 数量。含 internal/static
与条件定义；`ucos_ii.c` 聚合十个实现单元，`os_dbg_r.c` 另列，合计十一单元。未计函数原型。

## 读法、版本及审查边界

- 源行号指向绑定的本地 V2.93.01 原始源码。Task publication 与 Mutex nested-priority 的行为
  按已选 [Task 变体](../source_variants/task-atomic-publication/README.md) / [Mutex 变体](../source_variants/mutex-nested-priority/README.md)
  单独绑定；尤其 TCBInit、MutexPend/Post/Del/RdyAtPrio 的下述设计不声称与缺陷原版等价。
- 后续 [Flag abort cleanup 变体](../source_variants/flag-abort-cleanup/README.md) 仅调整
  `OSFlagPend` 的 abort 续体，跳过 Delete 已完成的摘链；下表原版路径作为来源保留。
  原版/修复版的源码回归不是 Flag 形式化验证完成，实施模型须绑定实际采用的版本。
- 外层 guards 决定函数是否生成；函数内部还有 ArgCheck、safety、布局、trace 等条件分支，按
  [配置增量设计](ucos2-v2.93.01-model-design.md#36-配置变化的具体增量) 处理。表中的 NULL/range
  检查按当前配置描述，不能将被预处理删掉的检查保留为错误返回。
  同理，“清池/复制结构”的实际长度经过 u16 size 窄化；大容量/其他布局需按真实调用补长度和 BSS 证明。
- “owner”列是主要语义依赖，不是每个指针都各拥有一份对象；critical 的 Intr 资源、输出参数
  的 caller 权限、共享名称字节及必要跨模块关系亦适用。函数 spec 放相应模块 proof/spec，
  共享表示/关系仍在 lib；已有 Task 的 TCBInit spec 等沿用既有归属。
- 空间接口统一从 `lib/ucos2_spatial.v` 的完整 `UCOS2_raw_rep` 出发；全局入口仍为
  `UCOS2_inv sg s := coq_prop (UCOS2_state_inv sg s) && UCOS2_raw_rep sg s`。缺一使用
  `UCOS2_raw_rep_missing_module`，缺二使用 `UCOS2_raw_rep_missing_two`（拆分时要求 owner
  不同），具名接口是二者的特化。完整 Task owner 包含公共存储及 parked stacks；只动
  TCB/ready 的端点明确使用 `missing_task_storage_sched`，保留栈资源。
  本批重组的检查状态见 foundation；下方历史检查记录不自动覆盖本批新字节。
- 模型字段按实际对象归属组织：补齐的 Task/Event 字段直接位于各自 abstract state，新增全局
  地址直接位于 `StableGlobVars`，不再经历史字段袋或兼容 alias。配置实例、raw image 与
  lifecycle 的独立语义保留；此调整不改变下表的源码/API 映射，细节与检查状态见设计和 foundation。
  TCBInit 无消费者的旧 3 个 projection/observation 定义及 6 个引理已删除；Tick 保持性已平铺并
  补 `curPrio`、适配三个消费者。waiting single backlink 的旧定义及两个 bundle 冗余已删除，
  全部 lib/spec 消费者已适配。
- 全局静态配置现名为 `selected_kernel_profile`，由 `UCOS2_inv` 的有效性层统一持有；
  TCB 特有条件仍为 `tcb64_configuration`。布局区间合并 core、条件模块、TaskReg 和所选系统栈，
  仅约束地址与范围，不重复拥有 caller/task/platform 已持有的栈字节。
  `stable_glob_vars.v` 全文件固定 debug Load 已通过（rc=0，0.442 秒）；44 个 `g_*` 在完整
  区间表各出现一次，当前 IEC 关闭时为 43 段。Timer unlink 已移除 profile 可导出的单池
  layout 前提；模型/spec 的 profile 名称已同步，并由本批完整集成检查覆盖。
- 下表接口名按当前模型整理：`UCOS2_inv` 指当前全局组合，`verification_slice_*` /
  `UCOS2_verification_slice_*` 明确指历史切片，不代表旧证明已迁移。源码 API 名不变；
  本批完整独立模块检查已通过入口中的 88 个唯一 lib/spec 文件（rc=0，
  `first_diagnostic=null`、`dependency_errors=[]`），当前源文件及入口与构建副本均逐字节相等。
  包含完整 MutexDel 及 SemPend、SemDel、MutexRdyAtPrio、MutexPost，不再仅依赖 focused/Load
  局部结果。MutexDel 公开 abort 效果不变，内部成功效果的 Event 有效性由入口不变式提供；
  SemPend 六条引理 statement 不变，MutexPost 的完整 frame 与 wake 前提传播已覆盖。
  `task_tcb64_image` 的局部同义别名已删除；去注释/字符串后的本批扫描无 `Native`/`native`
  标识符残留或实际 `Admitted`、`Axiom`、`Parameter`，不扩大依赖库/平台的信任结论。
  此结果只完成字段袋与接口清理批次；全部 API 模型剩余语义组合、旧 generated/manual
  迁移及旧 VC 验收仍未完成，原目标后续工作保留。检查范围见 foundation，历史 slice 并非冗余。
  第五份旧名映射见 `.coq_debug/model_static_interface_cleanup.json`。
- C annotation 的接口名称同步涵盖 `OS_TCBInit`、`OSMutex_Priority`，本轮另增
  `OSMutexPend`、`OSSemQuery`；非 annotation 字节精确相等，没有修改 C 实现，亦不代表旧 VC 迁移通过。
- Task 栈组合已通过独立模块固定检查：`task_stack.v` 的 parked publication/generation
  一致性、`task_context.v` 的实际 saved-SP 写后资源组合与保持性，以及 Create 的受保护
  提交接入均已实现。允许退休 generation 保留缓冲区，恢复另需 live binding；不重复拥有
  初始栈或 Flag 借出的节点。该结果不是完整 ARM/Save/Restore/Flag-Multi 借还协议或旧 VC
  迁移完成；检查入口和剩余边界见 foundation 的“栈发布与切换资源组合”记录。
- 新增 `core/spec/kernel_start_stack_spec.v` 已把 TCBInit 的实际发布写后单元与栈交入、
  OSStart 选择以及 actual post-hook 的 OSRunning 写后／栈取出接入全局资源。固定检查
  与采用记录见 `reports/kernel-model-20260924/startup-stack-integration/README.md`；
  不把外部 hook、ARM frame 解释或完整 OSInit 系统任务创建记为已经证明。
- Flag 节点的真实字节借还已由 `flag_stack.v` 接通 QCP 数组与现有节点表示，覆盖
  8/16/32-bit 布局；`task_stack.v` 保留两侧实际 residual，归还消费更新后的节点，
  不用 None 表示被借走的洞。完整导入检查通过，包含 Task context/Create/StackCheck
  直接消费者。片段表现在直接接入 Task 状态及全局资源，当前适配的集成检查状态另见 foundation。
  `flag_execution.v` 已将实际节点/链表写后资源、Task/Sched 字节与全局不变式连接，
  并组合唤醒/超时清理后的栈归还。真实 &node 的调用栈来源及完整 C store 调用证明
  仍需由函数层提供；源码 TCB backlink 早于节点初始化，Del/Post 摘链后仍需读取 Next。
  具体检查与边界见 foundation 的“Flag 栈节点字节借还”记录。
- `flag/spec/flag_block_spec.v` 已实现并通过完整检查：复用 Task/Scheduler/Flag 现有
  操作，证明真实 current 选点、精确字段变化、非目标状态 frame 和三模块有效性，
  不新增字段袋。Block 的完整跨模块保持及节点/TCB/位图写后重组已在
  `flag_execution.v` 完成，联合固定证据见 `reports/kernel-model-20260924/borrowing-integration/`；
  Pend 续体、平台和实际 C 调用仍有独立义务，该结果不是 OS_FlagBlock C 函数的 VC 验收。
- Task 共同配置的 used/free/private 存储现共用 Multi-off/on 的 64/72 字节地址接口；
  优先级表、调度缓存、Mutex owner 与 Flag node 的 TCB 回指同步使用该接口。
  WaitMulti 两指针的 source-image 对应及公共 Task map 拆合已接入；实际数组地址为
  `tcbEventMultiPtr`，逻辑输入序列为 `eventMultiWaitEvents`。`stat` 已改为同一 canonical
  `Byte.int`；Task Pend/wake/cleanup 和 Tick 已接入完整字节的操作与 image 对应。
  数组借用、全部等待/ready 操作及 Multi-enabled 全局不变式仍未闭合，不能把这些模型
  接口记为完整函数验证；各批检查证据以 foundation 为准。
- `task_tcb_init_spec.v` 已完成上述完整布局的消费者适配：同一 free/private image 贯穿
  摘取、初始化与发布，配置化 links/table/map 不再混用固定 64 字节节点所有权。
  Multi 的两次 NULL store 位于 EventPtr 之后，关闭时没有对应的物理写入；QCP-backed
  字段 partition 保留旧 FlagsRdy、padding 和实际未写部分，发布按当前布局的字段一致性
  接回 used node。该增量在本轮字段/接口重构前已通过完整依赖检查；当前重构检查状态以
  foundation 本轮记录为准。这是模型规约证据，不是旧 TCBInit C/manual 迁移或整个
  TaskCreate/Ext、平台与全配置验证完成。
- Suspend/Resume 的 selected-live-TCB 核心更新使用 `atomic_task_*_selected`；仅更新真实
  status/ready 字段，保留完整配置 image 的其余部分及物理调度缓存。Resume 的“无 pending”
  指 `Stat & PEND_ANY == 0`，并非完整 Stat 为零；MULTI 位与剩余 SEM/MBOX/Q 位必须区分。
  函数层的 `task_suspend_spec.v`/`task_resume_spec.v` 已给出参数检查、临界区内的
  SELF/current/priority-table 选择和有序错误/成功关系，证明确定性、错误帧及全局重组。
  两个阶段不能直接当作整个 API 的原子步；Save/Restore、trace 与调度续体仍须组合，
  不能把这些模型记为整函数已验证。Resume 的 ready 分支结果保存为局部值，退出临界区
  后另读 `OSRunning` 决定是否请求调度，不重读 TCB 或复用旧 running 快照。
  当前选定配置的全局保持与资源重组已由 `UCOS2_inv_merge_task_suspend`/`_resume`
  接通；保留位约束来自全局 `task_reserved_bits_clear` 的建立/保持，不是新增运行时 guard。
  两个 spec 的 `task_*_critical_client_certificate` 已证明其现有环境接口实例的全局保持、
  私有创建资源 frame 和 invocation 身份保持，不代表被挂起的调用立即能够继续执行。
  Suspend 的 live-current 读取前提及这些动作的真实调用嵌入仍须在 caller 边界建立。
- “直接调用”省略公共 ENTER/EXIT、安全异常与 Trace 宏（其原始位置/条件仍须在调用绑定中保留）。
  间接 Timer callback 另明确标出；callee 列不承诺每个配置、每条路径都会调用。
- Core/Task/Sem/Mbox/Flag/Memory/Time/Timer/Debug 读取了完整执行体与条件分支；Mutex/Queue
  复用了冻结 input 已允许的既有整族审查并重核当前结构相关路径，不声称这两族本轮全部从头重读。
  main 另以原始源码定义独立清点，函数名/行号/单元与 catalog 的126项一致。
- 依据为 [source-only intake](../../reports/del_full-20260909141749/rounds/del_full-annotation-r1/agent_report.json)
  的 `agent_result.annotation.source_function_inventory.function_family_catalog`。其 owner
  如实报告模型缺口，**不是 controller acceptance**；本清单只作设计和源码覆盖导航。

## os_core.c（35 个定义）

初始化资源组合补充：`core/spec/kernel_boot_spec.v` 将现有初始化端点的真实空间资源
汇合到 `UCOS2_boot_state` 的全局不变式，固定检查 `check-r0b0nu5x.json` 通过并采用。
OSCPUUsage/OSTickStepState 零值、名称字节及 Memory 初始池是明确输入，不将未证明的
初始化调用或系统任务创建当作已完成。证据见 `reports/kernel-model-20260924/boot-integration/`。

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSEventNameGet](/tmp/ucos2-official-audit-20260802/Source/os_core.c:117) | `(OS_EVENT_EN) && (OS_EVENT_NAME_EN > 0u)` | Event：按 event/output/ISR/type 的源码顺序检查；临界区读取名称指针及 NUL 字符串长度（u8），不复制名称。借用共享名称字节。 | `OS_StrLen` |
| [OSEventNameSet](/tmp/ucos2-official-audit-20260802/Source/os_core.c:197) | `(OS_EVENT_EN) && (OS_EVENT_NAME_EN > 0u)` | Event：按 event/name/ISR/type 检查；临界区仅替换名称指针。新名称存活期与旧名称归还由共享名称资源协议连接。 | — |
| [OSEventPendMulti](/tmp/ucos2-official-audit-20260802/Source/os_core.c:320) | `((OS_EVENT_EN) && (OS_EVENT_MULTI_EN > 0u))` | Event/Task/Sched：按输入数组/首项/输出数组 guards、清 ready[0]、全数组类型检查、ISR/lock 的顺序处理；保留 NULL 终止输入及输出权限。按输入顺序取得全部就绪 Sem/Mbox/Q（含重复项的真实效果），写结果前缀和终止项；u16 返回计数与实际写入长度分开，是否等待取独立 events_rdy。否则登记/阻塞；同一 invocation 恢复后精确 wake/abort/timeout、全组清理及早退前已写输出。 | `OS_EventTaskWaitMulti`、`OS_Sched`、`OS_EventTaskRemoveMulti` |
| [OSInit](/tmp/ucos2-official-audit-20260802/Source/os_core.c:582) | 无外层 guard | Boot/all：按源码依次调用 hook、Misc/Ready/TCB/Event、Flag/Memory/Q、条件 TLS、Idle/Stat/Timer、end hook/debug。TLS 失败可部分初始化返回；其他被忽略的创建错误须从具体 boot 资源推导成功，不能假设入口已满足运行态不变式。 | `OSInitHookBegin`、`OS_InitMisc`、`OS_InitRdyList`、`OS_InitTCBList`、`OS_InitEventList`、`OS_FlagInit`、`OS_MemInit`、`OS_QInit`、`OS_TLS_Init`、`OS_InitTaskIdle`、`OS_InitTaskStat`、`OSTmr_Init`、`OSInitHookEnd`、`OSDebugInit` |
| [OSIntEnter](/tmp/ucos2-official-audit-20260802/Source/os_core.c:663) | 无外层 guard | Intr/Sched：[int_enter_spec](../VC/code_proof/interrupt/spec/int_enter_spec.v) 复用 running 且 nesting<255 才递增的共享转换、UChar 范围与全局资源重组；自身没有 Save/Restore，入口中断屏蔽/调用配对来自平台及 ISR 协议。当前关闭的 trace 若启用需接真实调用契约。 | — |
| [OSIntExit](/tmp/ucos2-official-audit-20260802/Source/os_core.c:693) | 无外层 guard | Intr/Sched/Task：[int_exit_spec](../VC/code_proof/interrupt/spec/int_exit_spec.v) 保留 Save 前 running 分支和 Save 后的 nesting 递减；old nesting=0/1 且 lock=0 时均可选择，复用 high cache/counter 的源码准备端点及有条件的全局重组。比较真实 high/current priority 字节；OSIntCtxSw、trace/TLS 和 ISR 返回仍是后续调用组合。 | `OS_SchedNew`、`OS_TLS_TaskSw`、`OSIntCtxSw` |
| [OSSafetyCriticalStart](/tmp/ucos2-official-audit-20260802/Source/os_core.c:757) | `defined(OS_SAFETY_CRITICAL_IEC61508)` | Boot：直接写 started=TRUE；源码没有 ENTER/EXIT。同步/启动时序另由调用者提供，后续 Create/Delete 的实际 guard 单独编码。 | — |
| [OSSchedLock](/tmp/ucos2-official-audit-20260802/Source/os_core.c:782) | `OS_SCHED_LOCK_EN > 0u` | Intr/Sched：[sched_lock_spec](../VC/code_proof/sched/spec/sched_lock_spec.v) 保留 Save 前 running 观察；临界区中非 ISR 且 lock<255 才递增，其他分支不递增，并重组真实计数单元与全局残余资源。Save/Restore 仍需平台绑定，调度锁不等于持续屏蔽中断。 | — |
| [OSSchedUnlock](/tmp/ucos2-official-audit-20260802/Source/os_core.c:819) | `OS_SCHED_LOCK_EN > 0u` | Intr/Sched/Task：[sched_lock_spec](../VC/code_proof/sched/spec/sched_lock_spec.v) 保留 Save 前 running 观察、非 ISR 时递减正 lock，以及全部非目标资源。仅 old lock=1 请求 Restore 后的 OS_Sched；old lock=0 不请求。请求来自既走分支，后续选择必须使用新调用自己的状态，不能把 checkpoint 当成整个解锁返回。 | `OS_Sched` |
| [OSStart](/tmp/ucos2-official-audit-20260802/Source/os_core.c:869) | 无外层 guard | Boot/Sched/Task：未 running 时选择最高 ready 并写 current/high 指针和缓存优先级，调用 OSStartHighRdy；平台的启动、不返回/切换及 OSRunning 更新显式绑定。 | `OS_SchedNew`、`OSStartHighRdy` |
| [OSStatInit](/tmp/ucos2-official-audit-20260802/Source/os_core.c:902) | `OS_TASK_STAT_EN > 0u` | Statistics/Tick/Task/Sched：延迟 2 ticks、清 idle counter，再延迟 tick_hz/10，复制 Max 并置 StatRdy；包含两次真实阻塞恢复和干扰区间。 | `OSTimeDly` |
| [OSTimeTick](/tmp/ucos2-official-audit-20260802/Source/os_core.c:937) | 无外层 guard | Tick/Task/Sched/Event/Flag：实际 tick hook 后按配置使 OSTime u32 加一；未 running 或 step-WAIT 也保留该时间更新。[tick.v](../lib/tick.v) 的 `tick_task_step` 已组合单 cursor 的真实更新：旧 delay=0 不改 Task/Sched；非零递减并在归零时处理 PEND_ANY/result，再仅按 suspension 设置 ready，保留 MULTI 位及 Event/Flag 登记。Task/Event owner、跨模块关系和 Event 位图表示运输已证明；no-Multi 协议下可保持删除的 ready-excluded 阶段。外层配置、hooks、idle-tail/跨 Restore cursor 存活及整段遍历仍须组合。 | `OSTimeTickHook` |
| [OSVersion](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1025) | 无外层 guard | Config：返回 OS_VERSION=29301；无内核状态写入。 | — |
| [OS_Dummy](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1044) | `OS_TASK_DEL_EN > 0u` | None：空函数体；其前后的 Restore/reenter 间隔仍允许实际环境干扰，不能把整个间隔视为 no-op。TaskDelete spec 的已建模核心干扰闭包已运输保存 TCB/table/调用身份与私有资源，并连接实际 lock 增减：入口 255 最终为 254，只有未饱和时恢复原 lock。该闭包不代表全部 ISR/hook 或两个 Save 的 CPSR 值相同。 | — |
| [OS_EventTaskRdy](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1078) | `(OS_EVENT_EN)` | Event/Task/Sched：从 Event 位图选 priority，再经真实 priority table 选 TCB；dly=0、写传入 msg/result、清指定 mask、按 suspension 设置 ready，移除单/Multi 等待；返回选中的 priority，不是任意新 priority。event_multi_wake_selected_step 表达已选定且 MultiPtr 非 NULL 的后缀，保留其他 pending 位仍可 ready 的行为；不代替 selector、借用存活或全局保持。 | `OS_EventTaskRemove`、`OS_EventTaskRemoveMulti` |
| [OS_EventTaskWait](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1156) | `(OS_EVENT_EN)` | Event/Task/Sched：先写 EventPtr，再 OR Event 行/组，清 ready 行并条件清组；不刷新 current/high-ready 缓存。caller 已写 Stat/StatPend=OK/Dly，入口允许 TCB 已 pending 而 ready 位尚未清除的阶段，保留 IRQ 权限。 | — |
| [OS_EventTaskWaitMulti](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1192) | `((OS_EVENT_EN) && (OS_EVENT_MULTI_EN > 0u))` | Event/Task/Sched：MultiPtr 写真实输入数组基址、MultiRdy=0；按原顺序（允许重复）OR 各 Event 的 row/group，最后清 ready；不写 Stat/StatPend/Dly。event_multi_wait_step 已组合三个 owner，保留 common TCB 字段和调度缓存，并建立该 Task 的完整 Event wait-set；条件 TCB 两字段接到 72 字节局部表示。仍需全局配置/Task 状态推广及跨阻塞数组/Task 存活。 | — |
| [OS_EventTaskRemove](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1237) | `(OS_EVENT_EN)` | Event/Task：按 TCB 的实际坐标清 Event bit；仅该行变零时清 group bit；末尾清 `OSTCBEventPtr`，不改 Task status。`OS_EventTaskRdy` 的回指清理由此 callee 完成。 | — |
| [OS_EventTaskRemoveMulti](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1269) | `((OS_EVENT_EN) && (OS_EVENT_MULTI_EN > 0u))` | Event/Task：缓存 TCB 坐标/bit，按 NULL 终止输入的原顺序清 row，行变零才清 group；包括重复指针及已移除 waiter。event_multi.v 连接逐项 image 写入与逻辑整组清理；本 helper 不写任何 TCB 字段或输入数组，MultiPtr/MultiRdy 清理由实际 caller 执行。 | — |
| [OS_EventWaitListInit](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1310) | `(OS_EVENT_EN)` | Event：先写 grp=0，再逐行 typed store 清表；`event_wait_table_init_prefix`/`event_wait_list_init_image` 连接当前八行 UChar 布局、已写前缀与真实写后 merge。不是 OS_MemClr，不改 type/count/ptr/name/padding，也不分配 Event。其他行宽/配置实例仍需绑定。 | — |
| [OS_InitEventList](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1336) | 无外层 guard | Event：清 ECB 池并用 OSEventPtr 串接 free list、发布 root；内部条件区分单节点和未启用 Event，不拥有其他池。 | `OS_MemClr` |
| [OS_InitMisc](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1389) | 无外层 guard | Boot/Intr/Sched/Task/Tick/Statistics：只初始化源码实际写入的 running/int/lock/time/task/idle/stat/register/安全控制字段；不声称完整模块 invariant 已建立，不凭空重置 CPUUsage 等未写字段。 | — |
| [OS_InitRdyList](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1434) | 无外层 guard | Sched：清 ready group/rows，初始化 physical current/high caches；boot 阶段允许 NULL cache 和空 ready。 | — |
| [OS_InitTaskIdle](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1465) | 无外层 guard | Task/Sched/Statistics：按所选 CreateExt/Create 建立 idle（当前 prio63、实际栈/ID/options），条件 NameSet；忽略的错误须由 fresh boot 的容量和槽位事实消解。 | `OSTaskCreateExt`、`OSTaskCreate`、`OSTaskNameSet` |
| [OS_InitTaskStat](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1528) | `OS_TASK_STAT_EN > 0u` | Task/Sched/Statistics：按配置创建 stat task（当前 prio62），绑定实际栈/ID/options 和名称；具体 boot 需证明创建成功。 | `OSTaskCreateExt`、`OSTaskCreate`、`OSTaskNameSet` |
| [OS_InitTCBList](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1591) | 无外层 guard | Task：清 TCB 池和 priority table、串接 free next、初始化条件 names；还没有 published task。free image 与 private allocation 已共用完整配置 image；Multi-off/on 的 slot stride 分别为 64/72，boot 复用同一零初始化与 Next/Name 写入定义，不另建条件字段存储表。 | `OS_MemClr` |
| [OS_MemClr](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1640) | 无外层 guard | Bytes：对 caller-owned 区间恰写 INT16U size 个零字节；不是内存分配。 | — |
| [OS_MemCopy](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1674) | 无外层 guard | Bytes：恰执行 size 个正向逐字节复制；只有适当 alias 条件才等价于快照复制。Query 的 native 字段/填充必须保留，不当作 memmove。 | — |
| [OS_Sched](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1702) | 无外层 guard | Sched/Intr/Task：临界区内 int/lock 非零则不刷新 high cache；否则位图/table 选择并比较真实 high/current 缓存字节，不切换也更新 high 缓存。[sched_spec](../VC/code_proof/sched/spec/sched_spec.v) 表达外部调用前的计数回绕/物理端点及有条件的全局接回，不增加 OSRunning/空 ready guard，不提前写 current caches。实际 OS_TASK_SW/TLS、profile TCB 计数与原 invocation 恢复/终止仍须相应契约。 | `OS_SchedNew`、`OS_TLS_TaskSw`、`OS_TASK_SW` |
| [OS_SchedNew](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1751) | 无外层 guard | Sched：按 narrow/wide 位图和 OSUnMapTbl 算最高 ready priority；本函数只写 high-priority scalar，不写 high pointer。 | — |
| [OS_StrLen](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1796) | `(OS_EVENT_NAME_EN > 0u) \|\| (OS_FLAG_NAME_EN > 0u) \|\| (OS_MEM_NAME_EN > 0u) \|\| (OS_TASK_NAME_EN > 0u) \|\| (OS_TMR_CFG_NAME_EN > 0u)` | Bytes/Config：ArgCheck 开时 NULL 返回 0；关时没有该安全分支。对实际有限 NUL 字符串扫描，u8 累计返回长度 mod256，调用者提供全部读取权限。 | — |
| [OS_TaskIdle](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1838) | 无外层 guard | Statistics/Intr/Task：无限循环：临界区 OSIdleCtr u32 加一，然后实际 idle hook；不要求正常返回。 | `OSTaskIdleHook` |
| [OS_TaskStat](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1879) | `OS_TASK_STAT_EN > 0u` | Statistics/Task/Tick/Sched：等待 ready、Max/=100；零值自我 suspend 后可能再次 Resume。按真实采样延迟、unsigned 除法及 INT8S 窄化计算 CPUUsage/修正 Max，调用 hook/stack check；不能无来源要求分母恒正或 usage<=100。 | `OSTimeDly`、`OSTaskSuspend`、`OSTaskStatHook`、`OS_TaskStatStkChk` |
| [OS_TaskStatStkChk](/tmp/ucos2-official-audit-20260802/Source/os_core.c:1949) | `(OS_TASK_STAT_STK_CHK_EN > 0u) && (OS_TASK_CREATE_EXT_EN > 0u)` | Task/Statistics：遍历包括 idle 的全部 priority，调用 StkChk 后重新读取当前 table；profile 开时才写栈统计字段，需保护两次观察的实例关系。 | `OSTaskStkChk` |
| [OS_TCBInit](/tmp/ucos2-official-audit-20260802/Source/os_core.c:2022) | 无外层 guard | Task/Sched：按选定 atomic-publication 变体摘 private TCB、初始化全部实际字段、调用两个已选 creation hooks；临界区 commit active list/ready/count/table。区分 pool-empty、原 invocation 和 publication，原始函数行号不代表原版与修复版等价。 | `OSTCBInitHook`、`OSTaskCreateHook`、`OS_TLS_TaskCreate` |

## os_task.c（16 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSTaskChangePrio](/tmp/ucos2-official-audit-20260802/Source/os_task.c:60) | `OS_TASK_CHANGE_PRIO_EN > 0u` | Task/Sched/Event/Flag/Mutex：按优先级/源槽 guard 迁移 table、ready 和单/Multi Event 等待位；源码未写 OSPrioCur 时保留旧缓存。持锁者的 permanent/alias 协议另证，不添加 runtime guard。 | `OS_Sched` |
| [OSTaskCreate](/tmp/ucos2-official-audit-20260802/Source/os_task.c:219) | `OS_TASK_CREATE_EN > 0u` | Task/Sched：`task_create_spec` 保留 IEC→priority→Save 后 ISR/table 顺序、零扩展参数、TCBInit 返回及 trace 后新 OSRunning 观察。`task_create_lifecycle_spec` 连接实际 caller origin、预留与 TCBInit entry；`task_create_return_spec` 连接0/66和消费当前零值表项的失败回滚，不恢复旧快照。默认空 trace 不读取其参数。各文件联合检查状态见 foundation；完整 Save/Restore、栈/trace/schedule 调用资源尚需组合。 | `OSTaskStkInit`、`OS_TCBInit`、`OS_Sched` |
| [OSTaskCreateExt](/tmp/ucos2-official-audit-20260802/Source/os_task.c:347) | `OS_TASK_CREATE_EXT_EN > 0u` | Task/Sched：复用同一创建生命周期与返回接口；实际 bottom/size/ext/id/opt 传给初始化，stack-clear 条件绑定 OS_TASK_STAT_STK_CHK_EN 而非 statistics 总开关。错误分支没有基本版的 failed-trace 调用点；字段、填充、TLS 和平台调用仍按选定配置/实际资源绑定，不把参数化调用关系当作实现证明。 | `OS_TaskStkClr`、`OSTaskStkInit`、`OS_TCBInit`、`OS_Sched` |
| [OSTaskDel](/tmp/ucos2-official-audit-20260802/Source/os_task.c:450) | `OS_TASK_DEL_EN > 0u` | Task/Sched/Event/Flag/Mutex：[task_delete_spec](../VC/code_proof/task/spec/task_delete_spec.v) 保留 safety/ISR/idle/priority 顺序及实际 SELF/table 读取；单等待清理与三字段准备已建立 owner/跨模块关系、ready-excluded 阶段及保留 Flag 节点资源的堆重组。[task_retirement](../lib/task_retirement.v) 提供源序链/count/table/free 回收与 QCP-backed 堆归还。准备阶段可推出等待登记清空；未持锁时回收后 Task/Sched/Event/Flag/Mutex 关系及 Event 位图下标可恢复，只清捕获的真实 priority 槽，不新增 C guard。共享阶段复用完整全局资源，仅替换 ready 性质；Tick、Event/Flag 唤醒及中断计数核心步的有限闭包保持阶段与 lock，正 lock 阻止 IntExit 调度，有条件回收恢复普通全局有效性。真实 bitmap/table、node/TCB 对应推出被选 waiter 不同于删除目标，Flag 返回 false 仍摘链。该集合不穷尽全部 ISR；实际 Restore/token、其他合法 ISR/协议保持、Multi、hooks 和自删停止/调度续体仍须组合，移除 live map 不等于已经停止。 | `OS_EventTaskRemove`、`OS_EventTaskRemoveMulti`、`OS_FlagUnlink`、`OS_Dummy`、`OSTaskDelHook`、`OS_TLS_TaskDel`、`OS_Sched` |
| [OSTaskDelReq](/tmp/ucos2-official-audit-20260802/Source/os_task.c:613) | `OS_TASK_DEL_EN > 0u` | Task：SELF 查询当前 delete request；其他 live task 设置 request。精确 idle/无 Task/reserved/priority 返回，不执行真正删除。 | — |
| [OSTaskNameGet](/tmp/ucos2-official-audit-20260802/Source/os_task.c:688) | `OS_TASK_NAME_EN > 0u` | Task：检查 output/priority/ISR 及 lookup；临界区返回借用名称指针和 u8 长度，不复制字符串。 | `OS_StrLen` |
| [OSTaskNameSet](/tmp/ucos2-official-audit-20260802/Source/os_task.c:770) | `OS_TASK_NAME_EN > 0u` | Task：检查 priority/name/ISR 及 lookup；临界区换指针、调用 trace；不存在 Task 分支与存储存活期分别说明。 | — |
| [OSTaskResume](/tmp/ucos2-official-audit-20260802/Source/os_task.c:846) | `OS_TASK_SUSPEND_EN > 0u` | Task/Sched/Intr：只对真实 suspended live 非 idle Task 清 suspend；无 pending 且 delay=0 才设 ready，并按源码条件调度。没有单独禁止恢复 stat priority62。 | `OS_Sched` |
| [OSTaskStkChk](/tmp/ucos2-official-audit-20260802/Source/os_task.c:916) | `(OS_TASK_STAT_STK_CHK_EN > 0u) && (OS_TASK_CREATE_EXT_EN > 0u)` | Task/Bytes：先将输出两字段清零，再检查 live/opt；临界区快照 size/bottom，外部扫描连续零栈字，无 size 上界。安全规约需真实有限非零停止点和栈借用，失败输出不默认未改。 | — |
| [OSTaskSuspend](/tmp/ucos2-official-audit-20260802/Source/os_task.c:1002) | `OS_TASK_SUSPEND_EN > 0u` | Task/Sched：解析 SELF/current，拒绝 idle/空/reserved；清 ready 并设 suspend，仅对当前 Task 调度，保留 delay/pend 和等待拓扑。 | `OS_Sched` |
| [OSTaskQuery](/tmp/ucos2-official-audit-20260802/Source/os_task.c:1078) | `OS_TASK_QUERY_EN > 0u` | Task/Bytes：有序 guard/lookup 后复制 sizeof(OS_TCB) 全字节，包括配置字段和 padding；输出不是只有 priority/status 的抽象快照。 | `OS_MemCopy` |
| [OSTaskRegGet](/tmp/ucos2-official-audit-20260802/Source/os_task.c:1146) | `OS_TASK_REG_TBL_SIZE > 0u` | Task：检查 priority/id，选 current 或 table pointer 后直接读 register；没有 NULL/reserved lookup guard。存活 Task 权限是 caller 义务，不虚构 NOT_EXIST 返回。 | — |
| [OSTaskRegGetID](/tmp/ucos2-official-audit-20260802/Source/os_task.c:1209) | `OS_TASK_REG_TBL_SIZE > 0u` | Task：临界区分配 next register ID，至 table size 耗尽返回对应错误；返回旧 u8 ID，表示 NextAvailID 全局。 | — |
| [OSTaskRegSet](/tmp/ucos2-official-audit-20260802/Source/os_task.c:1269) | `OS_TASK_REG_TBL_SIZE > 0u` | Task：与 RegGet 相同的实际 lookup 边界，写一个 u32 register 和 perr；不隐含 Task 存在性检查。 | — |
| [OS_TaskReturn](/tmp/ucos2-official-audit-20260802/Source/os_task.c:1327) | 无外层 guard | Task/Sched：真实 return hook 后按配置 self-delete，或无限延迟循环；不能承诺原 Task 正常返回且继续存活。 | `OSTaskReturnHook`、`OSTaskDel`、`OSTimeDly` |
| [OS_TaskStkClr](/tmp/ucos2-official-audit-20260802/Source/os_task.c:1364) | `(OS_TASK_STAT_STK_CHK_EN > 0u) && (OS_TASK_CREATE_EXT_EN > 0u)` | Task/Bytes：`task_stack_clear_spec` 描述先CHK再CLR、size-- 后写零/后增、精确循环步数和最终全零；复用 copy_prefix_list/UIntArray.mixed_full 保留未初始化后缀及实际写后合回。当前仅 growth=1/32-bit OS_STK，数值范围不代替数组对象/provenance与C语义对应；growth=0需另审one-before指针。联合检查状态见 foundation。 | — |

## os_mutex.c（7 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSMutexAccept](/tmp/ucos2-official-audit-20260802/Source/os_mutex.c:93) | `OS_MUTEX_EN > 0u` ∧ `OS_MUTEX_ACCEPT_EN > 0u` | Event/Mutex/Task：有序 NULL/type/ISR 检查；available 时写 owner 和获取时 priority 快照，即使 perr=PCP_LOWER 也已获取并返回 TRUE；不可用返回 FALSE/NONE。 | — |
| [OSMutexCreate](/tmp/ucos2-official-audit-20260802/Source/os_mutex.c:187) | `OS_MUTEX_EN > 0u` | Event/Mutex/Task：可选 safety 检查后先验证 enabled PCP 范围，再 ISR；预留 PCP、摘 private ECB/初始化，池空回滚。255 为 disabled tag，不是索引；区分 creator/permanent/PCP 槽。 | `OS_EventWaitListInit` |
| [OSMutexDel](/tmp/ucos2-official-audit-20260802/Source/os_mutex.c:301) | `OS_MUTEX_EN > 0u` ∧ `OS_MUTEX_DEL_EN > 0u` | Event/Mutex/Task/Sched：采用所选 nested repair：NULL/type/ISR，再 opt/wait；先释放自身 enabled PCP，再扫描剩余 aliases、按需保持 ready-membership 地迁移 owner，精确 abort/wake/free。NO_PEND 允许 suspended owner；返回旧指针/NULL、perr 及条件调度绑定源码。 | `OSMutex_RdyAtPrio`、`OS_EventTaskRdy`、`OS_Sched`、`OSMutex_EffectivePrio（所选变体）` |
| [OSMutexPend](/tmp/ucos2-official-audit-20260802/Source/os_mutex.c:467) | `OS_MUTEX_EN > 0u` | Event/Mutex/Task/Sched：立即获取保存真实快照；contested owner 用最大 alias 作为 base，记录 qualifying masked PCP demand，按源码提升/登记/阻塞/恢复。timeout 不直接撤销已锁存 demand，owner 协议和所有返回分支分开。 | `OS_EventTaskWait`、`OS_Sched`、`OS_EventTaskRemove`、`OSMutex_BasePrio（所选变体）` |
| [OSMutexPost](/tmp/ucos2-official-audit-20260802/Source/os_mutex.c:642) | `OS_MUTEX_EN > 0u` | Event/Mutex/Task/Sched：NULL/type/ISR/current-owner guard；先将自身 PCP 设 reserved，再扫描/迁移；若有 waiter 用 EventTaskRdy(NULL,mutex,OK) 的返回 priority 写 owner/count，否则设 available。不虚构额外 cache refresh。 | `OSMutex_RdyAtPrio`、`OS_EventTaskRdy`、`OS_Sched`、`OSMutex_EffectivePrio（所选变体）` |
| [OSMutexQuery](/tmp/ucos2-official-audit-20260802/Source/os_mutex.c:727) | `OS_MUTEX_EN > 0u` ∧ `OS_MUTEX_QUERY_EN > 0u` | Event/Mutex/Task：ISR 检查先于 NULL event/output/type；临界区复制 PCP、高/低字节快照、OSValue=(lowbyte=255) 与配置 wait bitmap，不是 base-priority query。 | — |
| [OSMutex_RdyAtPrio](/tmp/ucos2-official-audit-20260802/Source/os_mutex.c:787) | `OS_MUTEX_EN > 0u` | Task/Sched/Mutex：所选 helper 保存实际旧 ready membership；只在原本 ready 时迁移位图，写 priority/坐标/table，仅 ptcb=OSTCBCur 才写 OSPrioCur；不写 Event/Flag 链或 high cache。 | — |

## os_sem.c（8 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSSemAccept](/tmp/ucos2-official-audit-20260802/Source/os_sem.c:57) | `OS_SEM_EN > 0u` ∧ `OS_SEM_ACCEPT_EN > 0u` | Event：NULL/type 返回0；否则临界区返回旧 count，正数才减一；无 ISR 拒绝。 | — |
| [OSSemCreate](/tmp/ucos2-official-audit-20260802/Source/os_sem.c:102) | `OS_SEM_EN > 0u` | Event：IEC 检查后拒绝 ISR，无 lock guard/perr；共享 `event_create_spec` 分开临界区 free-pop、Restore 后 Type/Cnt/Ptr/[Name]/Grp/rows 私有写入与最终发布。`sem/spec/sem_create_spec.v` 绑定传入 INT16U count、NULL Ptr、实际 generation/padding 和全局资源交接。空池返回 NULL；不把私有字段序列当整调用原子步，环境/trace/发布时刻与其他配置仍待组合。 | `OS_EventWaitListInit` |
| [OSSemDel](/tmp/ucos2-official-audit-20260802/Source/os_sem.c:185) | `OS_SEM_EN > 0u` ∧ `OS_SEM_DEL_EN > 0u` | Event/Task/Sched：NULL/type/ISR 后按 opt/wait；NO_PEND 无 waiter 才回收，ALWAYS 精确 abort 全部后回收；错误返回旧指针、成功 NULL，按初始等待情况调度。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSSemPend](/tmp/ucos2-official-audit-20260802/Source/os_sem.c:321) | `OS_SEM_EN > 0u` | Event/Task/Sched：NULL/type/ISR/lock 顺序检查；count>0 立即减一，否则写 pend/delay、登记并阻塞；原 invocation 恢复后区分 success/abort/timeout，timeout 清残留链。 | `OS_EventTaskWait`、`OS_Sched`、`OS_EventTaskRemove` |
| [OSSemPendAbort](/tmp/ucos2-official-audit-20260802/Source/os_sem.c:439) | `OS_SEM_EN > 0u` ∧ `OS_SEM_PEND_ABORT_EN > 0u` | Event/Task/Sched：NULL/type，无 ISR 拒绝；无 waiter 返回0/NONE。仅 opt 恰等 BROADCAST 才 abort 全部，其他值 abort 一个；有 abort 时精确计数/PEND_ABORT 并调度。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSSemPost](/tmp/ucos2-official-audit-20260802/Source/os_sem.c:513) | `OS_SEM_EN > 0u` | Event/Task/Sched：NULL/type 后优先唤醒 waiter 并调度；无 waiter 且 count<65535 才增一，否则 overflow 不改 count。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSSemQuery](/tmp/ucos2-official-audit-20260802/Source/os_sem.c:574) | `OS_SEM_EN > 0u` ∧ `OS_SEM_QUERY_EN > 0u` | Event/Bytes：NULL event、NULL output、type 顺序检查，无 ISR 禁止；临界区复制 group/全部配置行/count，返回观察点快照。 | — |
| [OSSemSet](/tmp/ucos2-official-audit-20260802/Source/os_sem.c:636) | `OS_SEM_EN > 0u` ∧ `OS_SEM_SET_EN > 0u` | Event：NULL/type 后，旧 count>0 直接赋新值，不先查看 waiter；旧 count=0 时 grp=0 才赋值，否则 TASK_WAITING；不唤醒。 | — |

Sem/Mbox/Queue 的 PendAbort 现分别由
[`sem_pend_abort_spec.v`](../VC/code_proof/sem/spec/sem_pend_abort_spec.v)、
[`mbox_pend_abort_spec.v`](../VC/code_proof/mbox/spec/mbox_pend_abort_spec.v)、
[`q_pend_abort_spec.v`](../VC/code_proof/queue/spec/q_pend_abort_spec.v) 绑定各自 type/mask，
共用 [`event_pend_abort_spec.v`](../VC/code_proof/event/spec/event_pend_abort_spec.v)。
模型保留 INT8U 计数回绕；当前 Task 池上界证明不会溢出，并得到精确 abort 数、返回码及
是否请求 OS_Sched。Event payload、Queue buffer、非等待者及调用身份保持有共享证明，
实际写后的 TCB/ready/ECB 堆由 caller 提供再重组。它是当前 native 模型增量，不是旧 Sem
proof 迁移或三个 C 函数已完成验证；Save/Restore/调度返回、perr 权限及 Multi 仍须组合。

Sem 的 Accept/Set/Post 临界区模型现分别位于
[`sem_accept_spec.v`](../VC/code_proof/sem/spec/sem_accept_spec.v)、
[`sem_set_spec.v`](../VC/code_proof/sem/spec/sem_set_spec.v)、
[`sem_post_spec.v`](../VC/code_proof/sem/spec/sem_post_spec.v)。共用 [`lib/sem.v`](../lib/sem.v)
的共同计数更新与 Event/QCP 字段拆合，不导入其他公有函数的 spec。Accept 观察旧计数；
Set 保留 count-first/bitmap-second 及 Restore 前 perr 写入顺序；Post 复用真实单 waiter
唤醒，只有无 waiter 才增加计数，溢出分支保持内核状态。
全局 count merge 消费新 UShort cell，Post merge 消费实际更新后的 TCB/ready/ECB
资源；Queue 及其他模块保留在 residual 中。检查范围见 foundation；完整调用组合和
旧 Sem spec/manual 的迁移仍未完成，模型结果不等于这三个 C 函数已经重新验证。

[`sem_pend_spec.v`](../VC/code_proof/sem/spec/sem_pend_spec.v) 分开首个临界区与调度返回后的
临界区。立即取得复用共同计数减一；等待复用 Event 登记，保留实际 TCB generation。
超时从既有 reference closure/backlink 取得仍存活的 Event 再 Remove；成功/abort 不读
旧 Event，因此不额外要求已被 Delete 回收的 Sem 继续存在。返回清理复用 Task 公共
`task_event_pend_cleanup`，按 Sem 源码保留 Msg/Dly，不照搬 Queue 的 Msg=NULL。
立即分支的 perr 在 Restore 后写入，返回 switch 的 perr 在 Restore 前写入；raw default
仍为 timeout。存在性、确定性、全局保持、原 invocation 与真实写后资源重组的检查见
foundation。返回边界/原调用存活是后续调用组合的义务，不是已证明 OS_Sched 必定返回；
完整入口、trace/平台、perr 存活资源、Multi 全局实例及旧 C/manual 迁移仍未完成。

SemDel 与 MboxDel 的同构删除主体共用
[`event_delete_spec.v`](../VC/code_proof/event/spec/event_delete_spec.v)，由
[`sem_delete_spec.v`](../VC/code_proof/sem/spec/sem_delete_spec.v) 和
[`mbox_delete_spec.v`](../VC/code_proof/mbox/spec/mbox_delete_spec.v) 绑定实际 type/mask。
仅 opt=0/1 有效；NO_PEND 的 TASK_WAITING 和 invalid-option 均保留原句柄/状态；
ALWAYS 按当前位图逐个 abort，再按 Type/Ptr/Cnt/free-root 的源序回收。
调度请求使用循环前的 tasks_waiting；成功 NULL、perr 及 trace/调用返回仍在 Restore 后组合。
共享资源证明保留所有 Queue 资源，不将 ECB-only 删除套用于 Mutex 的 owner/PCP 或 Queue
的 QCB/buffer 回收。检查范围见 foundation；当前 names-disabled 模型不等于 C 函数整体已验证。

## os_q.c（11 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSQAccept](/tmp/ucos2-official-audit-20260802/Source/os_q.c:70) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` ∧ `OS_Q_ACCEPT_EN > 0u` | Event/Queue：NULL/type；非空取最旧槽（可为 NULL）并返回 NONE，推进/回绕 Out、entries--；空为 NULL/Q_EMPTY。旧槽字节不清。 | — |
| [OSQCreate](/tmp/ucos2-official-audit-20260802/Source/os_q.c:136) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` | Event/Queue：`q_create_lifecycle_spec.v` 复用第一次 ECB pop，按第二次 Save 的实际 QCB free list 分支；耗尽时把 UNUSED ECB 接回当前空闲链，不恢复旧快照。成功时私有 QCB/ECB 初始化后消费实际字节与 caller buffer 发布，保留 OSQPtr。无 size0/startNULL 参数检查；完整平台/trace/调用与其他配置尚待组合，不等于旧 C/manual 已迁移。 | `OS_EventWaitListInit` |
| [OSQDel](/tmp/ucos2-official-audit-20260802/Source/os_q.c:241) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` ∧ `OS_Q_DEL_EN > 0u` | Event/Queue/Task/Sched：NULL/type/ISR/opt；NO_PEND 拒绝 waiter，ALWAYS abort；先经 OSQPtr 回收 QCB，再经 OSEventPtr 回收 ECB，按协议归还 buffer 权限但不声称调用 free。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSQFlush](/tmp/ucos2-official-audit-20260802/Source/os_q.c:372) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` ∧ `OS_Q_FLUSH_EN > 0u` | Event/Queue：仅将 In/Out 设 Start、entries=0；保留 buffer 字节、End/Size 和等待拓扑，不 wake。`queue_flush_state` 已连接 `UCOS2_queue_flush_preserves_validity`；Event/Queue 写后重组通过共用全局 residual 保留其他所有模块。零容量及原 buffer 字节不被排除；参数分支和 Save/Restore 的完整调用仍须组合。 | — |
| [OSQPend](/tmp/ucos2-official-audit-20260802/Source/os_q.c:436) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` | Event/Queue/Task/Sched：NULL/type/ISR/lock；立即 FIFO pop 可以是 NULL/NONE，否则登记/阻塞。原 invocation 的 TCB message 可为 NULL，靠 perr 区分 OK/abort/timeout 并清理。 | `OS_EventTaskWait`、`OS_Sched`、`OS_EventTaskRemove` |
| [OSQPendAbort](/tmp/ucos2-official-audit-20260802/Source/os_q.c:564) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` ∧ `OS_Q_PEND_ABORT_EN > 0u` | Event/Task/Sched：NULL/type 后仅 opt 恰等 BROADCAST 才 abort 全部，其余一个；精确 count/perr/调度，不改 buffer，无 invalid-option 分支。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSQPost](/tmp/ucos2-official-audit-20260802/Source/os_q.c:641) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` ∧ `OS_Q_POST_EN > 0u` | Event/Queue/Task/Sched：NULL event/type 检查，无 NULL-message 检查。优先 direct handoff；无 waiter 才尾插（可 NULL）、推进 In 或返回 Q_FULL。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSQPostFront](/tmp/ucos2-official-audit-20260802/Source/os_q.c:712) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` ∧ `OS_Q_POST_FRONT_EN > 0u` | Event/Queue/Task/Sched：同样允许 NULL 且优先 direct handoff；无 waiter 时回退/回绕 Out，写新头、entries++，不虚构 In 更新。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSQPostOpt](/tmp/ucos2-official-audit-20260802/Source/os_q.c:792) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` ∧ `OS_Q_POST_OPT_EN > 0u` | Event/Queue/Task/Sched：允许 NULL；按 BROADCAST/NO_SCHED/FRONT 位判断，未知位不拒绝。广播同一指针或单次 handoff，否则精确首/尾插和 full 分支。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSQQuery](/tmp/ucos2-official-audit-20260802/Source/os_q.c:876) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` ∧ `OS_Q_QUERY_EN > 0u` | Event/Queue/Bytes：NULL event/output/type，无 ISR 禁止；临界区复制 wait bitmap、head msg（空时 NULL）、count/size，不 dequeue。 | — |
| [OS_QInit](/tmp/ucos2-official-audit-20260802/Source/os_q.c:936) | `(OS_Q_EN > 0u) && (OS_MAX_QS > 0u)` | Event/Queue：清固定 QCB 池并按 OSQPtr 建 free list；Event 由独立 initializer 建立，不在此取得 caller buffers。 | `OS_MemClr` |

Create 的 Event 与 Task 调用编号分开：`critical_region_event_interval` 在同一环境轨迹中
保护第一次摘出的完整 allocation，再允许第二个临界区继续分配或回滚。Queue action
绑定实际 pool partition 与未占 QCB 的阶段事实，不能由任意“free”列表抢占其他调用的
私有 QCB。源序写后资源重组与纯 action certificate 分别证明；后者不替代实际 C 空间
足迹/Save/Restore 契约。新生命周期模型没有原地改变历史 QCreate 的证明或验收。

源序组合现由 `q_create_failed_reserve_after_environment_merge` 和
`q_create_initialized_publish_merge` 接通：前者从第一次分配及环境运输导出失败归还所需
身份/UNUSED/有效性，后者从私有初始化导出发布所需 pool/reservation/image，而非在后态
重新假定。共同固定检查及主目录采用记录见
`reports/kernel-model-20260924/queue-flag-integration/README.md`。

Post/PostFront/PostOpt 的临界区模型现见
[`q_post_spec.v`](../VC/code_proof/queue/spec/q_post_spec.v)：使用真实 EventGrp 测试与
bitmap/table waiter 选择，广播有有限性、准确接收者及 buffer/非等待者 frame 证明；
这些广播证明已提取到 [`event_wake_spec.v`](../VC/code_proof/event/spec/event_wake_spec.v)，
Post 保留既有观察接口并实例化共享 kind/message/result 参数，与 PendAbort 共用。
无等待者路径复用 canonical ring/QCB 写后重组。精确返回码与是否调用 OS_Sched 分开，
不把调度请求等同于函数已返回。此模型阶段不替代完整 Save/Restore/trace/调度续体或
三个 C 函数的验证；检查范围见 foundation 的本批实施记录。

`OSQPend` 的分段模型见 [`q_pend_spec.v`](../VC/code_proof/queue/spec/q_pend_spec.v)：
立即取实际 FIFO head 且不清 buffer；阻塞登记、超时摘链和返回清理分别连接共享模型。
成功/abort 不要求原 Event 仍存活；清理不改 Dly 或 ready/cache。已有 task-call boundary
提供返回点的 readiness，invocation/generation 单独保留。等待保持使用手册规定的非 idle
调用协议，不能从原生 ready 索引推出；该条件不是 C runtime guard。完整跨调度调用、
输出/栈资源及实际 hook 遵约尚待组合，不能记为整个 OSQPend C 函数已经验证。

`OSQDel` 的分段模型见 [`q_delete_spec.v`](../VC/code_proof/queue/spec/q_delete_spec.v)：
NO_PEND/ALWAYS/invalid 的指针、错误码与调度请求分开，ALWAYS 复用同一 abort 广播。
等待者清空后通过现有 reference backlink 证明可安全去掉 Event map 项；QCB/ECB 回收
复用既有生命周期接口，全局重组消费真实写后资源并返回原 buffer，而非释放它。
原 invocation 与 abort 后的 TCB 保留，不因 Event 回收就宣称调度已经返回。
检查范围见 foundation；上述模型不是 OSQDel 的 C/manual 验证完成。

`OSQAccept` / `OSQQuery` 的临界区接口分别见
[`q_accept_spec.v`](../VC/code_proof/queue/spec/q_accept_spec.v) 与
[`q_query_spec.v`](../VC/code_proof/queue/spec/q_query_spec.v)。Accept 的 head-slot 读取和
出队重组与 Pend 共用，空/成功 NULL 由错误码区分；perr 在 Restore 前写入。
Query 不出队，快照与临界区观察点绑定，非空时取实际 ring slot。输出依源码先 group、
再 typed wait-row loop、最后 message/count/size；QCP mixed-array 接口与既有
`copy_prefix_list` 保存已复制前缀及原后缀，padding 不被凭空覆盖。
当前接口使用八行 UChar profile；wider 配置、入口身份/Save/Restore 及完整输出资源
组合仍在全库目标内，不将这些模型证据计为两个 C 函数的验证完成。

## os_mbox.c（8 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSMboxAccept](/tmp/ucos2-official-audit-20260802/Source/os_mbox.c:56) | `OS_MBOX_EN > 0u` ∧ `OS_MBOX_ACCEPT_EN > 0u` | Event：NULL/type 返回 NULL；否则临界区读取 payload 并清 NULL，即使本来空也执行该写；无 ISR 拒绝。 | — |
| [OSMboxCreate](/tmp/ucos2-official-audit-20260802/Source/os_mbox.c:98) | `OS_MBOX_EN > 0u` | Event：复用 SemCreate 同序的 IEC/ISR、free-pop 和逐字段私有初始化。`mbox/spec/mbox_create_spec.v` 绑定 type=MBOX、count0、任意初始消息（含 NULL）及当前 names-disabled 发布资源；复用 canonical message 编码，ECB 不拥有消息内容。完整环境/trace/发布调用与其他配置仍待组合，不记为 C 函数已验证。 | `OS_EventWaitListInit` |
| [OSMboxDel](/tmp/ucos2-official-audit-20260802/Source/os_mbox.c:179) | `OS_MBOX_EN > 0u` ∧ `OS_MBOX_DEL_EN > 0u` | Event/Task/Sched：Event 删除的真实 NULL/type/ISR/opt/wait 顺序；abort/wake 后 ECB 回收，精确 pointer/perr/调度。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSMboxPend](/tmp/ucos2-official-audit-20260802/Source/os_mbox.c:317) | `OS_MBOX_EN > 0u` | Event/Task/Sched：NULL/type/ISR/lock；非空立即取走并清空，否则阻塞。原 invocation 恢复后返回 TCB message 或 NULL+abort/timeout，保留 cleanup/suspension。 | `OS_EventTaskWait`、`OS_Sched`、`OS_EventTaskRemove` |
| [OSMboxPendAbort](/tmp/ucos2-official-audit-20260802/Source/os_mbox.c:440) | `OS_MBOX_EN > 0u` ∧ `OS_MBOX_PEND_ABORT_EN > 0u` | Event/Task/Sched：NULL/type；仅 opt 恰等 BROADCAST 才 abort 全部，其他一个；精确 count/perr/调度，不改 payload，不拒绝未知 option。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSMboxPost](/tmp/ucos2-official-audit-20260802/Source/os_mbox.c:520) | `OS_MBOX_EN > 0u` ∧ `OS_MBOX_POST_EN > 0u` | Event/Task/Sched：NULL event、NULL msg、type 顺序检查；有 waiter 先 direct handoff，否则空才存消息，full 时不改。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSMboxPostOpt](/tmp/ucos2-official-audit-20260802/Source/os_mbox.c:599) | `OS_MBOX_EN > 0u` ∧ `OS_MBOX_POST_OPT_EN > 0u` | Event/Task/Sched：按 BROADCAST/NO_SCHED bits 处理多个/单个接收者或空/full；广播同一非 NULL 指针，不复制独占消息内容。 | `OS_EventTaskRdy`、`OS_Sched` |
| [OSMboxQuery](/tmp/ucos2-official-audit-20260802/Source/os_mbox.c:672) | `OS_MBOX_EN > 0u` ∧ `OS_MBOX_QUERY_EN > 0u` | Event/Bytes：NULL event/output/type，无 ISR 禁止；临界区复制 wait bitmap 和 payload，输出与所指消息内容的所有权分离。 | — |

MboxDel 的 native 临界区模型现通过
[`mbox_delete_spec.v`](../VC/code_proof/mbox/spec/mbox_delete_spec.v) 复用 Event 删除主体。
它没有 Queue 的 QCB/buffer 操作，也没有 Mutex 的 owner/PCP 修复；覆盖原 message pointer
不表示释放指向的应用内存。abort 的目标、NULL/PendAbort 与 suspension 保留来自共同
Event wake 定理；ECB 被回收后，原 Pend abort 续体仍须由实际调度/调用协议连接。
完整 names/Multi 配置、平台/trace/输出资源、其余 Mbox 操作族和旧证明迁移继续保留。

## os_flag.c（13 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSFlagAccept](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:101) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` ∧ `OS_FLAG_ACCEPT_EN > 0u` | Flag：NULL/type 后拆 CONSUME，SET/CLR ALL/ANY 求 ready bits；ALL 失败仍返回部分交集，zero mask 的 ALL 成功/ANY 失败。仅匹配成功才 consume。 | — |
| [OSFlagCreate](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:226) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` | Flag：ISR/depletion；临界区 pop 独立 group free list 并初始化 type/flags/empty wait/name，按实际 safety guard 返回。 | — |
| [OSFlagDel](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:318) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` ∧ `OS_FLAG_DEL_EN > 0u` | Flag/Task/Sched：NULL、ISR、type 顺序，再 NO_PEND/ALWAYS/invalid；ALWAYS abort+unlink 全部后将 WaitList 改作 free link。后续 Pend 再 unlink 的源码反例禁止宣称无条件保持。 | `OS_FlagTaskRdy`、`OS_Sched` |
| [OSFlagNameGet](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:449) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` ∧ `OS_FLAG_NAME_EN > 0u` | Flag/Bytes：NULL group/output/ISR，临界区检查 type 并读取 name/长度；名称借用和 u8 长度精确。 | `OS_StrLen` |
| [OSFlagNameSet](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:520) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` ∧ `OS_FLAG_NAME_EN > 0u` | Flag：NULL group/name/ISR，临界区 type/store；仅换指针，NUL 字符串存活期另证。 | — |
| [OSFlagPend](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:620) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` | Flag/Task/Sched：NULL/ISR/lock/type/mode；立即满足则 consume，否则在原栈建立节点并阻塞。timeout/abort 重置并 unlink，成功从 FlagsRdy 取值后延迟 consume；节点/组实例关系与 Delete 反例明确保留。 | `OS_FlagBlock`、`OS_Sched`、`OS_FlagUnlink` |
| [OSFlagPendGetFlagsRdy](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:820) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` | Flag/Task：临界区读取当前 TCB 上次就绪 flags mask，不是查询某个 group。 | — |
| [OSFlagPost](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:877) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` | Flag/Task/Sched：NULL/type 后 SET/CLR 修改，按链表次序测试节点，匹配则 wake/unlink，不在此 consume。条件调度后重新进临界区读 group flags 返回，不能绑定为最初修改值。 | `OS_FlagTaskRdy`、`OS_Sched` |
| [OSFlagQuery](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:1017) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` ∧ `OS_FLAG_QUERY_EN > 0u` | Flag：NULL/type 后临界区 snapshot flags；无 ISR 拒绝。 | — |
| [OS_FlagBlock](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:1090) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` | Flag/Task/Sched：初始化 caller 栈节点，头插 NULL 终止双链，写 TCB flag node/pend/delay 并清 ready；consume 留在 caller local。 | — |
| [OS_FlagInit](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:1142) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` | Flag：清 group 池，经 WaitList 建 free chain、初始化 name/root；不使用 Event 池。 | `OS_MemClr` |
| [OS_FlagTaskRdy](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:1209) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` | Flag/Task/Sched：`flag_task_rdy` 组合实际 node/TCB 选择和精确 BOOLEAN；有效登记推出 lookup/unlink 存在及物理 TCB 地址对应。dly=0、写 FlagsRdy/pend result，仅清 FLAG bit；整个 Stat=RDY 才执行 ready 写入，false 仍更新/摘链，true 不等于首次进入 ready。已连接普通全局有效性和删除准备阶段的保持证明；当前 FlagNode 清理使用 TaskDelete-enabled profile，不代表其他宏组合或调用循环已验证。 | `OS_FlagUnlink` |
| [OS_FlagUnlink](/tmp/ucos2-official-audit-20260802/Source/os_flag.c:1256) | `(OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)` | Flag/Task：读旧 Prev/Next，更新前驱或 group head、后继 Prev，条件清 TCBFlagNode；不清自身 Next/Prev，要求真实 linked-stage，不是幂等删除。 | — |

## os_mem.c（7 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSMemCreate](/tmp/ucos2-official-audit-20260802/Source/os_mem.c:70) | `(OS_MEM_EN > 0u) && (OS_MAX_MEM_PART > 0u)` | Memory/Bytes：NULL/base alignment/nblks>=2/blksize>=pointer 检查；临界区摘 MCB，外部对 caller buffer 建首字链及 private 字段。没有 stride/product-capacity/ISR 检查，保留 Init 的 name。 | — |
| [OSMemGet](/tmp/ucos2-official-audit-20260802/Source/os_mem.c:171) | `(OS_MEM_EN > 0u) && (OS_MAX_MEM_PART > 0u)` | Memory/Bytes：NULL partition 后临界区 NFree>0 则摘头/减数，将全块与 loan 转交；否则 NULL/no-free。首字旧 link 和 payload 不清。 | — |
| [OSMemNameGet](/tmp/ucos2-official-audit-20260802/Source/os_mem.c:235) | `(OS_MEM_EN > 0u) && (OS_MAX_MEM_PART > 0u)` ∧ `OS_MEM_NAME_EN > 0u` | Memory/Bytes：NULL partition/output/ISR 后临界区读取 name 和 NUL 长度；本结构没有 type tag。 | `OS_StrLen` |
| [OSMemNameSet](/tmp/ucos2-official-audit-20260802/Source/os_mem.c:300) | `(OS_MEM_EN > 0u) && (OS_MAX_MEM_PART > 0u)` ∧ `OS_MEM_NAME_EN > 0u` | Memory：NULL partition/name/ISR 后临界区换 name 指针，不复制字符串。 | — |
| [OSMemPut](/tmp/ucos2-official-audit-20260802/Source/os_mem.c:358) | `(OS_MEM_EN > 0u) && (OS_MAX_MEM_PART > 0u)` | Memory/Bytes：NULL partition/block、NFree>=NBlks 的真实检查；否则写 block 首字=旧头、push/count++。正确分区、唯一未归还 loan 和可写/对齐属于 caller 资源协议。 | — |
| [OSMemQuery](/tmp/ucos2-official-audit-20260802/Source/os_mem.c:411) | `(OS_MEM_EN > 0u) && (OS_MAX_MEM_PART > 0u)` ∧ `OS_MEM_QUERY_EN > 0u` | Memory/Bytes：NULL partition/output；临界区复制五字段，Restore 后用已复制 NBlks-NFree 写 NUsed；不再读 live pool。 | — |
| [OS_MemInit](/tmp/ucos2-official-audit-20260802/Source/os_mem.c:456) | `(OS_MEM_EN > 0u) && (OS_MAX_MEM_PART > 0u)` | Memory：清 MCB 池，用 OSMemFreeList 字段建链和 name/root；尚未取得任意 caller block region。 | `OS_MemClr` |

## os_time.c（5 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSTimeDly](/tmp/ucos2-official-audit-20260802/Source/os_time.c:53) | 无外层 guard | Tick/Task/Sched：ISR/lock 或 ticks=0 不延迟；否则清 current ready、写 delay、Restore/调度，只有原 Task invocation 恢复才返回。 | `OS_Sched` |
| [OSTimeDlyHMSM](/tmp/ucos2-official-audit-20260802/Source/os_time.c:111) | `OS_TIME_DLY_HMSM_EN > 0u` | Tick/Task/Sched：ISR、lock、zero/minute/second/ms 顺序检查；按源码 u32 和嵌套 500/tick_hz 舍入式调用 Dly 后返回 NONE。当前1ms可取整为0，不强制阻塞。 | `OSTimeDly` |
| [OSTimeDlyResume](/tmp/ucos2-official-audit-20260802/Source/os_time.c:175) | `OS_TIME_DLY_RESUME_EN > 0u` | Tick/Task/Sched/Event/Flag：priority/live lookup；delay>0 时置0，pending 转 timeout 或普通 delay 转 OK，尊重 suspension，保留 Event/Flag 链待清理并按源码调度；否则 TIME_NOT_DLY。 | `OS_Sched` |
| [OSTimeGet](/tmp/ucos2-official-audit-20260802/Source/os_time.c:237) | `OS_TIME_GET_SET_EN > 0u` | Tick：临界区读取 volatile OSTime，返回精确 u32 snapshot。 | — |
| [OSTimeSet](/tmp/ucos2-official-audit-20260802/Source/os_time.c:267) | `OS_TIME_GET_SET_EN > 0u` | Tick：临界区写 u32 OSTime，其他域包括 OSTmrTime/Task delay 保持。 | — |

## os_tmr.c（15 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSTmrCreate](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:121) | `OS_TMR_EN > 0u` | Timer/Intr/Sched：option/period/delay 在 ISR 前检查；scheduler-lock 下分配并初始化 stopped timer，callback/arg 可 NULL、name 有 fallback，精确 depletion/errors。 | `OSSchedLock`、`OSTmr_Alloc`、`OSSchedUnlock` |
| [OSTmrDel](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:225) | `OS_TMR_EN > 0u` | Timer/Intr/Sched：NULL/type 后 ISR；lock 下按 state：running unlink+free，stopped/completed free，unused/invalid 返回 FALSE/对应错误，字段按 Free 实际写集合。 | `OSSchedLock`、`OSTmr_Unlink`、`OSTmr_Free`、`OSSchedUnlock` |
| [OSTmrNameGet](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:320) | `OS_TMR_EN > 0u && OS_TMR_CFG_NAME_EN > 0u` | Timer/Bytes/Intr：先 output，再 timerNULL/type/ISR；lock 下按 state 读取 name/长度，精确 inactive/invalid-state，不复制名称。 | `OSSchedLock`、`OS_StrLen`、`OSSchedUnlock` |
| [OSTmrRemainGet](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:400) | `OS_TMR_EN > 0u` | Timer/Intr：running 返回 u32 Match-Time；stopped 用非零 Dly 否则 periodic Period，completed0；unused/invalid 有对应错误，与 OSTime 无自动联系。 | `OSSchedLock`、`OSSchedUnlock` |
| [OSTmrStateGet](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:501) | `OS_TMR_EN > 0u` | Timer/Intr：返回实际 state byte；UNUSED 的 perr 是 NONE，非法 state 仍返回该字节并写错误，保留 NULL/type/ISR 顺序。 | `OSSchedLock`、`OSSchedUnlock` |
| [OSTmrStart](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:570) | `OS_TMR_EN > 0u` | Timer/Intr/Sched：running 先 unlink 再 first-delay link 以 restart；stopped/completed link；unused/invalid 错误，Match 取模和 spoke 插入精确。 | `OSSchedLock`、`OSTmr_Unlink`、`OSTmr_Link`、`OSSchedUnlock` |
| [OSTmrStop](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:671) | `OS_TMR_EN > 0u` | Timer/Intr/Sched/Callback：running 先 unlink 再解释 opt/callback；invalid-opt 或无 callback 也可能 TRUE+error。stopped/completed TRUE+STOPPED，unused FALSE；回调可再次改变状态，不承诺最终必为 stopped。 | `OSSchedLock`、`OSTmr_Unlink`、`OSSchedUnlock`、`callback（间接）` |
| [OSTmrSignal](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:783) | `OS_TMR_EN > 0u` | Event/Timer/Task/Sched：原样返回 OSSemPost(signalSem) 结果；自身不写 Timer wheel/time。signal 频率来自真实 port/hook，core 不直接调用它。 | `OSSemPost` |
| [OSTmr_Alloc](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:807) | `OS_TMR_EN > 0u` | Timer：可用时 pop free，清 Next/Prev，Used++/Free--；其他 raw 字段保留至 Create 写入。NULL depletion 也保留。 | — |
| [OSTmr_Free](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:839) | `OS_TMR_EN > 0u` | Timer：写 UNUSED/optNONE/period0/match0/callback0/arg0/name?/Prev0，push Next 并改计数；Type/Dly 未写，不虚构清零。 | — |
| [OSTmr_Init](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:875) | `OS_TMR_EN > 0u` | Timer/Event/Task/Sched/Boot：清 Timer/wheel 池并建 type/free/count/time；创建 count1 与 count0 两个 Sem，再创建 Timer Task。OSTmrSem 并未用作 API 锁，忽略的失败需 boot 推导。 | `OS_MemClr`、`OSSemCreate`、`OSEventNameSet`、`OSTmr_InitTask` |
| [OSTmr_InitTask](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:936) | `OS_TMR_EN > 0u` | Timer/Task/Sched：通过真实 CreateExt/Create 建 current prio61、128-word 栈、TimerID 的任务，占总22 TCB之一；条件 NameSet，源码忽略返回。 | `OSTaskCreateExt`、`OSTaskCreate`、`OSTaskNameSet` |
| [OSTmr_Link](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:1004) | `OS_TMR_EN > 0u` | Timer：置 RUNNING，以 time+delay 或 period 作 u32 Match，再按配置 wheel size 取 spoke，头插并写 Prev/count；不是排序 delta 链。 | — |
| [OSTmr_Unlink](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:1054) | `OS_TMR_EN > 0u` | Timer：用 Match 求 spoke，区分头/内部节点摘双链，置 STOPPED/NextPrev0/count--；caller 必须持有实际 linked-node 权限。 | — |
| [OSTmr_Task](/tmp/ucos2-official-audit-20260802/Source/os_tmr.c:1100) | `OS_TMR_EN > 0u` | Timer/Event/Task/Sched/Callback：无限 loop：SemPend(signal,0) 后忽略 err，scheduler lock，time u32 加一，扫描一个 spoke；先缓存 next，再 unlink/relink或completed、回调、跟随缓存 next。需 cursor generation 保持或保留具体不安全轨迹。 | `OSSemPend`、`OSSchedLock`、`OSTmr_Unlink`、`OSTmr_Link`、`OSSchedUnlock`、`callback（间接）` |

## os_dbg_r.c（1 个定义）

| 函数与原始源行 | 外层配置 guards | 模型 owner 与必需语义 | 直接调用 |
|---|---|---|---|
| [OSDebugInit](/tmp/ucos2-official-audit-20260802/Source/os_dbg_r.c:255) | `OS_DEBUG_EN > 0u` | Config/Bytes：函数体仅对 exported const 地址作局部赋值；无内核状态写入。debug const 的布局/sizeof/endian/容量仍需配置化只读表示。 | — |

## 所选修复变体额外定义（不并入原版126）

| 函数 | owner | 必需关系 |
|---|---|---|
| `OSMutex_BasePrio` | Task/Mutex | 扫描实际 priority table，返回匹配 TCB 的最大索引；无匹配时返回源码 fallback。等同 permanent priority 必须由别名来源与存活定理推出。 |
| `OSMutex_EffectivePrio` | Task/Mutex | 返回匹配实际 table 的最小索引，否则 fallback；release 必须先只去掉当前锁的 alias，再运行扫描。 |

当前可验证提取位于 [OSMutex_Priority.c](../annotated_C/src/mutex/OSMutex_Priority.c)，已有 raw helper
规格位于 [mutex_priority_spec.v](../VC/code_proof/mutex/spec/mutex_priority_spec.v)。这些既有结果
不等于已经证明了全局 permanent/latched-demand 关系。

## 清单外的明确边界

CPU save/restore、平台栈初始化、Task/ISR/启动切换、App/CPU hooks、TLS 实现、Trace 展开和
应用 Timer callbacks 不是上述十一个源码单元的126个定义。设计必须绑定每个实际 callee 的资源、
状态作用及返回/终止；它们不因清单外就视为 no-op，也不宣称本轮证明了 ARM/BSP/应用程序。
默认字符串、OSUnMapTbl、debug constants 与系统静态栈属于资源清单，不能通过函数计数替代。
