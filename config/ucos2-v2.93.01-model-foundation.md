# uC/OS-II 全模块模型：分层、所有权与实施要求

内部函数实验的中文阶段成果、真实验收时间和可用于写作的摘要见
[阶段记录](../docs/case_briefs/internal_function_verification_progress.md)。

## 总体目标与当前实施边界

本轮以[完整验收目标](../../reports/kernel-model-20260927/acceptance-target.md)为准：
完成 V2.93.01 **当前选定配置**的全部启用模块、必要组合及真正受影响的历史证明，
并实际优化相关 skills。四个模型组合场景不要求顺带证明所有 C API；未启用宏组合、
ARM/BSP 实现和任意应用／ISR／回调不属于本轮完成条件，但其调用契约不能省略。
下述全函数族清单和早期记录继续作为覆盖导航，不能把其中的未来配置或完整系统执行
证明重新加入本轮，导致模型基线无止境扩建。也不能据此跳过选定范围内的已知共享缺口。

本文件保留全模块模型的实施要求。设计阶段已经完成；用户随后明确要求依据这三份文档完成
**模型实现、保持证明及受影响旧成果适配**，并授权自行进行有真实验证语义依据的必要改进。
设计完成不是当前目标完成；不能以工具改进或局部源码回归替代全库模型和证明交付。

用户随后明确：**本任务是直接的全库模型开发，不是完整的 C case 验证，不使用
controller.py 控制实施流程。** 在 main 的现有模型上保存原有改动、实现接口与引理，
用固定 Rocq 工具做受影响的必要检查；不为模型开发新建 annotation/VC 轮次、等待
controller acceptance 或重证不相关旧函数。历史 run/handoff/report 原样保留，不改写其结论。
以后真正验证 C case 时仍使用相应正式验证要求，这与本次模型开发的完成标准分开。

2026-09-12 用户调整实施次序：**相关依赖稳定一批，就迁移一批历史证明**，不再以全部
模块模型完成作为所有旧函数迁移的共同前置条件。首批审查 `OSSemAccept`，并按其暴露的
真实依赖排序：其锁外类型读取/句柄借还接口补齐期间，已有完整调用接口的 `OS_TCBInit`
先进入 C/VC 迁移；两者均使用当前完整 `UCOS2_inv`，不是用旧切片绕过缺口。创建/发布、阻塞恢复、
栈借还的已知缺口仍先在受影响函数的依赖中集中补齐。每批在当前源版本下收集全部独立
VC 的语义缺口，再统一修复 annotation；历史证据保留，不能继承为新版本 acceptance。
新增不变式的实际 writer 仍须补保持证明，未修改资源通过已证 frame 保留，不能退回旧切片
或弱化规格来避免迁移。全内核模型完善和受影响旧成果适配仍为总目标，下面历史实施记录中
“全部模型完成后再迁移”的排程由本条取代；不改变其既有检查范围或历史结论。

同日用户进一步授权 main 按实际变化选择历史 C annotation/VC 的迁移路线，不强制套用
新函数的完整 controller 阶段。仅类型/引用/证明脚本适配可直接迁移并检查当前完整 case；
真实模型/规格缺口仍批量修复，目标或生成输入变化仍做 canonical 生成。需要隔离授权、
多组证明或复杂合并时保留 controller。直接迁移不宣称 controller accepted/done，也不
改写冻结报告；存活 owner 先按既有 handoff 交接。实际产生的重复检查或流程缺陷据证据
修正 skills/tooling，不为本次排程另造流程或降低证明强度。

2026-09-10 用户曾明确实施次序：先完成全部 Coq 模型，再修复当前已有验证成果；
优先在现有 proof bodies、helper 和模型对应关系上迁移，不为这批适配强制重走特定流程。
模型完成之前不反复迁移同一批旧证明。最终仍须让实际证明符合最终模型和所验证的源码/规格，
不能靠跳过目标、弱化结论或旧成功记录代替检查；历史 acceptance 不自动成为新模型的结论。

2026-09-09 用户将范围明确扩展为：建立、完善 uC/OS-II 所有模块的 Coq 模型，
用于后续全部函数的验证；同时完成既有已证明函数在最终共享模型下的修复与适配。
不能把范围缩回 Mutex/Task/Queue，也不能以模型文件存在、单个 initializer 通过或
历史 slice 证明可编译代替全模块支持。后续全部 C 函数的完整证明是下一层工作，
最终实施必须提供其真实可用的模型接口和模型保持证明。

本文件规定模型工作的目标结构与实施要求，不表示这些模型已经实现或验收。
2026-09-09 根据本地 `LOS_Verify-capability` 的实际模型重新组织；借鉴其已经写出的
表示与证明接口，同时明确其占位定义、信任边界和与 uC/OS-II 的差异。不要求目录一一对应。
具体字段、资源谓词、关系与操作接口的设计见
[抽象 Coq 模型详细设计](ucos2-v2.93.01-model-design.md)，其状态与本范围文档分开说明。
逐函数的配置条件、模型归属、行为和调用见 [126 函数模型映射](ucos2-v2.93.01-model-api-map.md)。

以既有 V2.93.01 源码绑定、32 位 little-endian ABI 和已确认的实现修复为起点。
原始源码只读位置是 `/tmp/ucos2-official-audit-20260802/Source`；版本权威绑定仍在
[既有 profile](queue-v2.93.01-first-round/profile.json)，不为本设计另算摘要。
用户已经同意的 Task publication / Mutex nested-priority 实现变体保持显式区分，
不把原始实现、修复实现和历史 verification slice 混成同一声明。

当前 profile 不是“只有 Mutex/Sem/Queue”：`os_cfg.h` 已启用 Mbox、Flag、Memory、
软件 Timer、Task statistics；Flag 为 16 位，Memory partition 为 5 个，Timer 为
16 个、7 个 wheel spokes。它们不能作为未来可选功能而从当前完整全局不变式中省略。
EventMulti/EventName/TaskProfile/TLS/Trace/safety-critical 的当前关闭状态也不代表
相关源码函数可以从全函数族设计清单删除：按配置给出独立实例及依赖要求，不改写旧 profile，
不声称一个固定 64-byte TCB 表示支持所有宏组合。

CPU save/restore、context switch、BSP 继续使用已确认的外部平台契约；这不是新增 ARM
实现证明。只有已选择的两个 creation App hooks 可用其空实现，其他 hooks、Timer callback、
TLS/trace 等不能自动当作空调用。每个实际接口需要源码、调用约束和 frame 的对应关系。

## 从 LOS 模型采用什么

以下是已阅读的具体接口，不把“参考 LOS”留成遇到证明困难时才执行的泛泛建议。
路径指向同级本地参考仓库；声明名用于定位，不给参考工程增加本项目的 Coq import 依赖。

| LOS 的实际组织 | uC/OS-II 采用的原则与适配 |
|---|---|
| [Los_Verify_State_def.v](../../../LOS_Verify-capability/lib/Los_Verify_State_def.v)：模块 record、九个顶层 projection、`replace_tskS` 等更新 | 一个 canonical state，模块状态有明确归属；更新只替换目标部分并保留其他部分。uC 的 Sem/Mutex/Mbox 共用 `OS_EVENT`，不能机械复制 LOS 的九个 projection。 |
| [dll.v](../../../LOS_Verify-capability/lib/dll.v)：`store_map`、`store_map_missing_i`、`store_map_split/merge`，以及参数化 payload 的 `dllseg`、`dllseg_concat/split` | 复用“容器结构与节点 payload 分离、提取一个元素后保留其余资源”的方法。先用当前 QCP MapLib/ArrayLib 和本地已有引理；补真正可复用的链段接口，不复制 LOS 的结构名、16-byte 布局或公理。 |
| [task.v](../../../LOS_Verify-capability/lib/task.v)：`used_complete_task`、`store_used_task_map`、`task_inv`、`task_inv_missing_usedtask` | 按字段、对象、池、模块逐层聚焦；纯有效性与空间表示分别提供接口。`used_complete_task_merge_status` 是原 status 的重组，不是任意 status 更新的保持定理。 |
| [Los_Verify_inv.v](../../../LOS_Verify-capability/lib/Los_Verify_inv.v)：`LOS_Verify_inv`、`LOS_Verify_inv_missing_task/memory`、对应 `replace_*` 等价引理 | 全局组合保留未聚焦模块的真实分离合取；局部函数通过稳定的 open/merge 接口消费它。跨模块关系另证，不能仅凭分离合取就推出所有关系保持。 |
| [queue.v](../../../LOS_Verify-capability/lib/queue.v)：`valid_absqueue` 与 `semi_read/write_valid_absqueue*`；[swtmr_port.v](../../../LOS_Verify-capability/lib/swtmr_port.v)：state 与 sortlink 分层表示、missing-object 断言 | 为按源码顺序更新而暂时不满足稳定等式的状态提供精确阶段表示，不能强迫每条赋值后都恢复最终不变式。LOS 的双向读写等待/消息复制、sortlink 时间结构不照搬为 uC 的指针 FIFO/wheel。 |
| [sem_OsSemPost.v](../../../LOS_Verify-capability/VC/code_proof/sem/sem_OsSemPost.v)：`post`、`atomic_sem_post` 等函数语义位于模块 proof 目录；[sem_prog.v](../../../LOS_Verify-capability/lib/sem_prog.v)：操作族与初始程序集合 | 函数专有语义放模块 `spec/`，真正共享的状态变换与保持引理留模块库；操作族组合按需要建 `*_prog.v`，不为每个函数再造一个库层。 |
| [membox_lib.v](../../../LOS_Verify-capability/lib/membox_lib.v)：free/allocated 链与控制块；[memory_def.v](../../../LOS_Verify-capability/lib/memory_def.v)：动态池节点/大小/空闲索引 | uC 固定分区应借鉴前者的块分区与归还接口，而不是后者的动态堆算法；块的用户数据、空闲链头字和控制块需按 uC 源码重新划分所有权。 |

参考项目的边界也必须保留：`Los_Verify_inv.v` 中五个模块不变式仍声明为 `Parameter`，
`task.v` 的 `store_stack_memory` 为 `Admitted`；`dll.v` 含布局/未初始化存储公理。
[Los_Rules_lib.v](../../../LOS_Verify-capability/lib/Los_Rules_lib.v) 的 C transition
只固定 stable globals，抽象 transition 为 `1 = 1`。
这些能帮助理解接口，但不能证明真实环境只执行已验证的内核操作。
此外，`sem_prog.v` 导入了函数级文件，`queue.v` 也混有函数语义；本项目不把这种历史依赖
混合当成目标结构。参考代码中有 `Qed` 也不自动意味着其传递依赖没有假设。

## 模型的目标组织

### 层次与文件职责

保持现有可复用 owner，按真实依赖整理，不进行全库机械改名或“一模块固定拆四文件”。
下表列出模型 owner 与候选接口；当前用户已授权按真实语义需要直接实施及调整消费者。

| 层次 | owner / 位置 | 应包含的内容 |
|---|---|---|
| 配置、类型与更新 | `lib/stable_glob_vars.v`、`lib/ucos2_verify_state_def.v`、`lib/error_codes.v` | ABI、宏组合、地址/容量、模块 record、必要生命周期/ghost 类型、projection/replace 和结构等式。稳定的是地址与配置，不是这些地址中存放的可变值。 |
| 逻辑与结构基础 | `lib/ucos2_rules_lib.v`、既有 MapLib/ArrayLib；本地 `helpers.v` 及按需提取的结构引理 | CSL/STS 实例、整数/位图、有限 map、数组、链段的共用接口。纯容器规则不依赖函数规约或全局不变式。 |
| 模块表示与语义 | 见下一表中的既有或新增模块库 | 具体字段/字节、对象与池、模块有效性、局部状态变换、source-ordered 阶段、split/merge 与保持引理。函数入口专有约束不混入每个模块的公共不变式。 |
| 跨模块组合 | `lib/cross_module_invariants.v`、`lib/ucos2_verify_inv.v` | Task/Sched/IPC/Timer 等纯关系、完整资源组合、聚焦与更新后重组、初始化建立以及环境操作的保持证据。跨模块操作可在此层组合局部变换，不要求底层互相导入。 |
| 操作族与客户端协议 | 既有 `lib/atomic_ops_lib.v`、`lib/mutex_func_sem.v` 中真正共享的部分；仅必要时增加模块 `*_prog.v` | 原子动作组合、外部调用后恢复、阻塞 invocation、操作族证书。明确只刻画某个函数的定义下移到该函数规约；通用性质不因暂时只有一个消费者而机械搬动。 |
| 函数规约与 VC | `VC/code_proof/<module>/spec/<function>_spec.v`、该 case 的 `case_lib` 和生成/证明文件 | public Pre/Post、返回/错误码、输出参数、callee 契约绑定和函数特有中间语义；case helper 与 canonical VC/manual 各守原职责。 |

目标依赖方向是：配置/状态和逻辑基础 → 模块表示/局部变换 → 跨模块组合 → 操作族/函数规约 → VC。
这是整理后的方向，不是对当前完整 import 图的描述：当前 `array_abstraction.v` 仍包含依赖
Task/Event/Sched 的专用数组接口，不能直接当成底层纯库。`ucos2_verify_inv.v` 对
`mutex_accept_spec.v` 的反向导入已经删除，19 个 MutexAccept 专用 helpers 已随规约迁入
`VC/code_proof/mutex/spec/mutex_accept_spec.v`，旧 `lib` 路径仅重导出。需要的公共性质下沉到实际模块，
函数专有部分随受影响函数迁移，不让全局不变式反向依赖某个公有 API 的 spec。

既有 `lib/*_spec.v` 按消费者逐项迁到模块 `spec/`，不为目录整齐机械搬动。迁移保持 theorem
statement、实现/profile 绑定与公开规格；必要时保留临时兼容导出，先核对 annotation、callee、
生成 imports 和 controller 依赖。模块库不能再反向导入这些兼容入口来形成隐含耦合。
已经落在模块 `spec/` 的 MutexPriority、QCreate、TCBInit 可沿用，不另建同义接口。
新增声明沿用 [AGENTS.md 的命名规则](../../AGENTS.md)：对象与性质明确、同族可检索；
不复制 LOS 的历史拼写错误或 `cond1` 式泛名，也不把字段等式命名成正确性/保持定理。

record 按实际对象、配置实例、资源和生命周期组织，不因历史补字段而新建包装。
字段袋的清理同步移除其专用 updater/helper，不保留类型或投影 alias；独立的配置、raw image、
private allocation 与 lifecycle 不属于此类冗余，保留其语义边界。具体字段组织见详细设计第2节。
全模型接口使用按语义整理后的名称；当前 `UCOS2_inv` 与历史 `UCOS2_verification_slice_inv`
分开，前者的资源/有效性分层为 `UCOS2_raw_rep` / `UCOS2_state_inv`，不通过 profile
dispatcher 在两个强度不同的入口间切换。旧切片不因重命名获得当前所有模块的资源或保持证明。

冗余清理以实际语义和消费者为依据。旧 `OSEventAbstractState.flagFields`/`FlagFields.flag_dummy`
已删除：它被有效性恒约束为 `None`，实际 Flag 使用独立 `OS_FLAG_GRP` 与栈节点，不属于
`OS_EVENT` payload。该删除不去掉 Flag 资源义务；它们由新的 `FlagState`/`flag.v` 承担。
通用排序的按成员 key 一致性及 OR-fold 的置换/去重保持已放入 `helpers.v`；
`event_wait.v` 不再为一个排序引理依赖 `sched.v`。Task 的 live 字段修改共用池/链/代际/
优先级结构保持定理，真正改变 ready、等待登记或 native bytes 的部分仍分别证明。
仍有消费者的历史验证切片接口先隔离或迁移，不把旧切片的成功结论追溯宣称为新模型的证明。

### 全局状态与资源唯一归属

设计输入中的 `UCOS2_Verify_State` 只有 Intr/Task/Sched/Event/Tick 五个 projection。
直接模型开发现已增加 Flag/Memory/Timer/Statistics/Control/Name 六个 owner，补入配置与
全局地址，并建立各 projection 的 put-back、last-write、frame 和两两交换接口。
扩展按独立资源决定，不是按 C 文件数量决定；多个模块可以只读同一个抽象状态，
但同一内存单元只由一个表示拥有。状态更新代数通过不等于所有跨模块操作已经保持不变式。

| 状态或资源族 | 空间 owner 与扩展要求 |
|---|---|
| Intr | `interrupt.v`：中断/调度锁 nesting 等既有字段。IRQ masking 与 scheduler lock 分别建模；后者不自动禁止 ISR。 |
| Task | `task.v`：TCB 字段、优先级表、TCB 池与链、task count、generation/invocation、创建/回收资源；栈所有权接口也在此归属，平台契约消费的是被交出的部分。 |
| Sched | `sched.v`：ready bitmap、当前/最高 ready 缓存、running/context-switch 字段。Task 的优先级表不在这里重复存储；两者由纯一致性联系。 |
| Event / Queue | `event_pool.v` 拥有共享 ECB 布局/池/分配身份接口，`event.v` 解释 Mutex/Sem/Mbox/Queue payload 并组合生命周期；两文件共用同一个 Event 子状态。`mutex.v`、`mbox.v`、`event_wait.v` 提供相关语义。`queue_core.v` 拥有 QCB/ring 表示及存储转移接口；继续复用 Event 中的 Queue 状态/bytes 归属，补 QCB private/free/published 阶段，不另存一份 FIFO 或另一份 Event 池。 |
| Tick / Time | `tick.v`：内核 tick 与 tick-step 状态；delay 作用于 Task/Sched。软件 Timer 的计时域独立，通过真实 tick-to-signal 关系连接。 |
| Flag（新增） | `lib/flag.v` 与真实 Flag 子状态：组池/free list、flag bits、等待链及节点登记。栈上 `OS_FLAG_NODE` 发布时把所需字段资源借给 Flag 表示，解绑/任务终止时按协议归还或回收；Task 不再重复拥有这些已借出的栈字节。 |
| Memory（新增） | `lib/memory.v` 与 Memory 子状态：`OS_MEM` 控制块池、各固定分区、free/allocated 逻辑分区。空闲块由池拥有，分配块的数据权限交给调用者；全局模型保留分配记录，不把用户持有的数据再次放进 global `**`。 |
| Timer（新增） | `lib/timer.v` 与 Timer 子状态：`OS_TMR` 池、wheel、时间/数量/状态与 callback 阶段。初始化创建的 `OSTmrSem` 和 `OSTmrSemSignal` 两个 Sem 仍由 Event 拥有、系统任务仍由 Task 拥有；Timer 只持标识和关系。本版 API 实际用 scheduler lock，不能把未用于加锁的 `OSTmrSem` 当成锁证据。 |
| Statistics（新增） | `lib/statistics.v` 与统计子状态：`OSIdleCtr/Max/Run`、`OSCPUUsage`、`OSStatRdy` 等值及采样阶段。统计任务仍属于 Task，栈扫描通过 Task 栈接口取得权限，不再拥有一套栈。 |
| 跨模块公共资源（设计增补） | `lib/kernel_resources.v` 候选：实际条件控制 cell、共享名称字节及其来源/读取存活期、公共只读表接口；不是新的 IPC 模块。Name 指针仍属于各对象，字符串不能按每个引用重复占有。该 owner 是详细设计新增候选，不追溯修改已冻结 intake 的写路径。 |

Mbox/Sem 不为目录对称额外建立顶层 projection；uC 无 capability 模块，也不引入 LOS 的权限
对象模型。名称、TLS、Task profile、trace、debug、safety-critical 等依实际配置附着到其真实
owner；共享 init/辅助函数也不各自成为一个独立的“Core heap”。

### 通用结构如何复用

- map 的有限域、`NoDup`、单元素提取/重组、未选元素在更新下的等价优先用现有 QCP 接口。
  一个 `store_map_split` 只解决空间拆分，不自动建立 used/free/private 的穷尽与互斥。
- `field_storage.v` 仅把配置字段清单适配为 QCP `store_map`；split/merge/missing 复用 MapLib，
  单元蕴含的提升复用 QCP `proper_iter_sepcon_impp`。nil/cons 只组合这些已有引理，不再
  自行递归实现分离合取算法。Task/Event/Queue/Memory 各自提供真实字段、地址、类型与 image。
- 数组保留整体 list、单元与 missing-index、`replace_Znth` 更新、长度/边界/stride 接口；
  `queue_core.v` 的全部槽位字节与逻辑 FIFO 分开，Flush/出队不能把未写的旧字节虚构为清零。
- 链段抽象参数化 payload 和真实 next/prev 字段地址，提供 concat/split、提取/插入/删除及
  更新后的重组。TCB active list、TCB/free-block 单链、Flag 双链、Timer spoke 的端点条件
  分别实例化；不把 NULL 终止链强行当作 LOS 的带哨兵循环双链。
- 确认有跨函数/模块的结构复用需求时再抽到公共文件，`dll.v` 可以是这种抽取的结果，
  不是预先整份复制 LOS 代码的要求。节点字段归属与布局证明留在本内核，避免导入 LOS 公理。

## 全局不变式与可扩充接口

### 组合的是全部资源，不是全部断言文本

沿用 `UCOS2_state_inv` / `UCOS2_raw_rep` 的现有分层，把新增模块纳入。
目标结构示意如下，名称表示职责而非已落盘的 Coq 声明：

```text
kernel_inv = pure(config_valid /\ module_validity /\ cross_module_consistency)
             && (intr_rep ** task_rep ** sched_rep ** event_rep ** queue_rep
                 ** tick_rep ** flag_rep ** memory_rep ** timer_rep ** statistics_rep
                 ** kernel_resources_rep)
```

这里各 `rep` 的实际参数包括它所读取的必要状态；不能为了排成独立列表而删掉依赖。
全局不变式覆盖当前配置所有启用模块的共享资源和必要关系，但不无条件占有应用正在使用的
内存/栈，也不要求“某函数返回错误”这类局部性质永远成立。对关闭模块，只有配置与布局证明
确认对象不存在、不可访问时才用空资源实例；当前已启用的模块不能用 `True`/`emp` 代替。

纯跨模块关系至少按以下同族接口组织，避免每个函数各写一套：Task↔ready/当前缓存，
Task↔Event waiter 与 pend-result，Mutex↔base/effective priority/PCP alias，Event↔QCB 与
published bytes，Task↔Flag node/timeout/恢复，Timer↔Sem/system task/tick，统计↔采样阶段。
关系是双向成员对应还是仅单向约束，必须根据源码说明；不能只证明“链上节点能找到 Task”
却遗漏“所有正在该对象上阻塞的 Task 均有唯一登记”。

### 局部化、更新和扩展

1. projection/replace 提供 target-get、非目标字段保持、put-back、一般 last-write-wins，
   按实际使用补不同 projection 的 commutation。LOS 的 `dup_replace_*` 仅证明同值重复写，
   不能当作这组接口已经齐全；所有旧 record 构造/更新必须保留新增字段。
2. 模块表示提供“字段 → 完整对象 → map/pool → 模块”的 split/merge；全局层提供
   `..._missing_<module>` 或现有 `..._residual`。原值重组与更新重组分开：后者显式要求
   更新后局部有效性、cross 关系和 residual 可转移性，不能靠旧值 magic wand 接回新值。
3. 未写其他模块内存，不等于 residual 自动不变。例如当前
   `UCOS2_task_sched_residual` 的 Event 表示仍读取 Task 状态。Task 更新必须证明
   这些依赖字段不变，或证明该 residual 的更新等价/蕴含；只证明 `EventState` 不变不够。
   若操作确实同时改了 waiter、位图或定时关系，聚焦该组模块共同重组。
4. 增补模块内部纯性质时，首先修改该模块的有效性与 init/保持证明；其他函数优先依赖其
   稳定接口，不展开全部 record。增补跨模块关系时，定位所有写相关字段的操作族并补保持性；
   不相关函数使用已证明的 frame 接口。新增模块时同时补 state/config、真实 rep、全局组合、
   init 和环境操作实例，不以未约束的 `OtherInv` 插槽宣布扩展完成。
5. 泛化接口可带显式假设，但每个配置/模块实例必须提供证明，最终具体模型不能留下新增
   `Parameter`/`Admitted`/公理。结构可扩充不等于任意更强不变式都保持，也不保证以后零适配；
   目标是把必需适配收敛在 owning module 与受影响操作族，而非反复改所有函数断言。

### 初始化、中间阶段与并发边界

- 从启动内存到 OSInit 各子初始化再到 OSStart 分阶段建立运行态 invariant；证明合法配置
  的初始实例确实存在。运行前未初始化资源用 boot 表示描述，不假设完整运行态 invariant
  在 OSInit 第一行已经成立，也不用不可满足的不变式“证明”初始化。
- 私有分配、priority reservation、publication、逐个 wake/unlink、delete/retire、callback
  等按源码建立阶段关系。只在需要的阶段要求相应一致性：临界区内部允许合法的暂态；
  Restore、scheduler unlock、阻塞切换和回调这些可观察边界必须关闭正确的全局资源。
  某阶段若会跨边界暴露，必须进入真实共享状态/环境协议，不能仅藏在局部 annotation 中。
- 原 invocation、Task/object generation 与借出的存储必须跟踪到恢复或终止，防止删除/重用
  后按旧指针重新折回对象。Flag stack node、QCreate 私有 QCB、Memory 已分配块、Timer
  callback 各有自己的生命周期，不能都套创建阶段的单一 certificate。
- `KernelClientCertificate` 是“某已定义动作保持有效性与资源”的待证接口；逐个加入实际
  Task/IPC/Tick/Timer/ISR 客户端并证明实例和轨迹组合。目前 creation family 的证明不是
  全内核环境的证明。底层宽松 STS transition 不提供这些更强结论，Restore 后也不能直接
  假设所有所需关系保持。平台外部契约与内核客户端保持证明分开登记。
- QCP 对布局宏、指针运算、volatile、间接 callback、平台汇编的实际支持按具体 translation
  unit 检查。工具表达缺口与模型缺口分开；改用外部契约时列明其作用、资源和未证明实现，
  不静默跳过指令或把本应验证的内部 API 当作无效果调用。

## 源码到模型的全范围清单

下表是未预处理 `Source/os_*.c` 的函数定义清点：共 126 个定义，**不是 VC 数量，也不是
126 个已验证函数**。计入 internal/static helpers 和条件编译定义，排除了前置声明；
`ucos_ii.c` 是十个实现单元的聚合入口，不另计函数。后续按每个绑定配置检查实际编译覆盖。

| 源码单元 | 定义数 | 现有基础与本轮必须闭合的内容 |
|---|---:|---|
| `os_core.c` | 35 | Init/Start、IRQ/锁/调度、Event helpers、Tick、idle/statistics、TCBInit、mem/string helpers；启动阶段、全部已启用模块建立、统计全局变量、栈与回调/平台边界仍须共同覆盖。 |
| `os_task.c` | 16 | TCB64、generation/invocation、创建私有资源可复用；补 ChangePrio 当前缓存、删除中间阶段、Suspend/Resume、栈扫描、Reg allocation、名称与 Query 的完整读写/生命周期。 |
| `os_mutex.c` | 7 | 保留已修复变体与官方持锁协议；全族 permanent slot / enabled PCP aliases、masked Pend demand、逐步 release/handover、优先级恢复及 suspension 保持。 |
| `os_sem.c` | 8 | 计数和 Event/task wait 基础可复用；全部操作迁移至最终 native/global 接口，不能继续用历史 slice acceptance 代替。 |
| `os_q.c` | 11 | QCB、FIFO、publishedQueueBytes 可复用；私有创建/回滚/发布、精确 ring 更新、阻塞恢复、广播/abort/delete、调用者 buffer ownership。 |
| `os_mbox.c` | 8 | `mbox.v` 已有 NULL 规范化、初始 payload、取消息、无等待者的存消息、完整 native Event 有效性保持及消息指针单元拆合；继续补 private ECB 生命周期、阻塞恢复、direct handoff/broadcast/abort/delete 与 Query 输出。局部操作不等于八个 C 函数已完成验证。 |
| `os_flag.c` | 13 | `OS_FLAG_GRP` 与 `OS_FLAG_NODE` 是独立结构；已移除旧 `FlagFields.flag_dummy`。组池、等待节点双链、mask/mode/consume 的局部模型已建立，继续接入栈节点生命周期及 Task/Sched 双向关系。 |
| `os_mem.c` | 7 | 已建立独立 partition/block、控制块池和 free/allocated 分区；Get/Put 以线性块 loan 转移所有权，继续完成 Create/Get/Put/Name/Query/Init 的组合行为。不采用 LOS 动态堆合并算法。 |
| `os_time.c` | 5 | Tick 状态可复用；补 Dly/DlyHMSM/DlyResume/Get/Set 的整数舍入/溢出、Task/ready 更新和外部恢复。 |
| `os_tmr.c` | 15 | 已建立 pool、free list、wheel spokes、mode/state/match/time 及局部 source-ordered 更新；继续完成信号 Sem、timer task、callback 与 link/unlink/restart/delete 的全状态保持。源码使用 Sem，不照搬 LOS 的 handler Queue。 |
| `os_dbg_r.c` | 1 | `OSDebugInit` 和只读调试常量/布局导出，明确实际编译条件与 observation；不能因不是 IPC 而漏掉。 |

### 不得遗漏的内部与条件函数

Core：`OSEventNameGet/Set`、`OSEventPendMulti`、`OSInit`、`OSIntEnter/Exit`、
`OSSafetyCriticalStart`、`OSSchedLock/Unlock`、`OSStart`、`OSStatInit`、`OSTimeTick`、
`OSVersion`、`OS_Dummy`、`OS_EventTaskRdy/Wait/WaitMulti/Remove/RemoveMulti`、
`OS_EventWaitListInit`、`OS_InitEventList/Misc/RdyList/TaskIdle/TaskStat/TCBList`、
`OS_MemClr/Copy`、`OS_Sched/SchedNew`、`OS_StrLen`、`OS_TaskIdle/Stat/StatStkChk`、`OS_TCBInit`。

Task：`OSTaskChangePrio/Create/CreateExt/Del/DelReq/NameGet/NameSet/Resume/StkChk/Suspend/Query`、
`OSTaskRegGet/RegGetID/RegSet`、`OS_TaskReturn/StkClr`。

Flag：`OSFlagAccept/Create/Del/NameGet/NameSet/Pend/PendGetFlagsRdy/Post/Query`、
`OS_FlagBlock/Init/TaskRdy/Unlink`。Memory：`OSMemCreate/Get/NameGet/NameSet/Put/Query`、`OS_MemInit`。

Timer：`OSTmrCreate/Del/NameGet/RemainGet/StateGet/Start/Stop/Signal`、
`OSTmr_Alloc/Free/Init/InitTask/Link/Unlink/Task`。
修复变体新增的 Mutex 优先级 helper 另按其实际 source-bound translation unit 计入，不冒充原始源码定义。

## 实施批次与模型可用条件

### 先稳定共同接口，再按依赖实施

1. 全函数族 intake 一次列清配置、源字段/资源 owner、读写集合、退出与并发边界、阶段和
   工具限制。用上面的结构先验证这些行为能否表达；九类已收集 Mutex/Task/Queue 原因复用
   为导航，不重复没有变化的审查。新问题按源代码缺陷、模型阶段、annotation 传播、工具或
   L7 证明接口区分，不能把所有失败都解释成“再加一个前提”。
2. 同一设计批次确定 state/config、公共结构、必要 ghost 与全局组合接口，以及精确的既有
   owner、新文件和消费者，按用户授权直接开发。保留已有 dirty baseline 和历史成果；
   不修改冻结 handoff，不把新库开发伪报成旧 run 已验收的产物。
3. 实施依赖顺序：共同基础与 Task/Scheduler → Event/Mutex/Sem/Queue/Mbox 与 Flag/Memory
   各自的真实依赖 → Tick/Time、Timer 与 Statistics → boot/runtime 全局组合和完整客户端
   操作族。Memory 的独立结构不必等待某个 Mutex VC；Timer 的 Sem/Task 依赖则必须真实接上。
4. 用有代表性的接口使用检查设计：创建的 private→publish/rollback、Task priority/delete
   阶段、Mutex handover、Queue ring/直接唤醒、Flag unlink/timeout、Memory Get/Put、Timer
   callback/restart 和统计采样。可以先完成这些模型引理与受影响的小范围 VC，不等 126 个
   C 定义全部证明才确认接口；但一个 initializer 的成功不代表整族可验证。
5. 公共接口及组合稳定后，按实际依赖迁移既有函数的 spec/import/proof；保留旧版本报告，
   TCBInit 也纳入影响分析。未变化且无依赖风险的旧证明不重编译，受影响证明必须在新版本
   验收后才可称适配完成。不为排版/改名重新建立证明流水线。

### 每个模块应交付什么

交付实际定义、被证明的接口及必要检查结果，不另造模型开发审批或验收表格：

- 源码字段到抽象字段/资源的对应关系、合法配置与布局；地址不同不足以证明整个区域不重叠，
  还需池大小、stride、对齐、机器整数边界和 caller-supplied 区域的分离约束。
- 具体 rep、used/free/private/retired 等适用分区的穷尽互斥、初始实例与 init 建立、模块及
  cross 有效性；预处理配置改变布局时用独立实例，不修改旧 ABI 声明。
- 实际需要的字段/对象/池 split、原值 merge、updated-merge、状态更新等式及操作族保持；
  性质按源码赋值顺序闭合，所有返回、错误、输出及公开使用协议可由函数 spec 精确表达。
- 阻塞/唤醒/中断/callback 的恢复接口与环境动作证书；内核与用户资源转移、失效指针和
  generation 不被遗忘。某项无法闭合时保留具体路径/反例，不声称模型完整。

“模型可用”表示该模块整族行为有对应表示和可消费的接口，关键建立/保持/重组已证明；
“全模块模型完成”还要求全部启用模块组合及其关键建立、保持与资源重组闭合；
“本轮整体任务完成”还要求修复、迁移真正受影响的既有函数证明，不能将两阶段混称；
“所有函数验证完成”另要求每个 C case 按其实际路线完成当前源码、规约与全部目标的
必要检查。controller run 须为当前 `done`；直接迁移不得冒称 controller `done`。
完整性是相对源码版本、配置、公开协议和工具/平台信任边界而言，不是模型绝不再需扩展的保证。
当前配置完成与其他宏组合完成分别说明；未启用条件函数仍保留在全函数族设计清单，
未来启用时须补配置及必要模型，不能称为已经支持；它们不是本轮基线完成的附加门槛。

### VC 缺口仍然批量反馈

同一 `source_goal_version` 先完成全部 target/shape 分诊；proving 遇到首个语义缺口后，
继续其余独立目标和 dependency-ready groups，只暂停真实依赖该缺口的后继。
全部独立组 accepted 或形成 terminal blocker 后，按 earliest loss point / owning layer /
missing atom 合并 affected witnesses，一批 annotation 修复，尽量一次 canonical symexec。
源码审查提前减少已知的 L0–L6 缺口，但不能保证修改后不产生新形状或未知缺口；这不授权
把未经证明的所有目标标成通过，也不阻止因整个 source/target set 失效而立即停止。

## 实施起点与已有证据（2026-09-09 快照）

本节记录已有输入；当前模型开发进度以实际源文件和针对性 Rocq 结果为准，历史 case
状态仍由原 controller 报告决定。修改本设计不改变这些报告或冻结输入。
下述可复用模型接口以当前名称呈现；各日期下的通过、失败和未完成记录仍只属于当时版本，
不作为 2026-09-12 字段平铺与接口整理批次的通过证据，历史报告和绑定内容不改写。

- `sem_query-20260909110506`：16 个 manual targets，parent/final 已通过，controller `done`；
  另有 32 个 canonical auto/tool-trust obligations，不宣称这些也已 kernel-Qed。
  与 SemAccept/SemSet/SemPost/QCreate 一样，这是中间共享版本的结果，不是最终全模块证据。
- `mutex_priority-20260909114354`：25 个 manual targets，groups/parent/final 已通过且已 apply，
  controller `done`；另有 26 个 canonical auto/tool-trust obligations。其真实 native callee
  规约现可作为精确绑定的依赖，不代表公有 Mutex 函数/全局 alias 关系也已闭合。
- `del_full-20260909131500` r1：源码只读审查汇总九类缺口、十个 owner 请求、十八个只读依赖。
  controller 记录为 blocked，且报告还存在 OS routing/precheck 字段不满足的问题；
  不把此报告称为 acceptance，也不据此伪造可写授权。其精确源码诊断仍可作为后续审查导航。
- 当前实现了 controller 对模块目录 `spec/*_spec.v` 的精确共享依赖路径支持；27 项相关测试
  通过，保留 readonly/write、版本、symlink、case-owned、generated/manual 和 final-apply 边界。
  该工具改动本身不改变任何历史证明的验收。
- 全模块正式模型实现与最终旧函数迁移均未完成。本文件是当前任务/源码范围输入，
  不是 formal artifact、验收清单替身或新公理授权。

此前 `del_full-20260909141749` 的 r1/r2 已完成源码分析和实施范围梳理，R3 建立后、尚未
修改任何正式文件时，用户将当前任务明确为不经 controller 的直接模型开发；现在已切换。
新增共享 owner 为 `lib/flag.v`、`lib/memory.v`、`lib/timer.v`、`lib/statistics.v` 及
公共资源 `lib/kernel_resources.v`，实现进行中。此前完成的 controller 新文件支持与
源码审查复用改进保留，完整测试 329 项通过，但它们不再控制本次模型开发。
独立 [Flag abort cleanup 修复变体](../source_variants/flag-abort-cleanup/README.md) 的
原版/修复版共 8 个源码场景检查通过；其形式化模型与调用链保持证明仍待完成。
独立 [Statistics sampling 修复变体](../source_variants/statistics-sampling/README.md) 的
原版/修复版共 14 个场景检查通过，实际复现原版除零和百分比超界；修复版检查零除数并
在缩窄前比较完整比值。这是源码回归，不是统计任务或平台的形式化证明。

直接模型开发的近期进展：

- `tcb64_configuration` 明确限定实际宏布局，含 Reg=1、TLS=0、Flag16 及 Flag 容量为正等条件；不把
  该 64 字节表示当作全部合法配置的通用实例。
- Task 已拥有真实 `OSTaskRegNextAvailID` 动态值，构造和更新保留它；分配核心的
  成功/耗尽、范围、连续分配不重用以及 allocator 单元拆分/更新重组引理已编译。
  NULL `perr` 与 safety callback 仍属于函数入口契约，不能由该核心定理替代。
- Native scheduler 不再永久要求当前优先级缓存等于 TCB 的最新字段；已证明
  ChangePrio 待调度阶段的缓存陈旧性和显式 context-switch 契约下的重新同步。
  当前/最高指针与优先级仍有范围约束，调用边界另需 live/ready 证据。
- 全局 raw representation 已组合六个新增 owner，正在完成依赖检查与跨模块关系；
  尚未宣称全内核不变式或全部操作族保持性已经完成。
- Task 的 `task_linked_wait_phase` 现为 Event 与 Flag 共用；Tick 不再为这个 Task 状态
  定义反向依赖 Event。`task_flag_waiter_consistency` 已建立节点/TCB 指针的双向关系和
  代际绑定，并证明 Tick 超时与 Task 发布保持。Flag owning validity 排除 NULL 链节点。
- Flag/Memory/Timer 的全局 focus 与 updated merge 已编译；Memory Get/Put 的全局纯
  保持定理只消费前态有效性、实际变换结果与 Put 所需的线性分配记录，不假设后态有效。
- TCBInit 规约已适配 allocator 残余资源和发布时的 NULL Flag 节点条件，并删除 13 个
  无需使用的 Mutex/Sem/旧操作库导入；精简后的完整规约文件检查通过。此处是当前共享
  模型下的规约库适配，不等同于重新取得历史 C case 的 controller acceptance。
- `task_boot` 已提供空闲 TCB 存储/链、空优先级表、零寄存器计数和未发布 Task
  生命周期的有效实例；初始 image 区分 `Next`、默认 `"?"` Name 与其余零化字段。
  Task 全文件检查通过。这是 `OS_InitMisc`/`OS_InitTCBList` 的模型组件，不是 `OSInit`
  的完整 C 正确性证明。
- Timer 已区分 BSS 未初始化、建池、两次 Sem 创建返回与 Task 创建返回阶段，正式模型
  检查通过；`Finished` 只表示调用已结束，不假设两次 Sem/Task 创建都成功。
  enabled-but-uninitialized 表示拥有真实 Timer 数组和全局单元，不是 `emp`。
  `timer_running_initialization_consistency` 已接入 native 全局层并通过检查。
- `UCOS2_boot_state` 对应各 pool 初始化之后、首次系统 TaskCreate 之前的源码
  检查点；其完整纯 validity 已并入全局库，完整文件检查通过。此时 Timer 仍为 BSS
  状态，Task/Flag/Memory 默认名称分别传参，不假定编译器合并相同字符串字面量。
  该结论不建立全局原始堆的存在性，也不替代 C 初始化循环、名称引用存活期和 OSStart 证明。
- Timer 建池、记录两个 nullable Sem 结果、记录 Task 创建结果及 service time advance 的
  native 全局纯保持定理已通过完整文件检查。建池限于未运行的 Uninitialized 检查点；
  阶段更新不豁免实际字节重组，也没有把 Timer/Sem/Task 生命周期关系全部当成已完成。
- `mbox.v` 正式文件检查通过。Mailbox 与 Queue 的 NULL 语义分开：Mailbox 中 NULL
  表示空；Post/PostOpt 的无等待者存储分支拒绝 NULL 或要求对应的非 NULL 调用前提。
  取消息/存消息已证明保持完整 `event_in_range`，消息单元可以拆出并按新值重组；
  这些接口只拥有指针单元，不复制消息数据的独占权限，不假装已经证明阻塞/广播唤醒。
- `event_update_preserves_in_range` 作为 Event owner 的共用原位更新引理，明确要求
  新 payload/wait-entry 及原 queue binding 保持；不是假设整个后态有效性。native Event
  对象层的 split/merge/updated merge 已通过独立 debug 和全局库依赖编译，供各 IPC 模块共用。
- 单 Event 唤醒的 Task/Event/跨模块增量已通过完整文件检查（2026-09-10）。Task 以源码顺序
  区分 Dly/Msg/Stat/StatPend 前缀与 Remove 末尾的 EventPtr 清零；类型 mask 保留 suspension
  及非目标位，已就绪的 timeout-linked waiter 不被错误排除。Event 移除保持池/身份/payload，
  双向 Task 引用及跨 Event 唯一登记从现有关系推出；新组合还保持 Flag 登记排他、Mutex
  alias/owner/PCP 及物理调度缓存。`event_task_rdy` 的选择直接使用 Event 位图解码和
  实际 priority table，已证明对应 canonical 首 waiter 与精确返回 priority，复用既有
  Scheduler 数学引理。`UCOS2_event_wake_preserves_validity` 与基于实际解码操作的
  `UCOS2_event_task_rdy_preserves_validity` 也已通过完整全局模型及当前依赖集成检查：
  保持既有完整纯有效性集合与 idle-tail，未写的 Flag/Memory/Timer/Statistics/Control/Name
  约束原样保留；不由纯有效性凭空取得堆资源。后续窄位图增量也已完成全局模型集成检查：
  Scheduler 共用 OR 清位与条件组清位公式，Event 的逻辑删除对应逐 store 写后的 ECB image，
  保留非目标字段及 padding；字段和 map residual 均复用 QCP 拆合。Queue 更新保持真实 QCB、
  buffer 字节、发布绑定和池分区；`UCOS2_inv_merge_event_wake_storage` 消费实际写后
  Task/Scheduler/ECB 资源，接回其余全部 owner，而非只证明纯有效性。原值的全局 focus 接口
  是双向等价。无正式消费者、只有自反引理的旧 `native_queue_storage_frame` 已删除，以具体
  更新的已证保持接口替代；此前候选中的重复 Task 身份包装也已删除。当前结果仍限单 Event、
  8 行位图和选定数值 ABI；完整阻塞续体、符号 C 字段地址/配置桥接及 Multi/宽位图实例未完，
  不宣称全部 IPC C API 或所有模型已完成。本批未改 C、generated VC 或旧 manual。
- Flag 任意位置 unlink 的完整 `valid_flag_state` 保持已通过正式文件检查，涵盖首/中/尾
  节点、相邻 Next/Prev、组表头和其余组的保持。Task/Flag 双向关系进一步排除同一任务在
  Flag 节点尚挂链时同时登记 Event 等待；该条件覆盖 timeout-linked 阶段，已同步证明
  Tick 超时与 Task 发布保持。实际栈节点资源返还仍须空间证明，不能由纯关系代替。
- `task_flag_wake` 已给出清 FLAG bit、delay、FlagsRdy、pend result、FlagNode 的精确 TCB
  image 更新；`sched_wake_task` 保留物理缓存、允许任务原本已 ready，并已证明完整
  native Scheduler 有效性保持。OR 位图方程、单行更新后的数组重组已通过检查，不假定
  timeout-linked waiter 一定尚未 ready，也不把 suspended waiter 强行加入 ready set。
- `task_public_storage` 已有 live TCB 与单字段的 split/original merge/updated merge；
  residual 保留其余 TCB、free storage、roots、priority table 和 register allocator。
  Flag wake 的完整 `UCOS2_state_inv` 保持及三 owner 的全局 updated merge
  已正式编译通过；后者消费实际更新后的 Task/Sched/Flag 资源，非目标 Event 等模块的
  residual 等价单独证明，不假设整个后态 invariant 已成立。
- Flag timeout cleanup 另有独立变换、跨模块/完整纯有效性保持及全局 updated merge，
  均已正式编译。它只清 TCB 节点指针并摘链，保留已由 timeout 更新的 ready set 与物理
  缓存；挂链且 pending 已清的任务确实处于 timeout/delay=0 阶段，由现有关系推出。
  不把这一清理错误地复用成再次 wake，也不使原版 abort 的 double-unlink 获得幂等性。
- Timer 的头插入轮和任意位置 unlink 已证明保持完整局部 state/configuration，并已由
  最新全局库依赖检查编译。覆盖 wheel 成员/唯一性、Next/Prev/head、对象代际与池分区；
  row count 的 u16 界由池容量和 NoDup 推导。物理池非 NULL/地址单射仍取自实际 region
  条件；两操作的纯全局保持定理也已通过集成检查。Timer callback continuation、
  Sem/Task handle 关系及所有 API 族尚未全部接通。
- 本批 `ucos2_verify_inv.v` 固定工具完整文件检查通过；这是共享模型集成证据，未启动
  controller、未重生成 VC，也不将新增模型定理当作所有 C 函数已验收。Flag 邻接节点的
  原始堆重组/归还、Event private ECB/QCB 生命周期、完整客户端操作族和受影响旧 proof
  迁移仍是后续实施内容。
- 本轮受结构变化影响的 MutexAccept 完整 spec 与 manual proof 均已编译通过；旧 `lib`
  路径保留兼容导出。该结果不把历史切片规格升级宣称为完整 native 内核函数正确性。

后续增量（以下检查仅指各自模型/实际依赖，不覆盖尚未迁移的所有旧 C case）：

- QCP-backed 字段适配层已完整检查；原 Task 递归字段表示已移除。新 nil/cons/mono 均由
  QCP 现有接口导出，OS 库只实例化 typed cells 与字段清单。TCBInit 的 retained/written
  资源拆分和旧值遗忘证明已改为消费这些接口；完整 `task_tcb_init_spec.v` 及本次变化后的
  全局模型依赖已通过检查。既有 TCBInit manual proof 的五处字段展开已迁移到同一接口，
  完整 manual 文件检查通过；未改 generated witness、公开规约或 C 实现。
- `event_pool.v` 已完整检查：实际 20-byte ECB、padding、free/used/private 分区、free 链
  Type/Ptr、代际与私有 invocation 的新鲜性/唯一性，以及 detach/private-write/publish/
  rollback/recycle 的对应保持引理。OSQCreate 的 QCB 耗尽回滚只更新 Ptr/root；正常删除尾部
  则按源码更新 Type/Ptr/Cnt/root，不把未写字节清零，也不把 private ECB 当作 published UNUSED。
- `event.v` 与 `mbox.v` 已完整检查：上述生命周期已接入 native Event invariant/raw rep，
  initializer 建立真实 free image；发布需要 generation 对应和完整初始化 image，回收资源
  排除旧 live image。Mailbox 的消息 residual 保留完整节点（包括 padding），消息更新复用
  QCP-backed 字段重组。QCB 私有阶段见下述后续增量；跨模块/完整 IPC 调用族和恢复协议仍未完成，不宣称全局
  EventCreate/Delete C 函数已完成。
- Memory 私有 arena 的初始空前缀、当前链接字拆出、写后推进、末块 NULL 和完整 free-chain
  重组已完整检查。MCB 的 20/24-byte 配置改用同一个字段适配，已证明与原 typed-cell 布局
  双向等价，保留 Name。源序初始化、Get/Put 的 u32 回绕字段桥、实际 free-root pop 后的私有
  MCB/全局资源重组及最终 publish 也已完整检查；这些空间定理消费实际写后的 cells，不代替
  C store 或整个 OSMemCreate 的正确性证明。
- `queue_core.v` 已删除没有实际消费者的第二套 Queue state record，QCreate 只移除对应无效
  import；canonical `QueueFields`/`publishedQueueBytes` 保持唯一。尾部入队、头部入队、出队的
  总一致性及 wrap 索引保持、零容量入队失败均已完整文件检查；保留 NULL 消息，入队保持
  定理明确用于无等待者分支，不冒充 direct handoff 或物理 slot 写入证明。
- QCreate 规约中上述无效 import 的删除已通过受影响文件检查；未重跑 QInit。
  后续 QCB 创建阶段也已通过完整 `queue_core.v` 检查：`eventPrivateQueue` 复用已有 ECB
  invocation，三分区穷尽/互斥、合法域和 private owner 唯一性，pop 后实际 free-root/私有
  cells 重组，七字段 QCP adapter 与六次初始化写入，以及 Event/Queue 联合发布均已证明。
  初始空池可从真实 free-list 资源建立；ECB 摘取/私有字段写入/QCB 耗尽回滚分别保持 Queue
  资源，回滚要求该 invocation 尚未取得 QCB。上述初始化保留旧 OSQPtr 和 caller buffer
  字节，覆盖零容量；ABI 符号字段对应、完整 QCreate C 验证、删除回收与等待恢复仍分别处理。
- QCB 回收及 Queue buffer 归还的后续增量已通过完整 `queue_core.v` 检查。已发布 QCB/ring
  可以从共享存储拆出，旧 residual 明确排除被删节点；QCB link 写后重组、未写六字段保持、
  free/private/published 分区保持、删除 bytes 登记后其他队列不变，以及 Event/Queue 联合
  回收并归还原 `PtrArray.mixed_full` 权限均已证明。这里不执行 allocator、不清 buffer，
  也不替代 NO_PEND/ALWAYS 的前置唤醒循环、Task 跨模块关系或调度续体证明。
  新 QCB 三分区/创建接口和 Timer 有限扫描版本另已通过全局模型集成检查；随后追加的
  回收接口未改变既有全局不变式定义，其当前完整 Queue 文件检查也已通过。
- Queue 物理 ring 增量已通过完整 `queue_core.v` 检查（2026-09-10）。已证明尾插/头插的
  单槽更新、出队/Flush 的原字节保持、队头读取资源拆出，均复用 QCP `PtrArray` 拆合。
  QCB 按源码顺序写入后与逻辑后态一致，包含 Post/PostOpt 的不同回绕/count 顺序、未写字段
  保持及 UShort count 范围。新的同 QID 更新同时修改 canonical payload 与 buffer 登记，
  证明 Event 有效性、Queue 三分区/绑定保持、非目标 residual 双向运输及 Event/Queue
  共享资源重组；没有增加运行时元数据或假定整个后态有效。重复的 Queue 总一致性定义已
  改成 Event canonical predicate 的兼容名。该批没有改 C、generated VC 或旧 manual，
  不覆盖尚未完成的 waiter handoff、阻塞恢复、完整 API 观察及其 Task/Sched 跨模块证明。
- Timer callback/read-frame 与三字段游标已完整文件检查。Start/Stop/Delete/expiry 的真实读
  footprint、缓存 Next 值、remaining 严格减少和回调返回后的续体已建立；待访问节点的删除、
  generation/Next 改变有不满足 frame 的结论。当前 wheel suffix 从完整有效性、Next 链与原有
  非零/单射 pool 布局推导，单步调用端不再另传 row-history。这里的 callback-return 条件仍须
  由具体回调证明，不宣称任意回调、全局调度锁平衡或全部 Timer C API 已验证。
- Timer 已进一步完成有限内层扫描轨迹证明，并通过完整文件检查：在具体回调满足返回
  frame 契约时，执行记录的 visit IDs 恰为初始待访问行且无重复，最终 cursor 为 NULL，
  局部有效性和时间关系保持；服务时间推进包含 u32 wrap。它不证明任意回调终止，也不把
  内层扫描的有限性当作外层 Timer Task 无限循环终止。`kernel_resources.v` 的旧递归 byte
  predicate 已改为 QCP `UCharArray.mixed_full` 适配，nil/cons 保留原布局；Timer 与 Flag
  两个实际 padding 消费者均已通过定向检查。
- `interrupt.v` 已替换没有实际消费者的无条件计数模型：四个操作保留真实 running、ISR、
  零值和 255 饱和分支，exit 调度请求唯一确定，名称明确其只到调度前计数阶段。已证明
  UChar 范围来源/保持、未饱和配对恢复及饱和时 255→255→254 的实际结果；不把计数恢复
  当作整个含调度/回调函数的状态不变。全局层新增 Intr 的可逆 focus 与更新后重组，保留
  其他全部 owner 的真实资源。本批完整 `ucos2_verify_inv.v` 及其当前依赖已通过集成检查，
  包含 Queue 环保持和精简 Timer callback 版本；这不是全部 C API 的验证完成声明。

- 单 Event 等待登记增量已通过正式模型及 `atomic_ops_lib.v` 的完整依赖检查（2026-09-10）。
  Task 的 caller 前缀准确写 Stat、StatPend=OK、Dly，helper 仅写 EventPtr、Event 位图与
  ready 位图；已证二阶段与组合端点等价，保留 current/high-ready 缓存。等待集合插入、
  TCB 双向引用、Event payload、Task/Scheduler、Mutex/Flag 关系以及既有全局有效性与
  实际空间资源重组均有对应证明；不可用资源和单等待协议来自 caller，不作为虚构 C guard。
  `UCOS2_inv_merge_event_pend_storage` 保留 Queue buffer 和未聚焦 owner，字段、
  map、数组拆合继续复用 QCP。旧共享等待关系改用统一端点，移除重复 record 构造并修正
  StatPend 未重置/缓存提前刷新两处模型偏差。没有改 C、generated VC 或旧 manual；旧 Pend
  proofs 按模型优先顺序随后迁移。Multi 的组合状态位、借用数组与整组清理仍未实现完成，
  不由这组单 Event 定理推断全库模型或全部 IPC API 已验证。

- Multi 状态字节基础及真实消费者已通过完整模型依赖检查（2026-09-10，
  `atomic_ops_lib.v`，168.334 秒）。新 `task_status.v` 统一 pending mask、单等待兼容编码、
  Multi OR、byte complement/AND、超时结果及 suspension/MULTI 保持；范围与截断复用
  QCP IntLib。`event_wait.v` 从 unavailable Sem/Mbox/Q 类型列表推导 0..7 mask，证明
  非空时非零、append 累积与重复项幂等，并接到原始 TCB 三字段等待前缀；不要求输入
  `NoDup`，也不把 mask 计算当作资源取得/输出数组的完整语义。
  Task 中既有单 Event 等待/唤醒的 image 定理改用共同写入接口，旧 qualified 编码名保留。
  Tick 修复了原模型把 MULTI marker 清除并报告 Timeout 的偏差：只有 PEND_ANY 非零才
  清对应位/写 Timeout，否则保留 Stat/写 OK；已证明逐字段 image 对应及原 Flag-linked
  关系保持。单等待的一 tick 超时引理明确排除不是 pending bit 的 MULTI marker，Multi
  组合位超时由独立的完整字节定理覆盖。Task/Tick/Event 等待层和全局依赖均已检查，
  未改 C、generated VC 或旧 manual，也没有重新编译不相关旧函数。
  本批仅完成字节层；数组和整组循环的后续增量见下文。完整 Multi 仍缺条件 TCB 布局、
  跨调度数组存活和登记/唤醒/超时 cleanup 阶段与 ready 位图的组合关系。当前 `option PendType` 与
  `is_effectively_ready` 仍是单等待切片，不能用本批字节定理冒充全配置 Task/Scheduler
  已完成；剩余模块操作族和旧函数证明迁移仍按完整目标继续。

- Multi 数组/整组循环增量（2026-09-10）：`event_multi.v` 已实现真实基址、NULL sentinel、
  读出/归还和有界遍历接口，复用 QCP PtrArray 与 `Forall2_nth_iff` 绑定 live Event 实例；
  没有把 generation 当作 C 数组内的值，也没有额外拥有一份 Event 池。Task 中新增的
  MultiPtr/MultiRdy 仅为两字段切片，原数组借用不随 MultiPtr 清零自动消失。
  RemoveMulti 的逻辑循环与原始 row/group image 循环已对应；缺省清位前提由“必须是 waiter”
  推广到真实 TCB priority 有效，处理重复数组项和先前已被单 Event Remove 摘除的 waiter。
  单 Event 的原有全局重组调用同步使用可导出的 priority 前提，未改其语义结论。
  这一清理批次通过 `atomic_ops_lib.v` 完整依赖检查（174.202 秒）。后续登记批次增加了
  WaitMulti 的 Event-only 逐项 OR 循环、源序 endpoint、幂等/成员/规范序/身份保持，以及
  `atomic_event_multi_register_events` 消费者；当前整个 event_multi 文件已轻量加载通过，
  最终 `atomic_ops_lib.v` 完整依赖复验 passed/rc=0（174.463 秒），覆盖 Event/Task/Sched、
  既有全局模型消费者和新操作语义；未改 C、generated VC 或旧 manual，不是全函数验收。
  单元/数组/map 重组继续复用 QCP；仅对既有重组附加普通 frame
  的冗余包装已移除。此增量不覆盖完整 Multi-enabled TCB、Task/Sched 等待阶段及整个
  PendMulti API；新增文档明确 u16 返回计数、真实输出长度和是否等待的布尔观察必须分开。
  全库其余操作族与最后的旧函数证明迁移仍未完成。

- Multi-enabled 局部 TCB 增量（2026-09-10）：已把原 TCB 字节定义从 `task.v` 抽取到
  `task_storage.v` 并保持重新导出；字段拆合仍直接实例化 QCP MapLib adapter，没有第二套
  递归 SL 表示。新增配置字段索引，证明 64/72 字节清单覆盖、NoDup、关闭 Multi 的原表示
  等价与两个条件指针的拆出/更新合回；72 字节对象保留移动到 50/51 的 padding。
  Task 的 Multi Pend/wake/timeout/normal-cleanup image 保留真实写入与非目标 frame；
  `event_multi_borrowed_array_split_tcb/merge_tcb` 是完整 TCB 与续体数组切片的实际消费者。
  当前全部修改通过 `atomic_ops_lib.v` 完整依赖检查，passed/rc=0，251.403 秒。
  这不是全局 Multi 配置完成：全局 Task 池仍用原 64 字节 profile，旧 TaskStatus/ready 关系
  仍需替换或按真实等待阶段推广；跨调度借用存活、其他配置和全部 API 族仍未完成。
  数值布局定理不替代命名字段/ABI 桥接。未改 C、generated VC 或旧 manual。

- Multi 等待阶段与 Scheduler 组合增量（2026-09-10）：`task_multi_*_fields` 从真实
  status/result/delay/MultiPtr/MultiRdy 区分登记、超时仍挂接、唤醒后解链，已证明 Pend、
  timeout、wake 的字段关系及阶段互斥，不额外增加 phase 字段。`sched_ready_structure`
  提取 live/priority/排序/NoDup；按真实 suspension 位唤醒和 ready 清位保留该结构，
  OR/AND 位图编码不依赖单一 PendType，旧全局不变式没有被此较弱结构替代。
  `event_multi_wait_step` 组合两个 TCB 指针写入、原序 Event 循环、ready 移除，已证
  common TCB/物理调度缓存 frame、实际 TCB row/bit 读取对应，以及完整 Event wait-set
  的建立与清理。已选定 Multi 唤醒后缀保留首个 selected Remove 再遍历整组的次序，
  消费上述字段阶段和 source-level ready 操作；SEM|Q|MULTI 经 Sem 唤醒后仍 pending
  且已 ready 的具体区分情形也有 Qed，不再以单等待 ready 判定代替源码条件。
  最终 `atomic_ops_lib.v` 完整依赖检查 passed/rc=0，251.402 秒，覆盖本批 Task/Sched/
  EventMulti 与现有消费者；没有改 C、generated VC 或旧 manual。参考 LOS 的原生
  status 与合法性关系分层，设计文档取消“必须增加 phase 状态字段”的预设。
  全局 Task 的完整状态字节、Multi-enabled 池/生命周期、续体资源及其他配置/操作族仍待
  推广；本批不是全库模型完成，也不是全部函数已验证。旧函数 proof 迁移尚未启动。

- Task 生命周期配置 image 增量（2026-09-10）：`TCBLayoutField` / `TCBLayoutImage` 移到
  `TaskStateDef` 统一拥有；free image 与 private allocation 均使用该类型，不增加另一张
  Task 池或条件字段表。原分区、active/free 链、reservation、generation、invocation 和
  private-update 保持证明已适配，`TaskLifecycleAction` 也携带完整配置 image。
  free/private 字节表示、slot 地址和 free-link 采用 Multi-off/on 的 64/72 stride；字段
  split/原值 merge/updated merge 要求真实字段存在，继续调用 QCP-backed layout/map
  接口。boot 复用同一 free 初始化定义，回收仅更新 Next；关闭 Multi 时与原 64 字节
  common 表示的等价已证明。首次检查发现 free-head focus 仍写固定地址，已改为配置地址，
  Task 完整轻量加载通过后，最终 `atomic_ops_lib.v` 完整依赖检查 passed/rc=0，263.334 秒。
  该检查覆盖共享库与全局模型消费者，不覆盖尚未迁移的旧函数 spec/manual。
  公共 used Task 表示和顶层 profile 仍保留原 64 字节限制；真实 Multi 指针、完整状态
  字节、used 发布/回收与续体接口还需继续迁移。旧 TCBInit case 的 common-image 接口
  亦需随最终模型适配，不能沿用其旧检查声称当前依赖下已验证。未改 C/generated/manual。

- Task used/configured storage 增量（2026-09-10）：公共 used map 改为
  `used_task_rep`，与 free/private 共用 `task_slot_storage_rep`。
  完整 Task、字段 residual 及原值/更新重组已迁移到配置 image，字段 focus 必须证明
  实际存在；证明直接复用 QCP MapLib 和已建立的 layout 拆合，没有第二套资源算法。
  `task_slot_addr` 同时用于 active/free links、priority table、current/high-ready
  cache、Mutex owner 与 Flag node 的 TCB 回指，消除了 used 仍固定 64 字节的接口断点。
  固定 64 字节及 common image 的旧视图保留显式含义；关闭 Multi 时的 used rep、
  slot 地址和 Mutex owner 编码对应已证明。
  `tcbEventMultiPtr` 是源码的真实数组地址；原逻辑列表改名 `eventMultiWaitEvents`，
  保留顺序及重复项，不再以名称暗示它就是 C 指针。`task_set_multi_fields` 与源码
  WaitMulti 两指针写入的 image 对应、common frame 和公共 Task map 的拆出/更新后
  重组均已证明，数组本身的权限与登记/生命周期关系没有被这些空间引理替代。
  最终固定工具检查：`atomic_ops_lib.v` 完整依赖 passed/rc=0，281.014 秒；
  不在该依赖链的受影响 `mbox.v` 另行检查 passed/rc=0，170.864 秒。
  这两项覆盖本批共享模型与相关消费者，不覆盖旧函数 spec/manual 的完整证明闭包；
  共享库内已同步逻辑字段名引用，旧成果的最终迁移仍按用户要求留到模型全部完成之后。
  顶层 profile 仍关闭 Multi：完整 raw status、等待/ready 协议、数组借用、used 发布/
  回收闭包及其他条件布局/操作族仍须继续实现，不能将这次存储迁移记为全库模型完成。
  本批未改 C、generated VC、旧 manual 或历史 acceptance。

- Task canonical byte 与真实操作组合增量（2026-09-10）：`TaskStatus` 改为现有
  `Byte.int`，PendType 仅表示 mask 种类；不再用互斥 pending-kind record 丢弃组合位。
  Pend 的 OR、指定 mask 唤醒、Tick 超时及 Multi 正常收尾都作用于同一 Task；Tick 的
  完整配置 image 对应和 registered→expired-linked 保持已证明。单 Event Pend 的
  保持/全局重组从调用前 ready membership 及 Scheduler 有效性推出原等待位为空，
  再应用 OR 的单等待性质，不在 transformer 添加过滤或把 OR 偷换成赋值。
  canonical WaitMulti 与 selected/MultiPtr 非 NULL 的 wake 后缀已组合 Task/Event/Sched，
  证明 image 对应、整组 wait-set 清理、精确 ready membership、Task/ready 结构保持
  及其他 owner/物理调度缓存的 frame。数组顺序与重复指针保留；指针清零不代表
  caller 的数组借用已经归还，完整选择前缀与跨调度存活仍需组合。
  Suspend/Resume 共用单 status 字段更新，已证明完整配置 image、其余状态位与单等待
  linked phase 保持。selected-live-TCB 核心及 source-ready 条件已接入原子操作：Suspend
  清 ready；Resume 仅在 PEND_ANY 为零且 Dly 为零时插入 ready，不能消除残留 pending 位。
  Suspend 的 Task/Scheduler 保持与 Resume 的结构保持已证明；后者不冒充完整 Multi
  ready 协议，也不覆盖参数/SELF/error 前缀、hook、OS_Sched 或阻塞续体。
  最终固定工具检查 `atomic_ops_lib.v` 完整依赖 passed/rc=0，275.604 秒；
  不在该链的受影响 `mbox.v` 独立检查 passed/rc=0，166.316 秒。
  本批未增加状态字段、公理或 Admitted，未改 C、generated VC、旧 manual、controller
  状态或历史 acceptance。模型检查不能继承为旧函数证明的新版本验收。
  顶层 profile 仍关闭 Multi；借用/完整 ready 协议、所有配置与其余操作族，以及模型
  完成后的旧函数证明迁移，仍属整个目标的未完成工作。

- Suspend/Resume 全局闭包增量（2026-09-10）：从源码全部直接 `OSTCBStat` 写入与
  `ucos_ii.h:105–114` 的状态常量核对保留位来源；建立 `task_status_reserved_bits_clear`
  与 Task-owned `task_reserved_bits_clear`，不新增任何状态字段，也不限制 raw Byte 的值域。
  已证明无等待初值、Task 发布、单/Multi 等待 OR、任意 mask 清位、Tick、Suspend/Resume
  的对应保持。当前全局 bundle 纳入这一纯性质，并同步 boot、发布、Event Pend/wake、
  Flag wake/timeout cleanup 与 Memory/Timer frame；没有通过 raw 操作的额外 guard 保证它。
  `sched_resume_task` 与原子接口共用真实 PEND_ANY/Dly 判定，并在当前 Multi-off
  配置中由保留位性质证明它等于单等待 ready 更新。Event 等待列表规范性、双向引用、
  Flag 节点和 Mutex 关系的 status-update transport 已证明；资源重组直接复用现有
  Task/Scheduler split/merge、Event 下标等价和全局其他模块 residual，没有再建 SL 存储层。
  Suspend/Resume 的两个 state builder 移到 cross-owner 层，使全局保持与 atomic relation
  共享同一更新，消除了上层对原子库的潜在循环依赖与重复 ready 决策证明。
  `UCOS2_task_*_preserves_validity` 与 `UCOS2_inv_merge_task_*` 已通过固定工具
  `atomic_ops_lib.v` 完整依赖检查，passed/rc=0，275.211 秒；独立的 `mbox.v` 受影响检查
  passed/rc=0，165.355 秒。
  本批没有修改 C、generated VC、旧 manual、controller 状态或历史证据。
  这完成的是 selected-live-TCB 核心的当前配置全局闭包，不覆盖 API 有序错误/SELF/
  priority-table 选择、hook/OS_Sched、完整 Multi 续体及其余操作族。全库模型和之后的
  旧证明迁移仍未完成，不把此次模型结果记为整函数或整个目标完成。

- Suspend/Resume 函数阶段与环境动作增量（2026-09-10）：新增
  `VC/code_proof/task/spec/task_suspend_spec.v` 与 `task_resume_spec.v`，将函数专用的
  参数 guards、任务选择、NULL/reserved/未 suspended 错误及成功分支留在对应 spec。
  参数检查与 Save 后的临界区更新分开；复用已证明的共享 state builder 和全局 merge，
  没有复制状态模型或在共享 lib 中另写两套完整 API。已证明配置关闭时无虚构参数错误、
  检查成功后的索引范围、实际分支构造、结果/后状态确定性、错误 frame 与全局保持/重组。
  Suspend 的 SELF 来自真实 current TCB priority，不取 OSPrioCur 缓存；允许 table alias
  指向 current priority 不同的 TCB。显式 idle 参数的拒绝不被偷换成 SELF 解析后的检查。
  当前 Suspend 读域显式要求 live current TCB；此调用入口义务不能仅由 cache 范围推出，
  其他 raw/free-current 阶段若可由实际 caller 到达，仍需相应的读取接口与来源证明。
  Resume 的 ready 分支按 PEND_ANY/Dly 判定并保留为局部控制流结果，Restore 后另读
  OSRunning；不把旧 running 快照或再次读取 TCB 当作源码。ready trace 的调用效果仍由
  call-site contract 单独组合，不能把当前核心端点冒充已执行 trace/Restore 的端点。
  两个 `task_*_critical_client_certificate` 实例复用原有 KernelClientCertificate：
  证明当前全局有效性、创建者 private reservation/storage frame 与未退休 invocation
  身份保持。共享 Task 只增加 `glob_task_set_usedtask_preserves_invocation_active`，
  复用现有 map 更新，并以同一 slot/相同 generation 为身份来源；没有新增状态字段，
  也不把 active 或 stops=false 解释成 ready、立即返回或最终必然返回。
  检查：共享 `task.v` passed/rc=0，108.456 秒；随后以仅 Require 两个新 spec 的临时
  wrapper 运行固定 `coq_tooling.py check`，最终联合依赖编译 passed/rc=0，281.636 秒。
  本批临时 wrapper/debug 已移除；源码与证明分别保留在上述两个正式 spec 和共享 Task。
  未改 C/generated/旧 manual/controller/历史 acceptance，未新增公理或 Admitted。
  actor/Save/Restore 的源码嵌入、平台/trace/OS_Sched 及原调用恢复仍须组合；本批不宣称
  整函数 C 验证完成。全部模型、其余操作族和最后的旧证明迁移仍按完整目标继续。

- Scheduler 源码准备阶段增量（2026-09-10）：完整核对原版 `OS_Sched`/`OS_SchedNew`
  及 header 的 `OSCtxSwCtr : INT32U`、priority byte/pointer 声明，新增
  `VC/code_proof/sched/spec/sched_spec.v`。准备阶段只以 int/lock 为零决定是否选择；
  切换请求比较真实 high/current priority 字节，不补 OSRunning/current-live/空 ready
  guard。不切换仍更新两个 high-cache 单元，切换前对 UInt counter 加一并回绕，
  current-task/current-priority 缓存保持原值，留给真实平台操作。
  共享 Scheduler 新增 counter 更新及原值/更新后的字段拆合、范围保持；复用已有
  位图最小选择、table 读取、两次 cache 写入与 QCP 分离逻辑重组，没有第二套位图算法。
  `os_sched_prefix_physical_rep` 表达包括空 ready/NULL/reserved 选择在内的物理端点，
  不把不满足正常调用域的路径替换成 no-op。注册/范围与“开启选择时 ready 非空”成立
  后，才由已证明的对应关系接回 `os_sched_ready_checkpoint`；后者不是 source-total
  替代实现。非空来源仍须从实际 caller/idle 协议建立。
  已证明请求条件、同任务但 cache 陈旧时仍请求切换、不切换时 high refresh、counter/
  current/ready/running 观察、Scheduler 保持及真实资源接回全局不变式。
  `UCOS2_replace_sched_preserves_validity` 集中复用跨模块 frame，以新 Scheduler
  有效和 running 不变为前提，不重复每个调用者的全局拆解。
  平台 cache-install 下的 selected-task boundary 是条件性的目标状态结论，不证明
  ARM/BSP、栈/TCB 保存、hooks 或原调用返回。当前 profile 的 TaskProfile/TLS 关闭；
  其他配置的额外 Task 字段写入、TLS 调用及完整中断/调度续体仍待组合。旧 atomic_sched
  的 ready/任务 ID 简化只在缓存一致性桥前提下适用，未借本批改动迁移旧函数证明。
  最终固定工具 `coq_tooling.py check` 以新 `sched_spec.v` 为 target 检查完整依赖闭包，
  passed/rc=0，267.765 秒；本批调试文件已移除。未改 C、generated、旧 manual、
  controller 或历史证据，未新增状态字段、公理或 Admitted。
  这不是整个 OS_Sched 或全库模型完成；其余操作族、平台/调用组合与最后旧证明迁移
  继续保留在完整目标中。

- Interrupt/Scheduler 计数与准备阶段增量（2026-09-10）：新增
  `VC/code_proof/interrupt/spec/int_enter_spec.v`、`int_exit_spec.v` 和
  `VC/code_proof/sched/spec/sched_lock_spec.v`，共同使用 `interrupt.v` 的四个源序计数
  transformer。Enter 按调用协议在已屏蔽中断的状态中读取 running/nesting，自身没有
  Save/Restore；Exit/Lock/Unlock 的 running 分支在 Save 前观察，计数则在 Save 后读取。
  observed 参数仅为该源码分支的局部索引，不增加 OS 状态字段，也不预设两次读取间相等。
  已证明机器计数范围、未 running 的无写入、解锁零值的无调度、实际请求后的零计数，
  以及消费更新后两个 UChar 单元、保留其他模块真实资源的全局重组。未饱和配对等式
  只描述无中间环境步的组合；原有饱和反例继续保留，不声称调度锁持续屏蔽 ISR。
  Exit 的 old nesting=0 与 1 均可触发选择；复用 `sched_spec` 的位图/table/high cache/
  counter 准备证明，保留 current caches、Task 身份和其余状态。其逻辑 checkpoint 接回
  全局表示仍要求实际调用方提供选择时 ready 非空的来源，不把该条件伪装为源码 guard。
  Unlock 仅在 old int=0、lock=1 的已走分支请求调度；请求跨 Restore 保留，OS_Sched 的
  实际选择须用后续调用自身的 Save 后状态，不能提前在 unlock checkpoint 上执行。
  精简共享层：移除无源码/证明消费者的四个 `atomic_int_enter/int_exit_nesting/
  sched_lock/sched_unlock_nesting` 整状态包装、专用 `SchedTrigger` 及其两个包装引理；
  移除本批尚未被消费的 exit 专用非负保持/重组候选。统一采用已证明的
  `interrupt_inv_merge_counters`，直接复用 QCP 的类型范围、`coq_prop_imply` 和合取规则。
  没有新建字段存储、计数状态层、公理或 Admitted。
  检查：共享 owner 的 fixed debug 最终通过；仅 Require 三个正式 spec 的临时 wrapper
  经 `coq_tooling.py check` 完整联合依赖检查 passed/rc=0，295.335 秒。临时 debug/wrapper
  已移除；正式定义与证明保留在上述文件。未改 C/generated/旧 manual/controller/历史成果。
  该结果不包含 Save/Restore、trace/TLS、OSIntCtxSw 的源码调用嵌入或原 ISR/任务调用返回，
  也不等于整 C 函数验证、全库模型完成或既有证明迁移完成。
  后续 Task 删除已定位一个真实共享阶段：源码在 Restore 前将 Dly 清零、Stat 清为 RDY，
  但 TCB 仍在活跃链且不在 ready 集合；当前 `sched_ready_in_range` 的 ready 双向
  关系不能直接表达它。需按已设计的 retirement 协议处理，而不是给公开 API 添加排除条件。

- Task 删除准备/回收增量（2026-09-10）：`lib/task_retirement.v` 现提供三字段准备更新、
  ready-excluded 阶段和源码相邻节点解绑/回收。阶段用参数及已有 generation 表达，没有
  新增 OS 状态字段。回收已证明完整 Task owner 的 pool partition、active/free links、
  count、priority registration、generation/reuse 保持；另证 idle-tail 保持、非 idle 目标
  的真实 successor，以及回收后从删除阶段恢复普通 ready 关系。保留源码 u8 count 语义，
  只清选中的 table 槽；不把旧 alias、应用栈或调用续体凭空回收。
  `task_recycle_public_storage_merge` 消费实际写后的节点 residual、image、roots、
  count/table cells；资源拆合复用 QCP map 和既有 free-storage 接口。发现的同名重复
  image 定义已移除，改为组合已有 `tcb_recycle_image` 与条件 Name 写入。
  删除专用阶段、负例及前缀规约归 `VC/code_proof/task/spec/task_delete_spec.v`，不留在
  共享 lib；其回收检查点直接消费上述 owner/ready 保持结论。前缀保留 safety/ISR/idle/
  range 的真实顺序，SELF 读取当前 TCB priority，显式参数不凭空要求读取 current TCB。
  检查：共享库完整 fixed check passed/rc=0，128.671 秒；函数专用 spec 最终完整依赖
  检查 passed/rc=0，138.950 秒，覆盖本批实际消费者及共享回收库。两份临时 Load debug
  文件已移除；没有重编译不相关旧 C case。
  [官方 API Reference](https://micrium.atlassian.net/wiki/spaces/osiidoc/pages/163887) 对
  Suspend/Resume 标注 Task-only；当前据此区分调用协议与源码未设置 ISR guard 的事实。
  其他章节的 ISR Resume 叙述差异记录在 design。操作级 Suspend→Resume 负例继续保留，
  不再误把它当作已证合法 ISR 反例；正 lock 阻止 IntExit 调度的局部证明不代替整个窗口。
  后续组合使用 callee 之后的 TCB：单 `OS_EventTaskRemove` 在末尾清 EventPtr，已有
  `task_set_event_ptr` 可复用；Multi remove 不写 TCB。不能把准备阶段的字段 frame
  理解为跨这些调用保留入口旧值，也无需为此新建一份指针状态。
  下一步仍须完成共享删除阶段的 Event/Flag/alias 与合法环境操作闭包、hooks 和调度续体，
  以及全库其余模型；旧函数迁移在全库模型完成后进行。本批未改 C/generated/旧 manual/
  controller 或历史验收成果，不宣称整函数或全库模型完成。

- Task 删除的单等待清理组合增量（2026-09-10）：
  `task_delete_spec.v` 的 `task_delete_prepare_single_wait` 已连接无等待、单 Event、Flag
  三类源码分支及后续三字段准备。所需 Event/Flag lookup 的存在性和登记互斥从当前
  owner/跨模块关系推出，不新增错误分支或把期望 post-invariant 塞进运行时 guard。
  已证明 Task/Event/Flag owner 与跨模块关系保持，并建立实际 live-but-not-ready
  阶段。Flag 分支保留摘下的 waiter，供已有节点 loan 归还接口消费；不释放应用栈，
  不提前回收 TCB 或终止原 invocation。
  共享 `cross_module_invariants.v` 提取 Event removal/Flag unlink 的实际共用保持引理；
  原 wake/timeout theorem statements 不变，改为直接复用，未再复制一套删除专用跨模块库。
  两个函数级资源重组定理消费真实写后 Task/Scheduler、ECB image/map residual 或
  Flag 邻居资源，复用 `event_remove_waiter_reconstructs_raw_rep` 和
  `flag_unlink_reconstructs_raw_rep`。没有新增 OS 状态字段、存储框架、公理或 Admitted。
  检查：共享库完整 fixed check passed/rc=0，189.480 秒；函数级组合与资源证明的最终
  fixed debug passed/rc=0，3.906 秒；`task_delete_spec.v` 完整依赖检查 passed/rc=0，
  209.276 秒。证据属于 standalone model development，不是 controller acceptance；
  临时 Load 脚本已移除，未重编译不相关旧 C case，也未修改 C/generated/旧 manual。
  当前结论覆盖 selected native 单等待配置；Multi-enabled 仍需其数组借用/整组清理和
  全局等待关系推广。回收后的 alias/Event/Flag 闭包、Restore 窗口的合法环境保持、
  trace/hooks 与调度/自删续体仍待组合；全库其他模型和最后的旧证明迁移继续保留在目标中。

- Task 回收的跨模块组合增量（2026-09-10）：
  `task_delete_prepared_has_no_wait_registration` 从实际 RDY/OK 准备阶段和既有等待关系
  推出 Event/Flag 登记已清理；不另加同形 annotation 前提。回收后保留其他 Task 的
  非链接字段，Event 运输接口只要求实际 waiter 存活，不再要求被删除的无关 Task 存活。
  Mutex alias 协议在目标未持锁时推出其唯一合法表槽为 current priority，据此证明仅清
  捕获槽后的 owner/alias 保持；该前提是独立的调用协议条件，不是源码新增 guard。
  另证回收仍持锁的 Task 会破坏 owner snapshot 存活关系，不据条件定理扩大正确性声明。
  native 优先级表关系限于源码真实数组的 `task_priority_in_range` 域；域外 total-map 键
  不是额外 C 单元。同步适配创建、更新和全局启动证明，未放松任何实际表槽的约束。
  `task_delete_recycle_preserves_relations` 已组合 Task/Sched/Event 和跨模块恢复；
  `task_delete_recycle_event_rep_eq` 复用既有等待编码接口运输未改写的 Event 堆表示。
  检查：共享跨模块库完整 fixed check passed/rc=0，204.516 秒；最终 global/spec 联合
  fixed debug passed/rc=0，19.407 秒；仅 Require 两个正式模块的 wrapper 完整依赖
  检查 passed/rc=0，286.354 秒。修复了启动证明接收合法表下标前提的一行适配。
  临时脚本已移除；没有新增状态字段、存储框架、公理或 Admitted，未改 C/generated/
  旧 manual/controller。上述证据属于 standalone model development，非整函数验收。
  Restore 窗口的合法环境保持、调用协议来源、hooks/Multi 和自删调度续体仍须组合；
  全库其他模型及最后的旧证明迁移均继续保留在完整目标中。

- Tick 与 Task 删除阶段的保持增量（2026-09-10）：`tick_task_step` 直接复用
  原有 TCB timeout 与 Scheduler status-bit 更新，保留旧 delay=0 的真正无写入分支、
  非零递减和归零后的真实 suspension 测试；Multi 残余位不被伪造 guard 排除。
  已证明 Task owner、Event owner、Event/Flag timeout-linked 登记及 Mutex/table
  跨模块关系保持，并通过既有优先级编码接口运输未写入的 Event 堆表示。
  Event entry/object 的字段与阶段运输提取为共用接口，旧 status/Suspend/Resume
  theorem statements 保持不变并直接复用，不再复制一套 Tick 等待关系。
  删除规约已组合单 cursor 的 Task/status、保存 generation 的准备阶段及上述关系：
  zero-delay 删除实例不会重新 ready，其他任务仍可正常超时。普通 ready-excluded
  结论明确使用 no-Multi reserved-bit 协议；完整 Multi 全局关系没有冒用该结论。
  检查：Task/retirement 完整 fixed check passed/rc=0，134.885 秒；Event 运输 fixed
  debug passed/rc=0，3.297 秒；cross-module 完整检查 passed/rc=0，198.029 秒；仅
  Require 当前 global 与 task-delete spec 的 wrapper 联合依赖检查 passed/rc=0，
  281.545 秒，包含旧 status 接口的全局消费者。联合检查刷新了旧 interrupt 编译缓存，
  没有为此修改其语义。临时脚本已移除；没有新状态字段、存储框架、公理或 Admitted，
  未修改 C/generated/旧 manual，证据属于 standalone model development。
  此增量是 Tick 单迭代的实际保持，不是整段遍历、整个 Restore 窗口或整 C API 证明。
  其他合法 ISR 动作、hooks、游标/调用续体、全局共享阶段及全库其余模型仍须继续组合；
  所有模型完成后再迁移旧函数证明的原目标不变。

- Event/Flag 唤醒与删除阶段的保持增量（2026-09-10）：单 Event 原始端点现使用
  `sched_wake_by_status`，按源码只检查 suspension 位；普通 ready 条件的等价性
  从已有 waiter/Task 登记关系推出，没有新增公开 guard。同步适配普通全局保持消费者。
  `task_delete_spec.v` 已组合 Event 位图/table 选择和 Flag 节点/TCB 选择，证明唤醒
  保持保存的删除实例、ready-excluded 阶段及 Task/Event/Flag/Mutex 关系；目标不同性
  来自实际登记清空，而非“ISR 不得选择删除目标”的附加前提。
  `flag_task_rdy` 保留源 BOOLEAN：整个 Stat=0 才执行 ready 写入，false 仍写
  TCB 并 unlink；true 不必表示新加入 ready。全字节等式复用 status 分解，合法节点的
  操作存在性和物理 TCB 地址对应已证明，故不只建立成功返回条件下的保持定理。
  共用 `flag_linked_node_unlink_exists` 替换 Task 删除中重复展开的查找证明；新增选择
  端点复用原有 TCB/Scheduler/unlink 转换，无新状态字段、存储框架、公理或 Admitted。
  检查：最终共享 cross 模块 fixed debug passed/rc=0，5.323 秒；仅 Require 当前
  global 与 task-delete spec 的 wrapper 完整联合依赖检查 passed/rc=0，283.034 秒。
  检查过程中修复了结果分解后的等式化简和 Flag phase 的展开位置，不改变 theorem
  前提来回避诊断。临时脚本已移除；未改 C/generated/旧 manual/controller，结果属于
  standalone model development，不是整函数验收。完整 Restore 环境、资源/调用组合、
  Multi/其他配置、hooks 及其余全库模型仍未完成；旧函数证明按原目标在模型完成后迁移。

- 删除共享阶段与全局组合增量（2026-09-10）：将 Scheduler 既有 metadata 条件提取为
  `sched_metadata_in_range`，全局使用 `UCOS2_state_inv_with_ready`
  共用主体，普通不变式的逻辑内容不变。TaskDelete 的共享阶段保留完整共享堆及所有
  非 ready 条件，清理建立、Tick/Event/Flag/中断计数核心步保持及标准有限闭包已证明；
  closure 保持 lock，正 lock 阻止 IntExit 请求调度，满足最终回收条件时恢复普通全局
  有效性。重组定理明确要求实际 post-store 堆，不从纯 trace 生成空间所有权。
  检查：普通全局依赖检查 passed/rc=0，267.776 秒；完整 TaskDelete spec 的 fixed
  debug passed/rc=0，4.693 秒；全局与 TaskDelete、Suspend/Resume、Scheduler/Lock、
  IntEnter/Exit 规约模型联合检查 passed/rc=0，329.9 秒。没有新增状态字段、公理或
  Admitted，未改 C/generated/旧 manual；结果为 standalone model development，
  不是这些 C 函数的重新验收。有限核心步并非完整 ISR 调用族，实际 token/调用嵌入、
  资源借还、hooks/Multi/其他配置及其余全库模型仍未完成，旧证明仍在模型完成后迁移。

- 删除窗口的入口条件运输增量（2026-09-10）：上述核心步闭包进一步保持整个选中
  TCB、priority table、task count 与 lifecycle，运输未持锁条件和全部原 invocation 的
  live 身份；复用既有 saved-token/creation-frame 接口运输调用登记及已持有的私有
  storage assertion。没有从纯关系制造 token/堆，也没有把第二次 Save 的新 CPSR
  视为原值。实际 lock 增减已接到窗口后回收：未饱和时恢复 lock，入口 255 时得到
  254；interrupt nesting 不被强行恢复为入口值。回收所需 count 上界由当前池不变式
  推出，不额外索要相同 caller 前提。最终完整 spec fixed debug passed/rc=0，
  4.898 秒；受影响 TaskDelete spec 完整依赖检查 passed/rc=0，280.542 秒。
  仅改专用 spec 及这三份文档，没有修改 C/generated/旧 manual；此结果不包括
  未建模的 ISR API、Delete/TLS hook、真实平台调用嵌入及最终调度返回。

- Queue 更新的全局组合增量（2026-09-10）：共享跨模块层增加按实际 kind/Mutex/
  waiter 字段不变运输的引理，Queue 不另造 Task 或同步状态。完整 Event/Queue 双向
  拆分与写后合回使用既有 QCB/ring/missing-node 接口，residual 保留所有非目标模块；
  same-QID 更新不虚构 ECB 字节写入。普通全局有效性和 Flush 的 ring 后态保持已闭合，
  buffer binding/partition 仍从真实空间资源重组，不由纯有效性凭空取得。
  共享 cross 模块 fixed debug passed/rc=0，5.508 秒；完整 global 模型 fixed debug
  passed/rc=0，19.332 秒。首次集成诊断仅为 Event replacement 投影未化简，已修复，
  不改变 theorem 前提；最终 global/TaskDelete 联合依赖检查 passed/rc=0，284.904 秒，
  覆盖本次共享变更及已完成的删除窗口模型消费者。三个本批临时检查脚本已移除。
  未修改 C、generated VC、旧 manual、历史 acceptance 或 controller；此项不代表
  OSQFlush、QCreate、Queue 阻塞/唤醒族等完整 C 函数已经验证。

- Queue Post 家族组合增量（2026-09-10）：新增
  `VC/code_proof/queue/spec/q_post_spec.v`，覆盖 Post/PostFront/PostOpt 的独立参数/type
  观察、Save 后至 Restore 前的真实分支、返回码和后续调度调用请求。复用 canonical
  Event wake、Queue ring/slots、两种尾插写入顺序与全局资源重组，不增加 OS 状态字段。
  EventGrp 为零与 canonical 等待列表为空的等价性由 Event owner 复用既有 Scheduler
  head-bit 定理建立，不把未经证明的列表条件替换进源码，也不新增 source guard。
  广播每轮使用当前 bitmap/table 选择和实际 wake 端点，已证明有限执行存在与唯一性、
  迭代次数等于初始等待者数量、最终等待列表为空及原 QCB/payload/buffer 字节保持。
  每个初始等待者的最终 TCB 恰为原 TCB 经同一消息/PendOK 的真实 wake 更新，非等待者
  TCB 不变；NULL 消息、suspension 位和未知 option bits 按源码保留。实际 global residual
  经每次 wake 运输，不由 pure trace 产生写后 TCB/ready/ECB 空间资源。
  无等待者路径的操作存在性、全局有效性、slot/QCB 写后重组和 full 错误不修改状态均已
  证明；full guard 保留 `Entries >= Size`，允许零容量。调度布尔值仅在唤醒分支且未设置
  NO_SCHED 时为真，表示随后调用 OS_Sched，不声称实际切换或当前 invocation 已返回。
  检查：Event 增量完整检查 passed/rc=0，160.746 秒；共享 global 完整依赖检查
  passed/rc=0，270.579 秒；最终完整 Post spec 的 fixed debug passed/rc=0，3.674 秒；
  该 spec 完整文件/依赖检查 passed/rc=0，276.985 秒。调试修复限于析构后的重写和
  中间状态的显式实例化，没有增强语义前提。临时 Load 脚本已移除，未修改 C/generated/
  旧 manual/controller 或历史 acceptance。此结果属于 standalone model development；
  type 读取与 Save 入口的身份连接、trace/平台调用、Restore 后调度续体、完整 Multi 配置
  和其他 Queue 操作族仍待组合，不等于三个 C 函数或全库模型已全部验证。

- Queue Pend 分段模型增量（2026-09-10）：新增
  `VC/code_proof/queue/spec/q_pend_spec.v`，分开 safety/参数/context 观察、首个临界区
  和调度后的返回临界区。立即路径返回实际 head-slot（允许 NULL/NONE）且保留 buffer
  全部字节；等待路径复用单 Event 登记，不提前承诺同一调用已返回。两段的存在性、
  确定性、全局有效性及 invocation 存活保持均有对应定理。超时通过 reference closure/
  backlink 找到仍存活的 Event 并摘链；OK/abort 不读旧 Event，可在 Delete 已回收后返回。
  Task 的公共清理精确对应 Stat/StatPend/EventPtr/条件 Multi/Msg 写入，并证明完整配置
  image 对应；Dly、priority、其他 TCB 及 Scheduler 状态保持。原 Multi 清理改为复用
  状态/消息公共前缀，原有字段语义不变；不使用 Sem 的不同收尾代替 Queue 行为。
  全局提供实际写后资源与非目标模块 residual 的重组，未从纯状态等式制造空间资源。
  本批发现并纠正“ready 即可得到非 idle 优先级”的错误推断：native 索引允许 idle，
  合法阻塞调用按 [Micrium 手册 §3.08](https://datasheet.octopart.com/KRN-K2XX-PKG000-P-P1-Micrium-datasheet-27615537.pdf#page=124)
  排除 idle hook 调用 Pend。等待保持显式保留该调用义务，raw 分支不加 guard；实际
  caller/hook 遵约与原 invocation 返回仍需后续调用组合，不能说已由全局不变式推出。
  检查：共享 cross fixed debug passed/rc=0，5.461 秒；global fixed debug passed/rc=0，
  20.691 秒，完整共享依赖检查 passed/rc=0，272.155 秒；完整 Pend spec fixed debug
  passed/rc=0，3.622 秒；该 spec 的固定完整依赖检查 passed/rc=0，283.112 秒。
  四个本批临时 Load 脚本已移除，构建缓存保留供后续模型检查使用。
  未新增 OS 状态字段、公理或 Admitted；未改 C、generated VC、旧 manual/controller
  或历史验收。Multi-enabled 全局实例、Save/Restore/trace、输出与栈资源、跨调度恢复及
  其余模块操作族仍未完成；旧证明迁移继续保留在全部模型完成之后。

- Event 广播复用与 PendAbort 家族增量（2026-09-10）：将 Queue Post 的广播归纳提取到
  `VC/code_proof/event/spec/event_wake_spec.v`，按实际 kind/message/result 参数化；Post
  保留已有八个观察定理的 statement，证明体直接实例化共享结果。共同循环仍逐次使用
  当前 EventGrp、priority table 和真实 wake 端点，证明有限性、确定性、接收者/非接收者、
  residual 与 invocation 保持，不增加另一套 OS 状态。
  新增 `event_pend_abort_spec.v`，完整核对 Sem/Mbox/Queue 三个 PendAbort 执行体，三个
  模块的专用 spec 只绑定 type/mask。保留 safety/参数/type 顺序、无 ISR/lock 拒绝、
  仅 opt=1 广播及其他值单次 abort。计数复用 CompCert Byte 的窄化/加法，给出零值和
  每次递增/前缀追加对应；当前 Task 池上界推出至多 22 个 waiter，故有效调用无回绕。
  已证明存在性、确定性、准确 count/error/调度请求、Event payload 与 Queue buffer
  保持、原 invocation 和完整全局资源重组；后态 TCB/ready/ECB 空间资源由实际写入提供。
  abort 数量不等于新 ready 数，suspension 保留；perr 写入仍等待真实 Restore/OS_Sched
  返回组合，未把临界区端点当成整个函数返回。
  检查：共享广播完整依赖检查 passed/rc=0，282.2 秒；Abort 全文件 fixed debug
  passed/rc=0，4.978 秒，完整依赖检查 passed/rc=0，290.31 秒；三个专用接口与当前
  Post 联合 fixed debug passed/rc=0，3.825 秒，联合依赖检查 passed/rc=0，325.843 秒。
  首次联合检查会话消失且未生成目标产物，确认无存活进程后只恢复该未完成检查，未重证旧
  函数。五个本批临时脚本已移除，构建缓存保留。未改 C/generated/旧 manual/controller，
  旧 `lib/sem_pend_abort_spec.v` 留待最终迁移；上述证据仅属 standalone model development。
  全操作族、Multi、平台/调用/输出资源组合及最后旧证明迁移仍在完整目标内，未宣称全库完成。

- Queue Delete 与回收组合增量（2026-09-10）：新增 `queue/spec/q_delete_spec.v`，完整
  核对 os_q.c:241--348，保留 safety/IEC runtime、参数、trace、type/ISR 顺序及实际
  NO_PEND/ALWAYS/invalid 分支。ALWAYS 复用公共 abort 广播，调度请求取原始
  tasks_waiting，而非最终 bitmap 或新 ready 数；错误返回原句柄并保持状态。
  回收复用已有 `queue_recycle` 和源序 QCB/ECB 存储接口，注销 buffer binding
  但不调用 free。跨模块层提取 `cross_module_consistency_event_transport`，
  payload 更新与空的非 Mutex Event 删除共用证明，原更新定理 statement 不变。
  既有 Task reference backlink 加空 wait list 推出没有残留 TCB 引用，无须新增 caller
  unreferenced 前提；Mutex/table 的保留条件明确排除把该删除规则套到 Mutex 上。
  `UCOS2_queue_recycle_preserves_validity` 与 `UCOS2_inv_merge_queue_recycle` 将真实
  写后的 pool/root 资源接回完整全局不变式，并分离归还原 `PtrArray.mixed_full`。
  Delete 的存在性、确定性、错误帧、Event 删除、buffer 注销、全局有效性、原 invocation、
  ALWAYS 后的准确 abort TCB 和调度条件均已证明。Pend 的 abort 续体不需要再读取已回收
  Event，与其既有分段模型一致，但没有提前保证原调用已经恢复运行。
  检查：共享 cross 全文件 fixed debug passed/rc=0，5.775 秒，完整依赖检查
  passed/rc=0，199.613 秒；global fixed debug passed/rc=0，20.907 秒；最终完整
  Delete spec fixed debug passed/rc=0，3.67 秒。Delete/Pend/Post/三类 PendAbort 的
  联合依赖检查 passed/rc=0，338.988 秒；首次集成仅修复一处局部假设重名。
  四个本批临时脚本已移除，构建缓存保留。没有新增 OS 状态字段、公理或 Admitted，
  未改 C/generated/旧 manual/controller；证据属于 standalone model development。
  names/Multi 配置、平台/trace/Save/Restore、输出资源及调度返回的整调用组合仍未完成，
  不能将上述分段模型记为 OSQDel C 验证或全库模型完成；旧证明迁移顺序保持不变。

- Queue Accept/Query 与数组复制增量（2026-09-10）：新增 `queue/spec/q_accept_spec.v`
  和 `q_query_spec.v`，核对原版的参数/type 顺序及两个临界区执行体。Accept 的非空
  分支复用 canonical dequeue，空为 NULL/Q_EMPTY，成功允许 NULL/NONE；perr 写在
  Restore 前。已证明存在性、确定性、全局有效性、invocation 与全部 buffer 字节保持，
  并把实际 head slot 与返回消息连接。Pend 的立即出队有效性/全局写后重组提取到
  `UCOS2_queue_dequeue_preserves_validity` / `UCOS2_inv_merge_queue_dequeue`，
  原 Pend 定理 statement 不变，证明委托公共接口；Queue owner 提供同 QID 与真实
  published-bytes 原值保持，未另造一套 FIFO 或 Task 状态。
  Query 的临界区内核状态保持，只有非空时读取实际 ring slot，不推进 Out、不清 buffer；
  存在性、确定性及 group/rows/head/count/size 的精确观察均已证明。新增 snapshot record
  只是调用者输出，不是全局抽象字段。输出写入按 group、typed OS_PRIO table loop、
  message/count/size 分开，使用 QCP 符号字段地址与 UCharArray/UShort/Ptr typed cells；
  padding 留给外部 frame，既不猜数字偏移，也不把该循环称为 OS_MemCopy。
  沿用已有 `copy_prefix_list`，补共享 length/step/complete 引理；Query 的循环实例
  使用 option-valued mixed-array，写后 merge 消费真实新 cell，并保留未复制的原后缀，
  不要求调用者的输出数组预先初始化。原值拆分与写后合回复用 QCP ArrayLib。
  检查：共享 global fixed debug passed/rc=0，21.124 秒，完整依赖检查 passed/rc=0，
  281.896 秒；新增数组引理 fixed debug passed/rc=0，3.573 秒；Accept/Query/Pend
  联合 fixed debug passed/rc=0，5.506 秒。最终含三者、Post/Delete 与 Sem/Mbox/Queue
  PendAbort 的联合完整依赖检查 passed/rc=0，353.609 秒，无诊断。期间仅修复标准库
  nth_indep 的实参匹配和弃用别名，不改变语义前提。五个本批临时检查脚本已移除，
  保留构建缓存；未新增公理/Admitted，未改 C/generated/旧 manual/controller 或历史
  acceptance。当前接口仍绑定八行 UChar profile；wider/Multi、入口身份、Save/Restore、
  输出存活期和完整调用组合仍须完成，不能记为两个 C 函数或全库模型已验证。
  其余全库模型与最后旧证明迁移继续保留在完整目标中。

- Sem Accept/Set/Post 的 native 组合增量（2026-09-10）：新增共享 `lib/sem.v` 与
  `sem/spec/sem_accept_spec.v`、`sem_set_spec.v`、`sem_post_spec.v`。SemFields 继续由
  Event 持有，不增加 Sem map、计数 ghost 或其他内核状态字段。共同 setter 只改变
  count；原值/末次写入、增减范围、payload/native Event 保持都有对应证明。字段拆合
  实例化现有 Event/QCP FieldStorage，native image 恰只更新 EventCntField；原值和
  写后 merge 分开，不丢 type/ptr/wait/name/padding。
  新的全局 payload 运输桥消费 Event owner 已证明的新模块不变式，再运输现有跨模块
  关系；不要求调用者假设一个新 whole-global invariant。单 Event 写后合回保留完整
  Task/Sched/其他配置模块，Queue storage 通过其真实 Event 索引运输。Sem 专用 merge
  消费实际写后的 UShort count cell，不能从 pure count update 产生堆资源。
  Accept 按旧计数返回，只有正数才减一；Set 保留 count-first/bitmap-second 分支，
  不加入源程序没有的 waiter guard。INT16U 新计数范围来自参数类型；perr 在临界区
  先写 NONE，拒绝时再写 TASK_WAITING，端点错误码是 perr 观察而非 C 的 void 返回。
  Post 保留 NULL/ENTER trace/type/Save 的有序前缀，优先复用 Event 的 bitmap/table
  单 waiter 唤醒，参数为 NULL/PendSem/PendOK；只有无 waiter 才增一或报 SEM_OVF。
  已证明三个临界区端点的存在性、确定性、全局有效性、相关错误帧及 invocation 保持；
  Post 另有精确所选 waiter/后态、完整 residual 运输和真实 TCB/ready/ECB 写后合回。
  wake 的调度位只表示后续调用 OS_Sched，不宣称任务一定新变 ready 或原调用已返回。
  检查：共享 Sem fixed debug passed/rc=0，3.46 秒；global 全文件 fixed debug
  passed/rc=0，22.209 秒；三个 spec 联合 fixed debug passed/rc=0，5.599 秒。
  最终含共享依赖、Event wake 与三个 spec 的联合完整检查 passed/rc=0，317.348 秒，
  无诊断。期间修复 record 析构次序、分离合取结合形状和跨模块显式 import，未改
  theorem 语义前提。四个本批临时检查脚本已移除，保留构建缓存；未新增公理/Admitted，
  未改 C/generated/旧 manual/controller 或历史 acceptance。旧 `lib/sem_*_spec.v`
  留待最终迁移，完整入口/trace/Save/Restore、perr 资源、调度续体、Multi/其他配置和
  其余操作族仍待完成；上述结果不是三个 C 函数已重新验证，更不是全库模型完成。

- Sem Pend 与公共返回清理增量（2026-09-10）：新增
  `sem/spec/sem_pend_spec.v`，核对 os_sem.c:321--402，分开 safety/参数/trace/type/ISR/
  lock 观察、首个临界区和调度后的返回临界区。立即路径复用 Sem count 减一；等待路径
  复用 Event 的 Stat/StatPend/Dly 准备与登记，保留实际 TCB generation。源代码不存在的
  guard 不放入 transformer；非 idle、原调用身份与返回 current/ready 由调用协议承担。
  返回保留 OK/ABORT/TO/default 的精确 perr 观察。timeout 使用共同 reference closure/
  backlink 定理取得 live Event 和登记后 Remove；OK/abort 不读旧 Sem，可在 Delete 回收
  后继续。立即取得的 perr 在 Restore 后写入，返回 switch 的 perr 在 Restore 前写入，
  不把 C 的 void 返回改成错误码返回，也不假定 OS_Sched 必定返回。
  Task 的公共 `task_event_pend_cleanup` 与完整 layout image 按真实源码族选择 Msg 是否
  清空：Sem 保持，Queue 清空；均不写 Dly/ready/cache。该参数不是新的 OS 字段或运行时
  guard，实际 image 保留 Stat/StatPend/EventPtr/条件 Multi/可选 Msg 写入顺序。原 Queue
  接口的 statement 保留，其保持性转用共同 Task/cross/global 证明；超时引用查找也提取
  为共同定理，没有另建 TCB、Sem map、等待枚举或通用分离逻辑库。
  两段的存在性、确定性、全局有效性及 invocation 保持均已证明；返回另有完整 TCB 端点、
  Msg/Dly 帧、无超时时 Event 帧及 scheduler-boundary 条件下的组合。资源重组消费实际
  写后的 TCB/ECB，运输未改 Scheduler 字节、Event 的 Task 编码下标与完整其他模块
  residual，不由纯端点生成堆资源。首段沿用公共 count 与 Event pend 的写后合回接口。
  检查：完整 Task fixed debug passed/rc=0，11.036 秒（仅已有弃用记号警告）；共享
  Task/cross/global 完整依赖检查 passed/rc=0，280.82 秒，无诊断。SemPend 与当前
  QueuePend 联合 fixed debug passed/rc=0，6.046 秒；最终包含两者、Sem Accept/Set/Post
  和共享依赖的完整联合检查 passed/rc=0，333.531 秒，无诊断。局部调试只修复 eauto
  选择 TCB 实参及共享封装后的显式展开，不改变 theorem 的语义前提。
  三个本批临时检查脚本已移除，构建缓存保留。未新增公理/Admitted，未改 C/generated/
  旧 manual/controller 或历史 acceptance。证据属于 standalone model development；
  完整入口/trace/平台/Save/Restore、perr 存活资源、跨调度干扰和恢复、Multi-enabled
  全局实例与 Sem 其余操作族仍待组合，不等于 OSSemPend C 函数或全库模型已验证。
  旧成果迁移仍按用户要求留在全部模型完成之后。后续 SemCreate/Del 已核对源码，可复用
  既有 Event 私有初始化/发布/回收和 abort 广播接口，尚未将它们记为已完成组合。

- Sem/Mbox Delete 与共享 Event 回收增量（2026-09-10）：逐分支核对 os_sem.c 的
  OSSemDel 和 os_mbox.c 的 OSMboxDel，新增 `event/spec/event_delete_spec.v`，两模块的
  `spec/*_delete_spec.v` 仅绑定真实 Event type 与 Pend mask。共同前缀保留 safety、IEC
  runtime、参数、ENTER trace、type、ISR、Save 的顺序；Queue 的四个前缀定义转用共同
  观察，原 QCB/buffer 删除主体不变，Mutex owner/PCP 删除不套入该 ECB-only 模型。
  NO_PEND 有 waiter 时保留原句柄/TASK_WAITING 与状态；ALWAYS 每轮按当前位图选择并
  执行真实 NULL/PendAbort wake，随后按 Type/Ptr/Cnt/free-root 源序回收。未知 opt 返回
  INVALID_OPT，成功返回 NULL；是否请求 OS_Sched 取循环前的 tasks_waiting。perr、trace
  与调度返回均留在 Restore 后组合，不承诺新 ready 数或原 invocation 一定恢复执行。
  Sem 清 count、Mbox 覆盖 message pointer 都不代表释放应用资源或调用 free。
  Queue owner 新增 `queue_storage_event_entry_frame`，通过现有 QCP store_map
  split/merge/missing 规则证明无 Queue payload 的 Event 项插入、替换、移除保持全部
  QCB/buffer 与 private Queue 归属。没有重复实现分离逻辑 map 或新增 OS 状态字段。
  `non_queue_event_has_no_queue_fields` 属于 Event owner，由现有字段一致性和类型给出
  payload 事实；删除模型不新增公有前提或不存在的 runtime guard。全局回收保持性用
  既有 backlink/reference closure 加空 wait list 排除残留 TCB 引用，资源重组消费真实
  Type/Ptr/Cnt/free-root 写后堆，保留其他 ECB、Queue 和完整其他模块 residual。
  共同删除主体的存在性、确定性、错误帧、成功移除、精确 abort waiter、原 invocation、
  调度请求 iff、全局有效性与完整写后资源重组均有证明。无 Queue 字段由已检查的 Event
  不变式推出；完整资源规则不会悄悄丢掉 Queue 的额外 owner。
  检查：Queue 完整文件 fixed debug passed/rc=0，9.659 秒；共享 Queue/global 完整
  依赖检查 passed/rc=0，280.884 秒，无诊断。后增 Event 字段投影引理与 Sem/Mbox/Queue
  Delete、Sem/Queue Pend 由最终联合完整依赖检查覆盖：passed/rc=0，341.818 秒，无
  诊断。局部调试只修正 map 拆分后目标谓词的精确重写与 Event ID 实参，不改变语义前提。
  三个本批临时检查脚本已移除，构建缓存保留；未执行的共享 spec Load 脚本不计调试证据。
  未新增公理/Admitted，未改 C/generated/旧 manual/controller 或历史 acceptance。
  当前证据为 names-disabled native 模型；完整 names/Multi、入口/平台/trace、perr
  存活资源和调度返回、其他操作族及全库旧证明迁移均未完成，不能记为两个 C 函数已验证。

- Sem/Mbox Create 与 Event 发布增量（2026-09-10）：核对 os_sem.c:102--140、
  os_mbox.c:98--136 及 OS_EventWaitListInit:1310--1320，新增共同
  `event/spec/event_create_spec.v` 和两模块的 `spec/*_create_spec.v`。IEC/ISR 入口观察、
  Save 内 free-pop、Restore 后逐字段私有初始化和最终发布分别建模，不把整个 Create
  当成原子操作。源码没有 lock 拒绝或 perr；字段顺序为 Type/Cnt/Ptr/条件 Name，再
  Grp 与八行 UChar table。Sem 保留实际 INT16U count、NULL pointer；Mbox count=0，
  初始消息允许 NULL，沿用 canonical message 编码，不拥有或释放应用消息内容。
  复用现有 Event 生命周期、`event_private_write` 和 QCP FieldStorage；未增加
  OS 状态字段或复制另一套 map/array 分离逻辑库。Event owner 新增等待表 prefix、
  已写行观察、未写字段 frame 与真实 UChar 写后合回，明确不是 OS_MemClr。分配/私有
  写序列的存在性、确定性、全局有效性、invocation/origin/generation/QCB 关联保持、
  源序 image 对应与公有 Event/Queue/Task/Sched 帧均已证明；从全局 partition 推出
  初始化后仍是 private、既不在 used map 也不在 free list。纯序列不产生物理字节，
  每个 store 的空间规则单独消费实际新 cell 和原 field residual。
  全局 free-pop 将实际 ECB image 交给本次调用，同时保留其余模块资源；private store
  运输共享 frame；发布消费完成初始化的 ECB，保持全部 QCB/buffer，要求本 allocation
  没有额外占用 QCB（由真实摘取与私有写入保持性得到，不是新增公有 runtime guard）。
  Event 等待关系由旧 reference closure 推出 unpublished slot 无 live TCB 引用，再
  接入新空 waiter Event；跨模块层将 Mutex/table 运输提取共享，原更新/删除接口的
  statement 保持，不向调用者要求假设一个新的 whole-global invariant。
  修正发布资源接口对不可见字段的过强要求：按 `event_fields false` 中实际
  字段比较 image，不要求关闭名称功能时初始化不存在的 Name 单元。所有真实 padding
  仍取实际 allocation bytes 并保持；record 的未观察 Name=0 不代表执行过该 store。
  原 exact-image Queue 接口通过新 field-extensional 规则派生，未弱化实际堆覆盖。
  检查：Event wait 全文件 fixed debug passed/rc=0，3.267 秒；Event pool 全文件
  fixed debug passed/rc=0，5.078 秒；共同 Create spec fixed debug passed/rc=0，
  3.482 秒；当前 Mbox 库全文件 fixed debug passed/rc=0，3.472 秒。最终联合完整
  依赖检查覆盖 SemCreate/MboxCreate、Sem/Mbox/Queue Delete、Sem/Queue Pend 及共享
  图，passed/rc=0，371.46 秒，无诊断。调试修复显式 import、`value` 构造子冲突、
  归纳实参和 record/padding 展开；Mbox 旧 .vo 的依赖不一致由固定检查刷新，未改
  其库证明。单独 bindings Load 的整体失败不记为 passed，最终联合检查才是完整证据。
  六个本批临时脚本已移除，保留构建缓存；未新增公理/Admitted，未改 C/generated/
  旧 manual/controller 或历史 acceptance，没有提交。证据属于 standalone model
  development，不等于两个 C 函数或全库模型完成。当前完整调用的 Save/Restore、
  non-owner 干扰、trace/实际公开 handle 时刻、名称资源和其他配置仍待组合。
  该阶段定位的下一接口工作：`KernelClientCertificate` 当时只 frame Task creation，须
  补 Event/QCB private 资源的真实保持；Event 与 Task 的 invocation 计数器不是同一
  名字空间，必须结合已有 origin 与实际动作连接，不能直接按 nat 相等混用。
  旧证明迁移继续留在全部模型完成之后，完整目标中的其他操作族与模块仍保留。

- Event/QCB 环境保护与 QueueCreate 生命周期增量（2026-09-10）：
  `KernelClientAction` 分开 Task actor 与 Event allocator actor，均为动作参数而非新增
  OS 状态字段。Event owner 从既有 private map 按 invocation 取视图，frame 保留完整
  allocation 的 origin/generation、ECB image 与 QCB 关联；QCB image 由调用者局部
  提供，buffer 使用普通分离 frame。两个 storage 等式仅用于重接资源谓词，不代替
  C/ISR/callback 的物理空间足迹证明，也不产生内存资源。
  `KernelClientCertificate` 增加 Event frame；原 Task 创建和 Suspend/Resume 接入，
  统一 `kernel_client_resource_trace` 增加可选 Event observer。旧 Task-only trace
  是 None 的接口并保留原运输定理签名，不另建第二个执行关系。两个 nat 名字空间不混用；
  stopped 仍表示 Task 续体终止，不能据此宣称创建者的私有资源已自动回收。
  共同 Event 分配、私有字段写入和发布、Sem/Mbox 发布，以及 Queue 的二次分配/发布
  均有 action certificate。它们不是全部内核操作的来源嵌入或统一环境实例。
  `queue/spec/q_create_lifecycle_spec.v` 与历史 QCreate 切片分开，复用第一次 ECB pop
  后的同一 allocation；通过环境 frame 推出第二次 Save 后仍可访问它。第二次临界区
  观察当时的 QCB free list：成功摘 QCB 后恢复中断再初始化，耗尽则只写 ECB Ptr/root，
  将 ECB 接到当前 free list，不还原先前全局快照，不回退新分配的身份计数器。
  回滚保持证明实际需要 UNUSED 类型；它由原 free-storage 有效性、第一次摘取和完整
  allocation frame 给出，未增加公开函数前提或源代码不存在的 type 检查。action 还绑定
  实际 pool partition 和 no-QCB 阶段，不能任意声称其他调用的私有 QCB 是 free。
  成功初始化复用 `qcb_initialize` 六次源序写入及共同 ECB 私有写序列；发布消费
  实际完成的 ECB/QCB、原 caller buffer 和更新后的 free list，建立全局关系及空间表示。
  保留 OSQPtr 和未使用槽位（允许未初始化值），空 FIFO/零容量仍可表示；正基址、INT16U
  范围和实际区间/地址运算条件不伪装成 C runtime guard。资源组合只使用 QCP map、
  字段和 sepcon 单调性；修复结合形状/定理实参问题时未弱化目标。
  检查：Event pool 的完整 fixed debug passed/rc=0，4.942 秒；共同 Event Create
  完整依赖检查 passed/rc=0，288.208 秒。后增 UNUSED 来源引理已在后续依赖检查中
  编译；Queue 生命周期完整 fixed debug passed/rc=0，5.077 秒。
  最终完整依赖检查联合覆盖 Event/Sem/Mbox Create、Queue 创建生命周期、Suspend/Resume
  及共享模型图：passed/rc=0，339.082 秒，无诊断。早期缺少 compiled import、Mbox
  缓存依赖不一致及 --no-deps 拒绝均未记为 passed；本次联合检查已刷新相应依赖。
  另行检查 TCBInit 模型消费者时发现此前 Task 重构的适配遗漏：旧 eventMultiPtr/status
  record 和 common/full-layout image 混用。已同步逻辑等待序列名称、零 status、未观察
  Multi 指针的处理，并用既有 `tcb_layout_update_common` 和配置化 slot storage
  接入私有初始化。该文件整体尚未通过，当前首诊断为 `task_tcb_init_detached_state`
  仍将 TCBCommonImage 传给需要 TCBLayoutImage 的 detach；后续取得/发布及
  64-byte 空间接口还需统一适配。局部声明加载不等于 TCBInit 全文件通过或旧证明验收。
  本批不改 C/generated/旧 manual/controller/历史 acceptance，不提交；整调用的
  Save/Restore、trace、真实 actor/公开时刻、配置增量、其余环境操作族和全库模型仍未完成。
  旧函数的整体证明迁移继续留在全部模型完成之后，不能以本批成功缩小全目标。
  四个 Event/Queue 临时检查入口已清理，构建缓存保留；未完成的 TCBInit 布局适配
  保留其专用 fixed debug 入口，后续从当前首诊断继续，不重证已通过的无关模型。

- TCBInit 完整布局消费者适配（2026-09-10）：修复上一批记录的 common/full-layout
  类型遗漏，`task_tcb_init_spec.v` 的 detach、重新取得、私有 image 同步、commit node
  与返回观察均使用同一 `TCBLayoutImage`。公共字段数学保留为明确的 profile
  切片；完整 initializer 复用 `tcb_layout_update_common`，按 Multi 配置增加
  源码 EventPtr 之后的两次 NULL store。源序 fold 与独立 pointwise image 对应已证明，
  关闭 Multi 时未观察项被保留，不假称写入了不存在的 cell。FlagsRdy 来自既有 free
  reuse closure，padding 保留实际分配字节；未增加 OS 状态字段或另建 TCB image map。
  free-root、active-head、Prev 更新与 priority-table 插入统一为配置化 slot/link；旧 head
  和新节点的 map 拆合使用 `used_task_rep`。全局发布不再从公共字段切片凭空补出
  完整节点。实际布局字段上的相等通过已有 QCP 字段-map 单调性接回空间表示，关闭功能
  时不要求不存在字段的全函数等式。retained/written partition、写前只遗忘覆盖字段、
  写后合回均复用现有 QCP-backed FieldStorage，不复制分离逻辑库。
  检查：完整文件 fixed debug passed/rc=0，30.932 秒；随后以该 spec 为 target 的唯一
  完整依赖 fixed check passed/rc=0，325.103 秒，无诊断。前期的字段枚举 tactic、
  Prev cell 展开和命名空间解析错误已修复，不作为通过记录。最终源文件在检查期间未改动。
  本批布局及源序写入层证明 Multi 开/关，其他 scalar feature 仍取现有 native profile；
  全局保持仍使用 selected profile，不把它外推为完整 Multi 等待/环境实例。旧 common
  hook 数学接口不替代完整配置的 hook ownership/调用组合，ARM/BSP 与整调用返回边界
  仍保持显式未完成。未改 C/generated/旧 manual/controller/历史 acceptance，没有提交。
  已完整重核 TaskCreate/Ext 源码：两者共享 priority reservation/TCBInit failure rollback，
  基本版传零扩展参数，Ext 传真实参数并有条件清栈；这是下一组消费者，不记为已实现。
  本批专用 Load 调试入口已清理，构建缓存保留。其余操作族、配置、环境/平台、全库模型
  和随后全部旧函数证明迁移继续属于原目标，未因本批通过缩小范围。

- TaskCreate/CreateExt 及清栈接口（2026-09-11，本批检查通过）：Task invocation 注册、priority
  reserve/rollback 的模块、跨模块及全局保持接口已接入；抽出 Task 公共资源中除 priority
  table 外的真实 residual，优先级 cell 的原值/更新合回复用 QCP PtrArray。TCBInit 的
  map-Zrange 更新数学引理移到已有 array_abstraction，两个旧局部副本删除并同步引用，
  未另建数组库。array_abstraction 完整 fixed debug passed/rc=0，3.561 秒；全局 inv 文件修复
  编码展开后的 fixed debug passed/rc=0，22.969 秒。失败的早期集成检查不计为通过。
  新 Create/CreateExt 接口保留源序 guard、真实基本/扩展参数、条件清栈、默认 trace 参数
  不求值及 trace 后 fresh running 读取。caller origin 绑定当前 Task/generation；预留
  分支接到 TCBInit entry，0/66 使用公共错误码编码，失败回滚消费实际零值 cell 与当前
  residual，并运输原 invocation continuation。清栈使用真实 CHK/CLR 顺序和 size--
  后的写零/后增，复用现有 copy-prefix/UIntArray.mixed_full 处理旧值或 undef 后缀。
  检查：Create 参数接口修复局部 let 展开后完整文件 fixed debug passed/rc=0，3.192 秒；
  四个新文件的精确声明在去除批内 Require 的临时合并诊断中 passed/rc=0，5.754 秒。
  后者只用于集中修复导入/列表转换问题，不替代独立模块检查。最终通过
  `.coq_debug/task_create_complete_interfaces.v` 导入原始独立文件，以固定工具执行完整
  依赖检查 passed/rc=0，349.572 秒，无诊断；覆盖四个新增 spec、迁移公共引理后的
  TCBInit 及共享依赖，检查期间 formal 文件冻结。未新增 admission/axiom。
  本批是模型/接口证明，不是四个 C 函数的 canonical VC 或 ARM/BSP 验证完成。
  当前仍是 selected native profile；平台 Save/token/Restore、栈/trace/schedule 的完整
  调用嵌入、其余配置/模块和全部旧函数证明迁移均未从原目标删除。本批未改 C/generated/
  旧 manual/controller 或历史 acceptance，没有提交。
  下一步栈调用/生命周期连接已从实际 ARMv7-A StackInit 核对：opt 被忽略，VFP链接
  实例决定16/50/82字帧；失败保留初始化后的buffer，成功须在首次发布前转交栈资源。
  Basic的零bottom/size不是实际extent。后续已实现 TaskStackLease、创建/存活绑定、
  QCP 完整-buffer park/take/switch 与 TCB saved-SP 拆合；不能再将其列为未实现。
  运行/发布/回收调用协议及 Flag/Multi 借出片段的资源组合仍待完成；具体边界见 design。
  这些接口不是 ARM/BSP 执行证明。临时合并/Load副本清理，
  保留联合导入入口和可复用构建缓存。

- 历史字段袋与接口命名整理（2026-09-12，88 模型统一依赖检查通过）：已审计 57 个 record，
  将 `TaskNativeFields/taskNative` 的
  13 个字段直接并入 `TaskAbstractState`；将 `EventNativeFields/eventNative` 的 5 个字段
  直接并入 `OSEventAbstractState`，使用 `eventName` 与 `eventPadding1/2/3/19`；将
  `KernelGlobalAddresses/kernelGlobals` 的 22 个地址直接并入 `StableGlobVars`。
  专用字段袋 updater/helper 和旧类型/投影 alias 已删除，lib/spec 消费者按所属对象直接读写。
  `KernelConfiguration`、raw image 与 live state 的对应关系、private allocation、lifecycle 和借用协议保留，
  没有因平铺削减资源、字段或有效性义务。全模型 Native/native 标识符按真实职责归义，
  当前全局、历史 verification slice、固定 TCB 视图与配置布局、内核动作与平台资源各自分名，
  不统一替换为 Raw，也不保留旧名 alias；源码 API/字段原名保留。
  已删除 Event 有效性的两级兼容别名，直接使用 `verification_slice_event_in_range`；
  当前 Event 生命周期仍使用独立的 `event_in_range`。未使用的 `UCOS2_inv_for_task_profile`
  dispatcher 和 `mbox_initial` 已删除；全局 Task map residual 的重复引理合并为
  `UCOS2_task_sched_residual_task_map_frame`，Queue 历史切片接口也显式加上 `verification_slice_`。
  `TaskMemoryProfile` 及仅为它存在的地址分派、Event 编码分派和桥接引理也已删除；
  `tcb64_addr` 直接定义固定布局地址，配置化的 `task_slot_addr` 不变。
  源码核对发现 `tcb64_configuration` 曾遗漏 `OS_MAX_FLAGS > 0`：`ucos_ii.h` 的
  FlagNode/FlagsRdy 条件同时要求 Flag 开启且容量为正。现已补齐 `0 < cfgMaxFlags`，
  当前选定值仍为 5；此修复限制错误布局实例，不改变所选 C 配置或实现。
  进一步删除 TCBInit 开头无人调用的旧 projection/observation 家族，共 3 个定义和 6 个引理；
  真实源码参数、字段写集合、初始化/发布与 hook 契约保留。Tick 的非 timeout 字段保持引理
  已平铺原 13 字段嵌组、补齐 `curPrio`，三个跨模块消费者按实际所需事实提取，不再依赖旧袋位置。
  waiting single backlink 的旧定义及两个 bundle 中的重复约束已删除，全部 lib/spec 消费者已适配。
  静态布局接口已将 core、条件模块、TaskReg 和所选 idle/stat/timer 系统栈区间合入
  `selected_kernel_global_regions`，由 `valid_selected_kernel_global_layout` 约束范围与不重叠。
  原 `selected_task_profile` 已改名 `selected_kernel_profile`，由 `UCOS2_inv` 的全局有效性层
  统一持有；真正的 TCB 条件仍为 `tcb64_configuration`。系统栈区间是纯布局事实，栈字节仍由
  caller/task/platform 的实际资源接口持有，不在全局表示中重复分离合取。
  `stable_glob_vars.v` 全文件已通过固定 debug Load（rc=0，0.442 秒）；44 个 `g_*` 地址
  在完整区间表中各出现一次，当前 IEC 关闭配置实际启用 43 段。
  `UCOS2_timer_unlink_preserves_validity` 已删除可由 profile 导出的额外单池 layout 前提。
  模型/spec 中 profile 名称已同步，相关消费者已由本批完整集成检查覆盖。
  第五份旧名映射 `.coq_debug/model_static_interface_cleanup.json` 已落盘，仅用于迁移定位，
  不作为证明通过证据。
  本批字段袋与接口清理的完整模型集成已通过：实际固定独立模块检查 rc=0，
  `first_diagnostic=null`、`dependency_errors=[]`。从入口解析到 88 个唯一当前 lib/spec 文件；
  检查后逐字节确认这些文件和入口均与构建副本一致。剔除嵌套注释与字符串后的扫描中，
  `Native`/`native` 标识符残留为空，实际 `Admitted`、`Axiom`、`Parameter` 亦为空。
  扫描结论限于这 88 个文件，不是对依赖库或既定平台/工具信任边界的无假设声明。
  `task_tcb64_image` 的 `let n := t` 局部同义别名已在此次检查前删除，定义含义不变。
  本次统一检查覆盖完整 Task/栈/全局/QueueCreate 与 Mutex/Sem 模块，不再仅有较早的
  focused 或独立 Load 结果；其中 MutexDel 已去除旧私有 helper 依赖并补入 `event_wait` import。
  MutexDel 的公开 abort 效果未弱化，三个内部成功效果引理的 Event 有效性从入口不变式推出，
  不把“只清 Mutex 位”改成清全部 pending。SemPend 六条状态/等待证明保持 statement，
  三处旧私有 helper 替换已覆盖；SemDel 四处 Interrupt 重组和 MutexRdyAtPrio 等待类型
  分类也已集成。MutexPost 的六模块 frame、wake 桥接、内部 reserved 有效性修复已覆盖，
  更强结论对应 `mutex_post_disinherit_crit_rel__handover_commit`，无旧名引用或文件外签名消费者。
  全局不变式只读复审未发现此次展平遗漏资源连接；历史 verification slice 有不同语义，并非冗余别名。
  工具超时 bytes 输出捕获已修复，相关 mock 测试 24 项通过；这不改变超时策略或 formal 验收。
  本结果只完成字段袋与接口清理优先批次，不表示全部 API 模型剩余语义组合已完成，
  也不表示受影响旧 generated/manual 已迁移或旧 VC 已通过验收；原目标的其余工作继续。
  本轮同步了 `OS_TCBInit` / `OSMutex_Priority`，并新增 `OSMutexPend` / `OSSemQuery` 的
  C annotation 接口名称同步；非 annotation 的 C 字节经精确比较保持不变，没有修改实现。
  旧 manual/generated 尚未迁移，不能把名称适配记为旧证明通过。
  后续 TCBInit 迁移已定位 4 个 image 参数类型差异和 9 个 `free_image` binder：
  完整 `TCBLayoutImage` 用于摘取/发布状态，固定 64 字节接口显式接收其公共字段投影。
  当前 annotation 只同步名称，尚未实施这项类型迁移；Mutex Priority 的 Extern 签名则已对应。
  此记录不改写历史验收，也不将原栈调用/生命周期批次或整个目标改记为完成；其余模型及
  最终旧证明迁移仍按原范围继续。

- 栈发布与切换资源组合（2026-09-12，本批固定检查通过）：复用现有 TaskStackLease、
  QCP UIntArray 和 store_map，没有新增 record 或 generation/owner 账本。
  `task_stack.v` 新增 `parked_stacks_consistent` 及空集合、frame、park/take、commit 保持接口；
  entry 绑定既有 publication history，只有当前 slot/generation 匹配时才要求 saved-SP 对应。
  已退休 generation 可继续保留真实缓冲区；新 key 为 None 是空间转交前提，不从 used=None
  冒推出，也不添加 C guard。`task_context.v` 将实际写后的 SP cell、TCB residual 与
  outgoing park/incoming take 合成一个资源定理，另证 SP 更新及 park→take 的登记一致性。
  OSTCBCur 在该资源步骤中保留原值；目的选择、cache 更新、register restore 和 hook
  仍由实际平台/调用协议承接。共新增 10 条模型引理；`task_create_stack_protected_commit_resources`
  已接入同一 published parked-map 接口，消费当前初始化 buffer，不在成功返回时再交出同一份栈。
  检查入口 `.coq_debug/task_stack_protocol_check.v` 通过原始独立模块导入，固定工具
  `check` 返回 passed/rc=0，384.775 秒，`first_diagnostic=null`、`dependency_errors=[]`。
  检查后已逐字节确认三个改动模型、直接消费者 task_stack_check_spec 和入口均与构建副本一致；
  三个改动文件无实际 Admitted/Axiom/Parameter 声明。首次检查的结合形状错误已修复，
  不将该失败记为通过；没有重跑旧 generated/manual 或改写历史验收。
  本批仅覆盖完整-buffer 子接口，不能把 Flag 节点已借出时的栈再次整体放进全局不变式。
  Flag/Multi residual、完整 Save/Restore/创建发布/退休调用协议、其余模块操作和旧证明迁移
  仍在原目标范围内。实际 ARMv7-A 的三种 VFP 链接版本、异步中断 SP 对齐和自删除后
  free-TCB SP 写入边界已按本地源码复核，不宣称证明了 ARM/BSP 指令执行。

- Flag 栈节点字节借还（2026-09-12，本批固定检查通过）：新增 `flag_stack.v`，
  不新建 record、数组库或 owner/generation 账本。当前 ABI 下 8/16/32-bit Flag 的
  20/20/24 字节节点分别对应 5/5/6 个 UInt 字；`kernel_resources.v` 的 6 条薄类型桥接
  复用 QCP typed-cell/byte 规则。通用 `task_stack_array_split_app` 已从 Create spec
  移到 `task_stack.v`，原消费者同步；新增两段真实 residual 及 split/merge，借出位置
  不再被整栈的 None 单元重复占有。借出只得到未初始化节点字段；归还消耗当前完整节点
  和原 residual，保留四个 pointer 字以及 32-bit 配置的独立 flags 字，尾字只遗忘值。
  `flag_stack.v` 全文件 fixed debug Load 通过（rc=0，14.561 秒），随后
  `.coq_debug/flag_stack_protocol_check.v` 的原始独立模块 check 通过（rc=0，
  402.638 秒，`first_diagnostic=null`、`dependency_errors=[]`）。该入口还导入
  task_context、Create 栈规约及 StackCheck 消费者；检查后 6 个当前模型/spec 与入口
  均和构建副本逐字节相等，去注释/字符串扫描无实际 Admitted/Axiom/Parameter 声明。
  早期 debug 的展开顺序、数值化简与纯事实/空间结合诊断均已在最终版本中修复；
  被拒绝的 no-deps 尝试不计作检查通过，没有绕过依赖信任检查。
  源码时序也已复核：OS_FlagBlock 先写 TCB backlink，再进行六次 node store，必须在
  backlink 前完成资源借出；Del/Post 的 unlink 后 Next 读取完成前，节点不能归还任务。
  实际 &node 的 provenance、invocation 续体、完整 Task/Sched/Flag 联合保持、停放栈
  片段表/全局资源分区仍需继续，不把字节桥或原版 abort 路径记为整函数已验证。
  后续 FlagBlock 新规约单独检查，其候选不混入本批结论；未修改 C 实现、未迁移旧 VC。
  本批另做了只读编译成本诊断：当前工具只允许 21 个精确 lib owner 入口复用项目模型
  缓存；新 `.coq_debug` 入口、Flag spec 及 task_storage/task_stack/task_context 不在表中。
  因而重复依赖编译来自缓存资格策略，并非已发现 source/toolchain/provenance 漂移。
  现有 metadata 的相关条目相同，未重新 hash、未修改策略或用不覆盖新文件的入口替代检查。
  当前仍以 fixed debug 缩短局部迭代，集中运行必要的完整检查。

- 停放片段归入 Task 与全局不变式（2026-09-12，本批集成检查通过）：复用既有
  `TaskStackRegion`/lease，将片段/map 类型置于 TaskStateDef，在 Glob_TaskAbstractState
  直接增加实际资源索引 `parkedTaskStacks`，不新增遗漏字段袋或第二套对象身份。
  `UCOS2_inv` 及各 focused residual 恰好拥有一次停放资源，专用 parked residual 排除它。
  片段表示直接使用 QCP mixed_seg/iter_sepcon；完整 buffer 特化保留 region.words 端点，
  Flag residual 省略空段和已借出中段，返回合并的是当前节点字节，不是旧中段 image。
  Create/context 新端点回写实际 Task map，退休 generation 的缓冲区不随 slot 回收被删除。
  同时补齐既有 generation closure 中真实的 private-unpublished 性质：detach 用新代次，
  commit 清除本 reservation 后记录 publication；其他私有槽由池分区唯一性保护。
  `task.v` 完整 check 已通过（rc=0，108.275 秒）；task_stack/global/context/flag_stack
  整文件 fixed debug Load 分别通过（3.988/25.444/6.156/14.892 秒）。全局 residual 索引
  frame 和完整 buffer 等价的两个 proof 适配错误已修复，不把失败版本记为通过。
  统一入口 `.coq_debug/model_stack_fragments_check.v` 导入当前全部 90 个唯一 lib/spec，
  覆盖 TaskDelete 的五处保持证明及 TCBInit/Create 消费者，固定完整 check 通过
  （rc=0，1161.452 秒，first_diagnostic=null，dependency_errors=[]）。检查后 90 个
  源文件与入口共 91 份字节均与构建副本精确相同，无 Native/native 标识符残留，
  无实际 Admitted/admit/Axiom/Parameter 声明和行尾空白。已有 AUXLib.Axioms import
  仍属工具依赖，不能把模块名误当新增公理声明，也不将本批结果扩大为依赖库无假设。
  仅删除本批四个临时 Load 脚本，保留完整检查入口；未修改历史验收或旧 VC。
  这仍不证明 Create/context 完整全局合回、所有 Task 的可恢复栈覆盖、实际 &node/
  invocation 绑定、保存帧/恢复执行或 Flag/Multi 的完整借还协议，也未迁移旧 manual/VC。

- 纯状态不变式命名整理（2026-09-12）：原 validity_bundle 三项名称统一为
  `UCOS2_state_inv`、`UCOS2_state_inv_with_ready`、`UCOS2_verification_slice_state_inv`。
  33 个当前模型/spec 与 7 个 C annotation 文件仅替换标识符，已用修改前字节逐份反向
  替换比较确认；定义内容、证明体结构及非 annotation 的 C 字节不变。2 份当前设计文档
  同步说明名称含义；没有旧名兼容别名。历史 generated/manual 和冻结验收产物不原地改写，
  后续随原计划的证明迁移消费新名称。此前 90 文件检查仍是前一批的证据。本次以
  `ucos2_verify_inv.v` 为目标的固定检查已通过（rc=0，294.961 秒，
  `first_diagnostic=null`、`dependency_errors=[]`），只覆盖该入口及实际依赖；
  缺少编译依赖而失败的早期 debug 不记作通过，也不据此宣称所有旧 VC 已迁移。

- 完整空间层与统一局部化（2026-09-12，本批固定集成检查通过）：新增 `lib/ucos2_spatial.v`，
  将唯一 `UCOS2_raw_rep` 整理为 12 个实际共享资源 owner 的完整分离合取，Task 同时拥有
  公共存储及登记的 parked stacks；复用原有物理表示，不增删纯不变式约束。
  通用缺一/缺二及拆合、更新合回接口支持全部模块组合，缺二拆分显式要求 owner 不同。
  Interrupt、Flag、Memory、Timer、Event/Queue 的独立 residual 列表被统一接口取代，
  `UCOS2_core_rep` 删除；只拆 Task 公共存储的接口明确使用 `task_storage` 名称。
  20 份现有模型/spec 文件完成接口引用迁移；历史 generated/manual、冻结报告及 C 实现
  均未改写。缺一/缺二有双向拆合、逐 owner 的 frame、更新合回及缺二交换/重复选择等式；
  完整 Task 拆分与仅公共存储拆分、仅 parked-stack 拆分之间有已证连接。
  纯状态不变式正文与修改前一致；Interrupt/Tick 表示内的原有范围约束也保留。
  `.coq_debug/model_spatial_check.v` 导入 91 份唯一当前模型/spec，完整固定 check 通过
  （rc=0，1192.125 秒，`first_diagnostic=null`、`dependency_errors=[]`）。检查后这 91 份
  源文件及入口共 92 份字节均与构建副本相同，活动模型/spec 中无旧模块 residual 名称。
  本批新增声明没有 Admitted/admit/Axiom/Parameter；沿用的工具/平台信任边界不变。
  通用判等展开、左结合重组、Event 清理投影展开及五处显式 import 问题均已修正并被
  上述完整检查覆盖。保留集成入口，清理本批三个临时调试脚本。
  此结果完成空间层与接口整理，不是所有 OS 函数、历史 VC 迁移或 controller 验收完成。

- FlagBlock 联合端点（2026-09-12，本批固定检查通过）：新增模块归属的
  `VC/code_proof/flag/spec/flag_block_spec.v`，3 个操作定义和 15 条引理，复用
  Task prepare-wait/条件 backlink、Scheduler remove-ready 和既有 Flag node 插入。
  已证明精确状态字 OR/OK/delay、common-field image、实际 current lookup、非目标模块/
  scheduler cache/Task lifecycle frame，以及明确的 Task/Sched/Flag 三模块有效性。
  TaskDelete 关闭时不虚构 backlink 写入；模型 lookup 的 None 不是新增 C guard。
  整文件 fixed debug Load 通过（rc=0，2.692 秒），随后以原始 spec 为目标的完整
  check 通过（rc=0，144.453 秒，`first_diagnostic=null`、`dependency_errors=[]`）。
  最终文件与构建副本逐字节相等，15 条均为 Qed，无 record 或实际 Admitted/Axiom/Parameter；
  首次检查的缺 import 和局部 let 展开诊断均已修正。只删本批临时调试脚本，保留
  Flag 栈联合导入入口及可复用构建产物，没有修改工具缓存策略或 C/generated/manual。
  三模块有效性不等于完整 UCOS2 跨模块不变式；实际六次 node store、ready/TCB 的
  空间资源重组、原调用身份和完整 Pend/平台续体仍继续实施。

- 首批历史函数迁移的依赖审查（2026-09-12）：`sem_accept-20260912193435` 的
  source-only annotation 审查已收集四类独立缺口：锁外类型字节的真实空间所有权、
  published handle 跨获取临界区的存活、按源码顺序组合的公开调用语义、平台资源接口归属。
  owner 未修改 formal 文件、未运行 QCP/Rocq；controller 已将该审查封存为 blocked，
  不是 SemAccept 新版本证明失败后的重复重跑，也不是整个模型/迁移目标停止。
  旧六个 VC 的 acceptance 仍只属于旧版本。`OS_TCBInit` 已有完整调用接口，故在
  `task_tcb_init-20260912200208` 中先迁移其完整布局类型与 annotation；该新轮次尚未
  完成当前 C/VC 验收，不能继承历史十九个 VC 的通过结论。其登记共享依赖在迁移期间
  保持稳定，SemAccept 的未决公开句柄协议不作为 TCBInit 的前置条件。

- 共享平台接口归属及 SemAccept 临界区操作（2026-09-12）：将
  `InterruptPlatformResources`、`armv7a_irq_fiq_mask`、`interrupt_saved_value`、
  `save_token` 的原定义从 TCBInit spec 移至 `lib/interrupt.v`；原 spec 重导出该模块，
  不保留重复定义或旧别名。定义正文和外部 CPU/BSP 契约含义不变，不新增架构实现证明。
  以当前 `task_tcb_init_spec.v` 为入口的固定完整 check 通过（rc=0，344.272 秒，
  `first_diagnostic=null`、`dependency_errors=[]`），范围为该入口及其实际依赖，
  不代表重新检查全部 91 份模型/spec 或历史 TCBInit manual。
  当前 SemAccept spec 新增实际 ARG_CHK-on profile 约束、受保护计数操作的
  `sem_accept_critical_client` 及其已证 certificate，覆盖完整状态有效性、原调用身份及
  Task/Event 私有创建资源 frame；不改变全局配置不变式。该 spec 整文件 fixed debug
  Load 通过（rc=0，3.370 秒），不是 SemAccept 整函数/controller acceptance。
  上述三个 formal 文件与相应已检查构建副本的字节仍相同；不为本记录重新计算摘要或
  重编译。锁外读取的物理资源借还和公开对象生命周期仍须证明，不能用仅有计数保持性
  的 certificate 代替它们。
  后续在 SemAccept spec 补齐三条函数级证明：返回计数的 UShort 范围、计数操作保持
  已发布事件的代次/类型、非目标事件的完整 map entry 不变。完整 spec 的 fixed debug
  Load 通过（rc=0，3.515 秒）；此前一处状态更新展开不足已修复。它们允许计数真实变化，
  不把环境冻成状态相等，也不宣称所有环境操作已满足公开句柄存活协议。该增量未修改
  TCBInit 登记依赖；SemAccept 仍未完成整函数迁移。

- TCBInit 首批历史证明直接迁移（2026-09-12）：当前 C annotation 的四个完整布局签名和
  九个 free-image binder 已接入 `TCBLayoutImage`，仅在固定 64-byte 空间接口投影 common
  image。整个 C 预处理结果与迁移前逐字节相同；本批未修改实现、case spec 或共享模型。
  复用原 19 个 manual 的证明结构，适配现行名称、地址配置桥和完整/公共字段表示；逐目标
  重放全部通过，正式 manual 只有当前 19 个 witness 的 Qed，无旧 native 声明或 admission。
  在全新隔离输出中按当前 C 独立 canonical symexec，通过并保留四组 strategy-correctness
  接口；规范化得到 19 个 manual targets 和 17 个非 target diagnostics。新 goal 与调试
  候选精确相同；auto、diagnostics、snapshot 和 goal-check 与 main 原字节相同，按 no-op 保留。
  当前完整 `task_tcb_init_goal_check.v` 的固定检查通过（rc=0，518.875 秒，无首诊断或
  dependency error），目标/auto/manual/check/spec 与已检查副本一致。证据为
  `worktrees/_model_builds/task-sched-mutex/tool_evidence/check-7pbr720h.json`；直接迁移记录与
  迁移前七份文件保存在 `.coq_debug/task_tcb_init_migration/`。
  完整接口覆盖 52 个函数义务，其中 19 个 manual 已证，33 个 canonical auto 仍沿用原有
  工具信任边界，不能称为 52 个无假设 kernel proofs。所选源码修复变体、配置及 CPU/BSP
  外部契约不变。原 annotation 会话已无活动 handle，pending 报告及其工作树保留不改；
  本结果是已获授权的直接迁移，不是该 controller run 的 accepted/done。其余模型和历史
  证明迁移目标继续，未被本函数完成替代。

- QInit 当前模型连接（2026-09-12）：在 `queue/spec/q_init_spec.v` 追加四条已证连接，
  从精确零字段节点推导通用空闲节点，再提升到空闲链、`queue_init_post` 和
  `queue_storage_rep sg (event_pool_initial sg)`。复用 QCP 既有值遗忘和分离合取规则，
  未增加状态字段、公理或额外前提，也未弱化原 `OS_QInit_spec`。
  四条新增证明体按项目 proof-text 规则改用既有 `sep_apply_l_atomic` / `entailer!`
  等允许接口，声明不变。当前完整 `q_init_goal_check.v` 固定检查通过
  （rc=0，213.438 秒，无首诊断或依赖错误），证据为
  `worktrees/_model_builds/task-sched-mutex/tool_evidence/check-ht0qv3h8.json`。
  goal/auto/manual/check/spec 与已检查构建副本逐字节一致；11 个 manual 全部 Qed，
  8 个 auto 义务仍保留原工具信任边界。本批未改 C、原规格定义或 generated/manual 文件，
  不重做符号执行、不改旧 controller acceptance；不是 19 个无假设 kernel proofs。
  该连接只建立 Queue-owned storage，不建立 Event 堆或启动后的完整全局不变式；
  `OS_MemClr` 的 C 验证现已完成（见下）；其字节规约到 QInit 专用 callee
  契约的完整调用连接仍是独立待办。

- 内部函数驱动的新批次（2026-09-12）：按用户新目标启动 `OS_MemClr` 和
  `OS_EventWaitListInit` 两个独立 controller run，分别为
  `mem_clr-20260912221131`、`event_wait_list_init-20260912221131`。
  新 standalone C 的函数体与绑定上游去注释后的代码一致；Event 使用当前八行 UChar、
  names-disabled 布局。owner 仅可修改各自 C annotation/case_lib，现有共享模型只读。
  它们先证明精确字节/等待表写入与资源 frame，再接入代表性的初始化/创建调用者；
  不能用模型 lemma、已声明的 callee contract 或启动会话代替实际 C/VC 验收。
  后续批次保留模块初始化、Event Remove/Wait/Rdy、调度/中断/tick 及 Flag/Timer 的实际
  内部依赖；不以两个基础函数完成代替用户全目标。可复用经验写入现有 skills，
  同批独立 VC 缺口聚合后统一修复，不添加另一套强制验收表。
  首次实际反馈：MemClr 的原 `*pdest++ = (INT8U)0` 被 QCP 拒绝，annotation 候选仅拆为
  旧地址写零和局部指针递增；上游原版保留在绑定源码中，不声称已有通用编译器 refinement。
  其 r1 annotation 由 controller 接受，进入 proving 前以 r2 补齐该候选实际使用的
  四份只读 UCOS2 规则依赖，
  不修改共享模型，不把登记补全当成语义 blocker。EventWaitListInit 的 full-image
  consequence 如使用额外 `event.v` 布局桥，同样须先补齐实际依赖绑定。
  main 同时在 `.coq_debug/core_init_byte_views.v` 检查九条候选字节/typed-view 连接，
  覆盖零字节对/四元组到 UShort、UInt、Ptr，以及 QCP 长度 2/4 的零数组实例；
  并将其组合到完整的 24 字节 QCB 和当前四节点、96 字节的 Queue 表。
  反向调用前连接把未初始化 QCB/整个表转换成 QCP undefined-byte 数组，同时保留原
  类型化存储给出的对齐条件。当前完整候选的 fixed debug 通过
  （rc=0，22.150 秒，`debug-g7ehcot_.json`）。其中 UInt 四字节零值连接直接复用
  `SimpleC.SL.StoreAux.store_uint_store_char`；没有重复实现已有打包库。
  候选尚未合入共享库，也尚未完成已证 MemClr C 与 QInit 专用 callee 契约的完整组合：
  末次指针递增要求最终地址仍可表示，
  仅拥有最后一个字节或 `kernel_region_valid` 的半开区间上界不足以自动给出该事实。
  此调用边界仍需单独核实；不改变正在证明的共享依赖、不弱化旧 public contract，
  也不把该局部检查当作新函数完成。
  随后在同一候选追加 QInit→generic MemClr 的资源前置和返回资源→`q_init_after_clear`
  两条连接，显式保留空闲根 cell 和对齐。完整 11 条候选 fixed debug 通过
  （rc=0，22.878 秒，`debug-5yugeash.json`）。这两条只证明资源 consequence，
  不声称由旧 QInit 前提推出未决的游标最终地址界。

- MemClr 实际 C 验证完成（2026-09-12）：上述 run 的 4 个 manual targets 全部 Qed，
  controller 独立 group-check、parent full check、final apply 和 final-check 均通过，
  最终状态为 `done`。当前 main 已应用该候选；所有权精确覆盖 `size` 个字节，
  包含 `size = 0`，后置为全零数组，未修改资源由分离 frame 保留。
  原 `*pdest++` 的 frontend 等价拆写和 ILP32 地址上界如实保留在契约/报告中。
  完整接口另有 3 个 canonical auto admission，仍属既定工具信任边界；
  不是 7 个无假设 Rocq kernel proofs。权威结果见
  `reports/mem_clr-20260912221131/run_logs.json` 的最终 state snapshot，
  不为本进度记录重编译、重算摘要或变更历史验收。

- EventWaitListInit 实际 C 验证完成（2026-09-13）：4 个 manual targets 全部 Qed；
  controller 独立 group-check、parent full check、final apply 和 final-check 均通过，
  `event_wait_list_init-20260912221131` 最终状态为 `done`，候选已应用 main。
  源码保持原写入次序，只清零 group 和八个等待表字节；case_lib 的 full-image
  split/updated-merge 保留 Type/Ptr/Cnt、padding 和未写字段。末次正式编辑后的
  combined fixed debug 覆盖四个 proofs，完整 group-check 委托 controller，
  没有把旧 worker check 冒充最终版本验收。10 个 canonical auto admission 仍属
  工具信任边界，不称为 14 个无假设 kernel proofs，也不建立已发布事件或全局不变式。
  权威结果见该 run 的 `run_logs.json` 最终 state snapshot；本记录未重复编译。

- 下一批 InitRdyList（2026-09-13）：新 run `init_rdy_list-20260913011224` 已启动
  独立 annotation owner，当前尚未完成函数验证。独立源码和组合要求见
  `config/core-initializers-v2.93.01.md`；已有 `sched_boot` / `sched_raw_rep` 为只读依赖，
  不因写零就假定整个调度器初态已成立。新增 controller 精确模块路由的相关测试
  31 项通过；不更改 Event/MemClr 已完成 run 的验收状态。
  同批 `init_tcb_list-20260913012100` 与 `init_event_list-20260913012101` 已分别启动
  独立 annotation owner，共用已验证的 generic MemClr 字节契约并保持共享模型只读。
  新增两项精确模块路由后相关测试为 33 项通过；三个 main intake 的上游执行 token
  和选定 ILP32 布局诊断通过，尚不代表这三份函数已完成 VC 证明。
  InitRdyList 的 r1 annotation 已由 controller 接受，四个当前 manual targets
  已完成独立全量分诊，均为 L7 proof gap；分诊由 controller 接受后按一个 coherent
  group 开始实际证明。TCB/Event 初始化的 r1 annotation 同样已接受，分别为八个/
  七个 manual targets，正在独立全量分诊；这三份函数均未提前计为 `done`。
  全局数组注解的元素步长与 typedef-array `sizeof` 前端处理经验已写入既有
  `annotation-filling/docs/array-string-guide.md`，不改源码访问或冻结 handoff。
  等待/唤醒批次的 Remove/Wait/Rdy 三份 main intake 已完成上游执行 token、完整
  TCB/ECB 声明和实际 bitmap offset 的 ILP32 只读诊断；所选 trace 默认为空，
  不声称覆盖自定义 trace 或 EventMulti。新增三项模块内 case-lib 路由后相关测试
  36 项通过，未变更验收逻辑。Rdy 将消费 Remove 的实际已证接口，不把旧调用声明
  作为 callee 实现证明，也不要求 Remove 接收已恢复的全局不变式。
  TCB/Event 的全量分诊随后均由 controller 接受：TCB 为两个独立组（字节重组、
  链接与根发布），Event 为一个组。Remove 的新 run
  `event_task_remove-20260913020326` 已启动独立 annotation owner，保持这些 run
  的共享依赖只读。Event preparing 曾因 os-sync 路由只识别 Flag 名而未识别
  `OS_InitEventList` 失败；已按实际源码身份补齐 ECB helper 路由，13 项相关测试及
  skill 校验通过，同一 accepted plan 的 preparing 现已成功，不重做 annotation。
  两份未分配 worker 的部分工作树保留在该 proving container 的
  `partial_unassigned_event_boot_storage*` 目录；没有已证成果被覆盖或删除。
  `os-sync-module` 已明确 ECB 与独立 Flag group 的区别，不把 ANY/ALL/consume
  强加给等待表 helper，也不凭 proof hint 选择 primitive。

- InitRdyList 实际 C 验证完成（2026-09-13）：4 个 manual targets 全部 Qed；
  controller fresh group-check、parent full check、final apply 和 final-check 均通过，
  `init_rdy_list-20260913011224` 已为 `done`，成果应用到 main。精确覆盖六个 global
  cell/array 地址处的写零操作，不修改 C 实现，也不假定已有完整调度器不变式。
  `init_rdy_list_spec.v` 的六条既有 case-local helper 支持数组前缀重组和 boot
  consequence；group 未增加 helper。10 个 canonical auto admission 仍属既定
  工具信任边界，不称为 14 个无假设 kernel proofs。
  boot consequence 所需的 OSCtxSwCtr/OSRunning 零值来自更早的 `OS_InitMisc`；
  已补入该真实依赖的 main C intake，保留两个 volatile RAM 声明、static linkage
  和全部十一处写入。上游 token/标量别名/ILP32 只读诊断通过，新增路由后相关
  controller 测试 37 项通过；InitMisc 尚未开始正式 run，不把源码诊断当作证明。
  TCB/Event 初始化与 Remove 工作继续，后三者均未因本函数完成而被缩减或计为 done。

- InitTCBList 实际 C 验证完成（2026-09-13）：
  `init_tcb_list-20260913012100` 的 8 个 manual targets 全部 Qed，两个 group 的
  controller fresh check、deterministic parent full check、final apply 与 final-check
  均通过，最终 state 为 `done`，8 个正式文件已应用 main。已接受 annotation 的
  完整函数执行 token 和 TCB 声明与选定上游再次对应，未修改 C 实现。
  证明实际连接两次 generic MemClr 调用：1408 个零字节重建为 22 个完整 64-byte TCB，
  256 个零字节重建为 64 项 PTFree 优先级表；随后安装 Next、默认名称和两个根。
  非链接/名称字段及 padding 的零值均保留，GlobalStrings 和无关资源保持为 frame。
  23 个当前 group suffix helper 已合并，复用现有 QCP 字节/数组和 Task 字段存储接口，
  未新增 TCB record 或修改共享模型。另有 23 个 canonical auto admission 属于既定
  工具信任边界，不称为 31 个无假设 kernel proofs；也不声称完整 OSInit、BSP 或
  运行态全局不变式已证明。Task boot 的 count/register 零值仍由 InitMisc 的调用者帧提供。
  原 QInit 的 MemClr 最终游标地址界仍是独立未决调用契约问题，不被这个新规约掩盖。
  当前 Event 初始化已进入 7-target proof group；Remove 的 annotation 与 3-target
  全量 VC 分诊均 accepted，实际证明组已启动。`event_task_wait-20260913025852`
  已启动独立 annotation owner；`sched_new-20260913024634` 的 annotation 已 accepted，
  5 个 manual targets 待全量 VC 分诊，保留只写 high-priority byte、旧 TCB pointer 不变
  和空位图结果零的源码边界。
  SchedNew source/layout 诊断及 38 项相关路由测试通过。实际 import 可见性与 NoDup
  搜索成本经验已反馈到 group-worker-proving / os-performance-optimization，两个
  skill 校验通过；这不改变冻结 handoff 或新增验收步骤。

- Event 内部函数及真实调用链推进（2026-09-13）：
  `init_event_list-20260913012101` 的 7 个 manual targets 与
  `event_task_remove-20260913020326` 的 3 个 manual targets 全部 Qed；各自
  controller fresh group-check、parent full check、final apply 和 final-check
  均通过，两个 run 已为 `done`，成果已应用 main。Event 初始化重用已证 MemClr，
  将 200 个清零字节重建为十个完整 ECB，再链接空闲链并发布根；保留 padding 和
  未改字段，不声称 Queue 初始化或运行态全局不变式。其执行 token/static linkage
  与上游一致，ECB 声明仅需明确折叠所选八行常量并展开 INT8U 别名；无需修改正式源码。
  Remove 仅更新一个事件等待行、条件更新 group 并清除 TCB event pointer，两个返回
  分支均覆盖，调用前不要求 Rdy 尚未恢复的 pending/status 不变式。完整执行 token、
  TCB/ECB 声明和六个标量别名与选定上游对应；未修改 C 实现、共享模型或其他已证成果。
  Event group 增加十个后缀 helper，Remove group 不增加 helper。两函数分别仍有
  12/3 个 canonical auto admission，属既定工具信任边界，不能计为无假设 kernel proofs。
  `event_task_rdy-20260913034227` 已启动实际 caller annotation，十五个只读依赖中
  包含刚最终应用的 Remove spec；将核对位图选中任务、priority-table owner、更新后
  suspension 分支及 Remove 调用，并返回原选中优先级，不把未证声明当作 callee 证明。
  Wait annotation 已 accepted，三个 manual targets 正在全量 VC 分诊；SchedNew
  annotation/五目标分诊均 accepted，单 proof group 运行中。InitMisc 的新 run
  `init_misc-20260913032206` 保留 volatile 和十一处实际写零，annotation、canonical
  QCP、case-lib check、smoke 均通过，唯一 return target 待分诊/证明；提供 task/scheduler
  零标量 framing，但不虚构未写 OSCPUUsage 的零值。QInit 旧 MemClr 末地址界、整体
  OSInit、上层等待/唤醒与平台实现证明仍未由这一批结果覆盖。

- 选择与等待辅助函数完成，进入实际调用者（2026-09-13）：
  `sched_new-20260913024634` 的 5 个 manual targets 与
  `event_task_wait-20260913025852` 的 3 个 manual targets 全部 Qed；两个 run
  的 controller group/parent check、final apply、final-check 均通过并为 `done`。
  SchedNew 证明实际查表与最高优先级字节写入，保留空位图结果零和旧 high TCB
  pointer；Wait 证明实际九个 protected cells 的事件插入、ready 清除及原 current
  身份，保留调用者已准备的 status/delay 等字段。两组均无新增 helper，没有改共享
  模型或 C 实现。各有 5/1 个 canonical auto admission，仍在既定工具信任边界。
  InitMisc 唯一手工目标也已 Qed，worker/controller group-check、parent check、
  final apply/final-check 均通过并为 `done`；该 case 没有 canonical auto admission。
  Rdy annotation 和 17-target/11-shape 全量分诊已 accepted，没有 L0-L6 缺口。
  两个独立组为 selection/table 十目标与 updates/Remove 七目标；七目标组已返回
  completed，全部 Qed，69.697 秒最终组合调试通过，无新增 helper/import，case_lib
  和未分配 blocks 不变。十目标组也全部 Qed，9.749 秒组合调试与 controller fresh
  复查通过，无新增 helper/import。Rdy 的 17/17 已通过 parent 合并、final apply 和
  final-check，run 正式 `done`；当前目标、共享依赖、隔离 symexec freshness 和所有
  结构/禁用扫描通过。应用后的完整函数/TCB/ECB/六个别名与上游对应；保留 28 个
  canonical auto admission 的既定工具信任边界。连同随后完成的 Sched、FlagInit 和
  Timer Alloc/Free/Unlink、IntExit 及 TimeTick，本批累计十七个函数 done、132 个 manual targets，不宣称整体 OSInit、
  全局保持或 ARM/BSP 实现已证。
  `sched-20260913042243` 的 annotation 与十目标/八形状分诊已接受，31 个只读依赖包含已完成的
  SchedNew spec；完整 Save/Restore、switch hook、Task/stack 和原 invocation
  边界已写入完整 caller 的外部契约候选，未把 masked-prefix 模型当成整个函数已证。
  全部十个手工证明已有最终组合调试通过（31.07 秒），case_lib 未变且无新增 helper，
  controller fresh review、parent 合并、final apply/final-check 均通过，run 已 `done`；
  保留十个 canonical auto admission 与显式平台/回调契约边界。一次报告字段 completed/passed 不匹配由 owner
  如实修正，未修改或重编译 formal 源。完整 case-lib 和生成接口检查通过；唯一 parser 适配是 opaque tag 的前置声明，
  root 复核目标函数/四个别名与源码不变，删去仅此三个声明 token 后全预处理流与原 intake 相同。
  `OSIntExit` 独立源码 intake 与所选端口宏、别名及 ILP32 诊断对应；新 run
  `int_exit-20260913065528` 的完整 annotation 已获 controller 接受，32 个精确只读
  依赖包含最终应用的 Sched/SchedNew spec；canonical、case-lib、生成接口与源码/布局
  检查通过，独立 `int_exit-vc-checking-r1` 已完成全部 11 个 manual targets 的分诊。
  另有 15 个 canonical auto admission，不计手工证明。普通返回与独立资源显式的
  exception transfer 分开；已证局部保持/重组不替代外部汇编、hook 和非局部资源交接
  契约。未添加共享字段或改 C 算法，也未虚构 OS_Sched callee。
  后续全部十一目标/七形状静态分诊发现一项 case-local proof-policy 修复：种子
  os_int_exit_prefix_cells_merge 有六处直接调用禁表中的两个名称；并非 C/规格/模型
  语义缺口。完整分诊后统一反馈，controller 已创建 annotation r2；owner 仅修复
  该引理证明体，不改结论、C 实现或规约，root 不原地改 accepted seed。r2 修复和
  新版本十一目标/八形状全量分诊现均已接受，全部为 L7；完整调用路径的唯一
  int_exit_full_call 组已完成全部十一证明，最终组合调试通过，无新增 helper/import
  或 case-lib 改动；controller fresh review、parent 检查、final apply/final-check
  均通过，run 正式 done，精确覆盖 11/11。当前目标/共享依赖/隔离新鲜度及结构扫描
  通过，保留十五个 auto admission 与显式平台控制转移契约，不扩大为 ARM/BSP 已证。
  annotation-checking 已补充对同一 canonical 禁表的早期读取/扫描；未删禁表或
  parent/final gate，其他 live owners 在原 attempt 内提前处理相同问题。
  `flag_init-20260913043225` 的 annotation 已获 controller 接受；新 Flag intake 与上游完整
  执行 token、group 声明和四个标量别名一致，诊断确认 16-byte group、80-byte pool
  与 0/4/8/12 字段偏移。case-lib 的双向字节转换和 exact post → flag_initial/flag_inv
  已检查通过，保留 357 个原 C token 与十个只读依赖。八目标全量分诊随后发现四个
  目标共享一个 case-local 字段地址词汇缺口：既有 layout 约束 field_address，而实际
  generated arrow cell 使用 CNotation.eval_addr_expr；其他四个为 L7。controller
  已登记完整反馈并创建 annotation r2，owner 仅更正四个实际 ABI 绑定。新 annotation
  和八目标/六形状全量分诊均获接受，已无上游缺口。八个手工证明均 Qed，六个后缀
  helper 已证；controller fresh review、parent 合并、final apply/final-check 均通过，
  run 为最终 `done`，精确覆盖 8/8 manual targets；保留十九个 canonical auto admission。
  应用后的源码/完整结构/别名及 ILP32 诊断通过。未新增公理、共享
  写权限或 C 修改，旧 acceptance 不转移。
  实际端口源码促使架构 skill 明确区分任务级保存 continuation 与中断级使用已保存
  任务帧；创建 hook 为空不代表 switch hook 为空。文档结构/链接检查通过；当前
  Python 缺 PyYAML，未伪报 quick_validate 成功。没有修改 live handoff 或接受状态。
  IRQ 参考也已裁剪为按真实入口/栈帧/返回路径核对，去掉所有 IRQ 必为
  OutsideCritical、可变 nesting 值是稳定环境、普通 RAM 模拟 MMIO 等笼统模板。
  相对链接和 scoped whitespace 检查通过，不为文档改动重证既有函数。
  Timer 的真实 `OSTmr_Alloc`/`OSTmr_Free` 两个静态函数已准备源码 intake，完整
  结构、callback typedef、函数签名/执行 token 和 40-byte ILP32 布局诊断通过。
  Timer 路由的测试 selection 为 37 passed；两个独立 run
  `tmr_alloc-20260913045648`、`tmr_free-20260913045648` 已登记九个实际只读依赖，
  Alloc annotation 已接受：canonical QCP、fixed case_lib/export 检查通过，实际
  callback typedef 和函数体保留，只补 QCP 所需 opaque-tag 前置声明。两侧 framed
  consequence、16 位计数的模运算与 private 转移已 Qed，三个 manual targets 全部
  完成证明；controller fresh review、parent 合并、final apply/final-check 均通过，
  run 为最终 `done`，精确覆盖 3/3 manual targets，无新增 group helper。应用后的
  完整源码/结构/callback typedef/别名及 ILP32 诊断通过；八个 auto admission 不计为
  手工证明。Free annotation 与三目标全量分诊已接受，raw/valid-pool 两层规约及恢复
  后果检查通过，无上游修复项；三个手工目标全 Qed，无新增 helper/import 或 case-lib
  修改。controller fresh review、parent 合并、final apply/final-check 均通过，run
  已 `done`，精确覆盖 3/3；五个 canonical auto admission 保留既定信任边界。应用后
  完整静态函数、结构、callback typedef、别名和 GCC ILP32 诊断均与固定源码对应。
  分配是 private storage 转移而非发布；回收保留 Type/Delay/padding、不代做 Unlink。
  新增实际 `OSTmr_Unlink` intake 和独立 run `tmr_unlink-20260913073058`，九个只读
  依赖、annotation owner 已启动；完整源码/两结构/callback typedef/别名及 ILP32
  诊断通过，spoke 为 8 字节、七项表为 56 字节，模块路由 36 项相关测试通过。
  它检验真实 head/non-head 与邻居写入、STOPPED 和 16 位 Entries 更新，尚未宣称
  函数证明完成。完整 Delete 源码确认运行态先 Unlink 后 Free，停止/完成态直接 Free。
  Timer skill 据此补充 private/发布/摘链/回收边界及回调游标 footprint；不扩 live
  handoff 权限，不以模块不变式保持冒充任意遍历稳定，scoped whitespace 检查通过。
  Unlink 完整 raw/configured annotation 已 accepted，十二个 case-lib 引理、固定检查、
  生成接口和禁表扫描通过；独立 vc-checking-r1 已完成全部十个 manual targets 的
  分诊，另有二十三个 canonical auto admission 保留既定工具边界。分诊发现 r1
  虽传递了 spoke 大小事实，但绑定的是 sizeof_struct_type，实际目标使用
  sizeof_alias_type；两种字段定义也把实际 FET_alias 误绑为 FET_struct。
  GCC 布局一致不能推出这些独立 Coq 参数相等。controller 已创建 annotation r2，
  集中修复两项 case-local 词汇绑定，保留数值布局、完整资源和 C 实现，无共享写入。
  r2 annotation 与新版本十目标全量分诊现均已接受；raw 九目标与 configured
  consequence 一目标相互独立。raw 全部九个证明完成且无新 helper/import；configured
  目标及十二个后缀 helper 完成，两处直接禁表调用修复后只接受最终合规字节。
  两组 controller fresh review、parent 合并检查、final apply/final-check 均通过，
  run 正式 done，精确覆盖 10/10 manual targets，保留二十三个 auto admission 的
  既定工具边界。当前目标/共享依赖/隔离 symexec freshness 与结构扫描均通过；
  C 实现及所选 ABI 未变、没有新增共享字段，不扩大为整个 Timer Delete 的证明。
  相应教训已写入 os-state-abstraction。VC-checking skill 增补：空 pure
  alternative 不代表空间地址转换已验证，使用完整分支/已有 bridge 覆盖真实转换，
  不手改 canonical 目标或另造 targets。
  `OSTimeTick` 已准备 tick 模块源码 intake，完整执行 token、TCB/八个别名与所选
  upstream 对应，ILP32 字段布局及 volatile 类型诊断通过；新增路由后的测试为
  38 passed。保留全部 step cases、逐 TCB critical interval、超时仍链接的 Event/Flag
  阶段和真实 tick hook；新 run `time_tick-20260913062313` 已登记三十个精确只读依赖，
  独立 annotation owner 已开始，没有 annotation/证明 acceptance。端口 hook 会调用应用 hook、递增独立
  OSTmrCtr 并周期性调用 OSTmrSignal，不能因 trace defaults 为空便将它视作空调用。
  Tick r1 已完成时钟/step、逐 task 与 scan、完整纯不变式/TCB merge 和私有 16 位
  计数后果，最终版本绑定 case-lib check 通过；C 未改、VC 未生成。完整 source-only
  反馈仅请求两个已有只读规约 sem_post_spec/event_wake_spec，并保留 hook/游标存活/
  mask 外读取/ISR 与 task 返回等组合义务。controller 审查后创建 annotation r2，
  三十二个只读依赖、无共享写权限，候选引理保留但不继承验收。
  为此新增“首次生成前仅登记只读依赖”的最小 controller 路线，40 项相关测试通过，
  补充的 3 项接受状态/路径检查也通过；旧 input/report 不改，漂移和写入扩权仍拒绝。
  新 owner 已完成完整 C annotation 的 canonical 生成：97 个接口义务、31 个 manual
  targets，当前版本 case-lib 检查和 owner 全目标审查通过，controller 已接受 r2，
  独立 time_tick-vc-checking-r1 已完成全部目标分诊，统一返回生成 goal 的 import
  闭包及五条正 delay 路径覆写前旧 UInt 范围丢失这两类问题。r3 仅修 C annotation，
  显式导入已登记依赖并在真实旧单元仍存在时保留范围；31 targets、实现、公开规约、
  case_lib 和共享模型不变。canonical、固定 case-lib 与实际新 goal export smoke
  已通过，controller 已接受 r3。临时线程限制解除后，独立 checking r2 已在
  全新 owner 会话完成；未以原 annotation 作者替代独立审查，也不计为 manual 证明。
  本次完整三十一目标及 unsigned 覆写审查确认 r3 修复，并定位唯一剩余根因：
  partial_solve_wit_5_pure 在时钟递增前拆分处丢失旧 OSTime 非负事实。旧值 -2
  反驳的是被削弱的 VC 前提，不是真实 UInt 起始状态；运输已有下界即可建立
  unsigned wrap 与 Z.rem 的等式。delay/step/status/ready/hook 私有计数路径均已
  核对，完整反馈已由 controller 审查并创建 annotation r4。新 owner 已作两行
  C annotation 修改，一次 canonical 生成保留 31 targets，缺失事实已进入相关
  pure 两分支及写后检查点；case_lib/共享模型/实现/公开规约不变。固定 case-lib
  与实际新 goal export smoke 已通过，controller 已接受 r4。新独立 checking r3
  已完成 31 targets / 17 shapes 的全量分诊，无新增语义缺口，固定 interface check
  与 diagnostics 通过，分组报告已 accepted。time_tick-vc-proving-r1 的 clock/step
  12 个、traversal/return 12 个、task update/backedge 7 个目标已由三个隔离 worker
  并行启动，组间无依赖。三组均已通过 controller fresh review，Tick 当前
  group-accepted 为 31/31；确定性 parent merge、整函数检查、final apply 和
  final-check 均已通过，8 个正式文件应用 main，run 于 2026-09-13 12:56:45（UTC+8）
  首次 done。终检确认隔离 canonical symexec 新鲜度、当前共享依赖/candidate 对应、
  case_lib/结构/禁表扫描和固定 Rocq 检查通过。66 个 canonical auto
  admissions 不计为 manual 证明。已在 annotation-checking 的既有旧值范围
  条目补充按全部相关写点审查及区分所需非负条件/位宽上界，未新增验收阶段。
  显式支持 IRQ/FIQ 已屏蔽、nesting 非零的已打开 ISR region，应用 hook
  保留独立资源工作及有序 semaphore posts，并非任意内核写回调或无屏蔽并发扫描。
  running idle-tail 从既有全局不变式导出，不新增公开前提；未将 canonical
  critical-prefix 模型虚报为完整 SemPost/Signal C 或平台实现证明。
  Sched 的实际 QCP 诊断也促使 annotation skill 增加不完整类型前置声明适配提示；
  不引入虚构字段/布局，不声称全 C projection 未变，不修改 live handoff。
  QInit 旧地址末界、完整 OSInit、Timer 其余函数证明和 ARM/BSP 实现仍未由本批结果覆盖。

### 生成前 source/model intake 要求（设计阶段记录）

这是全模块模型的生成前 source/model 审查，不是重证旧 Delete，也不把新增所有 C 函数
一次塞入一个 VC run。保留既有目标 C、case_lib、共享 formal 和生成产物原字节；
不用 symexec/coqc 再次证明已知旧候选不闭合。根据当前实际源码/配置/模型，完成：

- 覆盖上述各源码单元的 public/internal/条件函数，特别核对 caller-supplied storage、
  callback、系统任务、statistics/volatile、Flag 栈节点、Memory 块归还、Timer wheel/Sem。
  新模块正文需要完整理解，未完整读过的函数不能仅凭名称标记已审查。
- 将现有九类 Mutex/Task/Queue 诊断作为精确只读导航；仅复核对本次全内核结构选择有影响
  的部分，勿重新建立已存在的 TCB/Queue/位图模型或读取历史 proof archive。
- 提出一种统一的全状态/配置/生命周期组织，列出所有 source fields/global resources 的
  owner，说明模块 invariant、局部化、保持性和 critical client 的最小接口及真实来源。
  对“现有共享文件改动”与“新建模块文件”分别列出精确路径和消费者，禁止把后者伪报
  为输入中已登记的只读依赖；path 请求不是写授权。
- 区分源码实现反例、合法中间阶段欠建模、公开使用协议、工具表达限制和纯证明接口缺口。
  不随意修补新发现的 C 实现；保留具体输入/路径/读写证据后，由 main 按用户已经授予的
  真实语义需要改进权限选择最小修复变体，原版与修复版分开绑定，不再逐项等待用户确认。
- 在 owner result 中如实填写 skill routing 的实际读取、整族事实寿命/退出需求和反例挑战。
  已发现缺口时 precheck 不伪造 passed；source-only blocked/terminal 和 `not-run` 的工具
  记录与可验收 annotation 明确区分。保留 controller 自有 envelope，使用当前报告字段。

该历史轮次的产物是完整缺口与设计批次；当前实施及模型/受影响接口证明按用户最新要求
直接完成，不再等待后继 handoff，也不能以只读审查结束整个用户任务。
该 intake 的职责仍以原冻结 input 为准，本次文档重组不追溯改变它的权限、验收字段或输入字节。
