# uC/OS-II V2.93.01 抽象 Coq 模型详细设计

本文件落实 [全模块范围与组织要求](ucos2-v2.93.01-model-foundation.md)，同时保留设计接口与
已实施增量。设计中的 record、谓词和引理签名不自动代表已经实现或证明；实际实现与检查
范围以各节说明和该范围文档的实施记录为准，不构成 Coq/controller 验收。
现有可复用定义保持其 owner；接口名按当前模型的实际语义整理，新增/扩展接口按用户授权直接实施，不由 controller
控制本次模型开发。必要的实际证明检查仍保留，历史 C case 验收结论不改变。

设计状态：**设计完成，实施/证明进行中；全库模型尚未完成**（2026-09-10）。覆盖全部模块状态、资源及配置增量、
跨模块关系、接口签名和 [126 个原始函数的映射](ucos2-v2.93.01-model-api-map.md)，另列两个
修复变体 helper。已核对源码定义与43个头文件 `OS_EXT` 全局声明；这只是设计覆盖检查，
不等于126个函数已验证或所有拟定不变式已证明可保持。

2026-09-12 起按 [当前实施次序](ucos2-v2.93.01-model-foundation.md) 分批推进：相关模型
接口稳定后即迁移历史函数，以实际 annotation/VC 检验模型；全模块完善继续进行，但不再
统一阻挡所有迁移。每批先补所依赖的已知语义缺口，新增约束按实际 writer 补保持证明，
未改模块经已证 frame 保留。历史章节的检查结论不变，旧“全模型完成后迁移”的排程已取代。

## 1. 版本、配置与语义口径

基线是绑定的 V2.93.01 `Source/ucos_ii.h` 与 `Source/os_*.c`，32-bit little-endian ABI，
当前 [os_cfg.h](queue-v2.93.01-first-round/os_cfg.h) / [app_cfg.h](queue-v2.93.01-first-round/app_cfg.h)。
Task publication、Mutex priority 的已批准源码变体单独绑定；原版中存在的反例不因模型调整而消失。
设计阶段未改 C、旧 profile 或重证旧函数。现在按用户授权实施模型及必要的独立源码修复变体；
不修改已冻结的原版/历史证据，也不以模型弱化掩盖实现差异。

### 1.1 配置 record 的扩展

继续以 `StableGlobVars` 提供固定地址/容量，不在其中保存运行时值。将以下数据形成配置接口，
可先作为现有 record 的有归属字段族，避免为每个配置宏新建一个模块：

| 字段族 | 当前实例 | 必须约束的关系 |
|---|---|---|
| 优先级与位图 | lowest=63，priority word=8 bits，ready/event table=8 项 | 窄配置 `x=p mod 8, y=p/8`；wide 配置用 16；idle 允许占 63，普通 API 和 PCP 的 guard 分别编码。 |
| 池容量 | Event=10、QCB=4、Task=20+2、Flag=5、Memory partition=5、Timer=16 | 有限合法索引、所有池的真实字节区间、各模块分区守恒；不能只用不同基址代替不重叠证明。 |
| 时间 | kernel tick=100 Hz、timer signal nominal=10 Hz、wheel=7 | 两个时间域分开；本内核没有在 `OSTimeTick` 内自动调用 `OSTmrSignal`。频率对应依赖实际外部调用/port hook 实例。 |
| 系统任务 | idle prio=63、stat prio=62、timer prio=61；各栈 128 个 `OS_STK` | `OS_N_SYS_TASKS=2` 由 stats 开关决定，并不另为 Timer 增加一个 TCB；Timer 仍消耗同一 TCB 池中的槽。 |
| 当前附加功能 | Flag/Memory/Timer/Mbox/stats/debug、Task/Flag/Memory/Timer names 均开；TaskReg=1 | 所有对应字段/全局对象都必须表示；`OSIdleCtr` 即使关闭 stats 也存在。 |
| 条件实例 | EventMulti/EventName/TaskProfile/TLS/Trace/safety-critical 当前关闭 | 各自给出字段族/协议扩展；当前 TCB64 不能被改称所有宏组合的布局。 |

增加 Flag/Mem/Timer/Statistics、Task register allocator、系统栈及条件控制全局的地址声明。
`OSUnMapTbl` 与默认字符串等只读常量另有只读存储来源，不混入可变计数值。
机器数值复用 QCP IntLib/CompCert：`TaskStatus` 直接使用 `Byte.int`，经 `Byte.unsigned`
给出 C-facing 的 `Z` 值；其他 `Z` 字段附 `0 <= value < 2^w`。机器加减/窄化使用已有
`unsigned_last_nbits`、机器整数或等价取模，signed cast 使用当前 C/CompCert 语义；`nat`
仅用于不会被 C 读取的 generation/history。

### 1.2 物理字段与抽象值

每个模块有单一 concrete image/字段表示，抽象 record 是对其稳定值和生命周期的解释，不再拥有
另一份堆。未初始化、未改写、释放后的残留字段用精确 raw image 或未定值表示；不能统一清零。
示例：`OSTmr_Free` 没有写 `OSTmrDly`；QFlush 没有清 Queue slots；TaskQuery 复制整个 TCB，
包括本配置实际存在的字段/填充字节，而不是只复制逻辑 TaskStatus。

公开函数的域分开表达：NULL、源码可判定的错误 type/state/option、以及有效对象路径。
非 NULL 不等于可安全解引用；调用者必须提供 C 实际读取的存储权限，但不能为了证明而删除
源码本来处理的 NULL/错误类型路径。未被源码检测的所有权违约不会自动得到某个错误返回码。

纯表关系同样只观察真实下标。`task_mutex_priotbl_consistency` 的 table 分支现限定
`task_priority_in_range`；依据是源头 `OSTCBPrioTbl[OS_LOWEST_PRIO + 1]` 与当前
`store_prio_tbl` 的有限数组表示。Coq total map 在数组外的值不是额外 C 单元，
不应用这些值制造删除后的悬空别名义务。合法下标的 reserved/free/live 与 Mutex alias
约束不变；任何实际数组访问仍须证明下标合法，disabled PCP 仍是字段 tag 而不是下标。

### 1.3 错误码、option 与结果编码

扩展已有 `error_codes.v` 的 `OSErrCode`/`encode_os_err_code`，覆盖 header 中实际使用的
Event/Mbox/Queue/Sem、Task/Reg、Flag、Memory、Time、Timer、TLS 和 safety 错误；保留现有
构造子的源码数值。补 `encode_os_err_code_in_range` 与已定义码的 encode/decode 对应，不将
未定义字节随意解释成成功码。若源码常量存在数值别名，按别名等价处理，不能假设名称全单射。

option/status/state 的 raw 字段均保留原 word，另给相应 encode/decode/bit-mask 关系。
只能在该 API 实际 enum 检查成功后得到合法构造子；PostOpt 未使用的位和 PendAbort 的 default
分支不能由一个严格 option datatype 预先排除。`BOOLEAN`、perr、返回指针/数值、输出参数和
是否改变状态是独立观察：例如 MutexAccept TRUE+PCP_LOWER、TimerStop TRUE+error、Queue
成功 NULL+NONE、FlagAccept 非零+NOT_RDY，必须能由同一结果接口无歧义表达。

`OS_MemClr/Copy` 的 size 参数是 u16；每个调用先应用 C 的实参窄化。当前所选池大小可另证
未截断，其他合法宏组合不能因实参写着 `sizeof(pool)` 就假定全部池被清零/复制。大容量实例
需保留实际低16位长度与剩余原字节，再用真实 BSS 初值/后续字段写入证明 boot 性质。

## 2. Canonical state 与公共更新接口

保留 `UCOS2_Verify_State`，扩展为 Intr/Task/Sched/Event/Tick/Flag/Memory/Timer/Statistics 的组合，
另明确共享控制字段与名称资源的归属；它们是同一状态中的公共资源接口，不是第二个内核状态。
Mutex/Sem/Mbox/Queue payload 仍归 Event；QCB/private/published storage 由 Queue owner 在同一
Event/Queue 家族中组织。配置关闭时使用经过布局/可达性证明的空实例，不使用无约束 `OtherInv`。

字段按对象语义组织，不因历史补字段而新建包装。本轮已将原 `TaskNativeFields/taskNative`
的 13 个字段直接并入 `TaskAbstractState`；原 `EventNativeFields/eventNative` 的 5 个字段
直接并入 `OSEventAbstractState`，命名为 `eventName`、`eventPadding1/2/3/19`；原
`KernelGlobalAddresses/kernelGlobals` 的 22 个地址直接并入 `StableGlobVars`，与已有全局地址同层。
专用于这些字段袋的 updater/helper 同步删除，操作直接更新所属对象，不保留旧类型或投影 alias。
`KernelConfiguration` 仍表示独立配置实例；raw image 与 live state 的区别、private allocation、
lifecycle、借用与调用历史各有独立语义，保留其类型和资源关系，不随字段平铺合并。
实施检查状态见 foundation，本轮组织调整不改变历史验收结论。

本轮进一步删除 `task_tcb_init_spec.v` 开头仅互相引用的旧 projection/observation 家族
（3 个定义、6 个引理），保留实际源码参数、初始化写集合和发布/hook 接口。
`tick_task_preserves_non_timeout_fields` 已平铺原 13 字段嵌组并补 `curPrio`，三个跨模块消费者
不再依赖历史分组位置。waiting single backlink 的旧定义及两个 bundle 冗余已删除，
全部 lib/spec 消费者已适配。
第五份旧名映射 `.coq_debug/model_static_interface_cleanup.json` 仅用于迁移定位。
本批字段袋与接口清理的完整模型集成已通过：固定独立模块检查覆盖入口中的 88 个唯一
lib/spec 文件，rc=0，`first_diagnostic=null`、`dependency_errors=[]`。检查后逐字节确认
88 个当前源文件及入口均与构建副本一致；剔除嵌套注释和字符串后，无 `Native`/`native`
标识符残留，也未发现实际 `Admitted`、`Axiom`、`Parameter`。`task_tcb64_image` 中残余的
`let n := t` 局部别名亦已在这次检查前删除，定义含义不变。
这次集成包含完整 MutexDel，不再只有先前 focused 证据；公开 abort 效果未弱化，三个内部
成功效果引理的 Event 有效性前提仍由入口不变式推出。SemPend 的六条状态/等待证明保持
statement，三处私有 helper 替换及 SemDel、MutexRdyAtPrio 的适配均已覆盖。
MutexPost 的六模块 frame、wake 桥接和内部 reserved 有效性修复也已集成；更强 frame helper
现名为 `mutex_post_disinherit_crit_rel__handover_commit`，无旧名引用或文件外签名消费者。

本结果只完成字段袋与接口清理优先批次，不表示全部 API 模型剩余的语义组合已经完成，
也不表示旧 generated/manual 已迁移或旧 VC 已通过验收；原目标其余工作继续。
全局不变式复审未发现此次展平资源漏接，历史 slice 仍有独立语义。上述声明扫描只覆盖
这 88 个文件，不扩张既有工具/平台信任边界；工具 24 项 mock 是独立的工具测试。
`OSMutexPend`、`OSSemQuery` 新增的 C annotation 名称同步与先前 `OS_TCBInit`、
`OSMutex_Priority` 相同，非 annotation 字节经精确比较保持不变，没有修改 C 实现。

接口名同样按实际语义区分：当前全模型采用 `UCOS2_inv`、`UCOS2_raw_rep` 和
`UCOS2_state_inv`；旧证明切片采用 `UCOS2_verification_slice_*` 及模块级
`verification_slice_*`，不是当前全局不变式的别名，也不因改名获得全模块覆盖。
固定 64 字节视图使用 `TCBCommonImage`、`task_tcb64_image`、`encode_tcb64_link`；
配置布局使用 `TCBLayoutImage`、`task_layout_image`、`encode_task_link`，不混用二者的地址与资源。
真实内核动作及其保持义务使用 `KernelClientAction` / `KernelClientCertificate`，
临界区资源为 `CriticalRegionResources`，平台中断契约为 `InterruptPlatformResources`；
这些不是 raw bytes，不能统一改称 Raw。源码 API、C 结构/字段及其布局语义不因改名改变。

必要的 boot、借用和调用历史是明确的 ghost 元数据，不假冒 C 全局变量：

- 启动阶段区分原始静态存储、各池已初始化、系统任务已创建、运行态已建立。优先把阶段作为
  `kernel_boot_rep phase ...` 的索引及建立关系，不额外在 C 状态中发明一个初始化标志。
- Task 已有 invocation/generation/history 继续使用；Event/Flag/Timer/Memory 的对象实例身份
  与池索引分开。真正跨回收/再分配的调用保存实例身份，不仅保存地址。
- 条件 `OSSafetyCriticalStartFlag` 是真实可变 control 字段，归全局控制表示；不把它误放成
  immutable configuration，也不把条件源码从函数清单删除。

具体采用 `KernelControlState` 的可选 safety-critical flag，以及 `NameResourceState` 的共享
名称字节/借用登记；公共 owner 为新 `lib/kernel_resources.v`。该文件只负责这些确实跨模块的
资源，不吸收 Task/IPC 的具体语义。它是四个新 OS 模块库之外新增的公共资源 owner 候选。

对每个 projection `get_m` / `replace_m`，同族接口是：

```text
get_m (replace_m v s) = v
get_n (replace_m v s) = get_n s                         (m <> n)
replace_m (get_m s) s = s
replace_m v2 (replace_m v1 s) = replace_m v2 s
replace_n w (replace_m v s) = replace_m v (replace_n w s) (实际独立的 m,n)
```

这些是结构等式，不命名成 `*_correct`。局部对象 map 更新复用相同的查找/非目标保持接口。
操作先给源码效果，再证明有效性；不能把 desired post-invariant 当作操作自己的额外 guard。

## 3. 统一的资源与并发设计

### 3.1 全局组合与局部资源

当前全局入口为 `UCOS2_state_inv`、`UCOS2_raw_rep` 和 `UCOS2_inv`。
各模块的空间资源以 `**` 合并，模块有效性与跨模块关系是单独的纯合取。
`UCOS2_state_inv : Prop` 表示全局抽象状态不变式，不占有堆；`UCOS2_raw_rep : Assertion`
描述空间资源，`UCOS2_inv : Assertion` 将两者结合。原 `UCOS2_validity_bundle` 已统一改为
`UCOS2_state_inv`，不保留同义别名。`UCOS2_state_inv_with_ready` 仅用于显式给定 ready 关系
的源码阶段；历史切片对应 `UCOS2_verification_slice_state_inv`，不与完整状态不变式混用。

空间层的唯一完整定义位于 [`ucos2_spatial.v`](../lib/ucos2_spatial.v)：
Task（公共存储及 parked stacks）、Scheduler、Interrupt、Event、Queue、Tick、Flag、Memory、
Timer、Statistics、KernelControl、Names 依次分离合取，不再以 Task/Scheduler 加一个大 residual
作为主定义。Sem/Mutex/Mbox 的 ECB 由 Event 统一拥有，不重复加入同一块存储；它们的有效性
和跨模块协议仍由原有纯状态不变式约束。正在执行和私有创建的栈、已借出的 typed 区间仍由
实际调用者持有，不因模块重组而成为第二份全局资源。

统一接口是 `UCOS2_raw_rep_missing_module` / `UCOS2_raw_rep_missing_two` 和
`UCOS2_inv_split_module` / `UCOS2_inv_split_two`；常用名字只是它们的特化。
第二项要求两个 owner 不同，不能从一次占有中拆出同一个模块两次。形状为：

```text
UCOS2_inv sg s
  <-> coq_prop (UCOS2_state_inv sg s) &&
        (module_rep sg s m ** missing_module sg s m)

UCOS2_inv sg s
  <-> coq_prop (UCOS2_state_inv sg s) &&
        (module_rep sg s m ** module_rep sg s n ** missing_two sg s m n)
        (* m <> n *)
```

`UCOS2Module` 只是上述物理资源所有者的选择标签，不增加 abstract state/ghost 字段。
`UCOS2_selected_rep` 在同一完整模块分离合取中将被选出的项替换为 `emp`；所有项均选中时与
`UCOS2_raw_rep` 定义相等。它只选择模块断言，不改变其内部条件或全局 `UCOS2_state_inv`。
拆合、剩余资源运输及更新后合回
使用 QCP 现有分离逻辑定理；更新后的 `UCOS2_state_inv` 仍必须来自操作保持性证明。
调用端优先使用现成的 split/merge/frame 引理，不手工展开模块标签的判等实现。
完整拆合保留纯条件的原有归属：Interrupt/Tick 等既有模块表示中
内联的数值范围条件仍随该模块一起拆出、接回。本批没有把这些局部条件搬入
`UCOS2_state_inv`，也不声称 `UCOS2_raw_rep` 的每个叶子都不含纯命题。

`missing_task` / `missing_task_sched` 会移除整个 Task owner，包括 parked stacks。
现有只改 TCB 公共存储/ready bitmap 的端点改用明确的 `missing_task_storage_sched`；
它保留 parked stacks，不能与完整 Task 模块拆分混称。栈子资源、priority table 和三方 IPC
的细分接口同样明确所移除的资源。这些是实际子模块操作需要的局部化，不是旧名兼容别名。
本批接口重组的检查结果以 foundation 本批记录为准，前一批通过不自动覆盖新修改。

全局静态配置已从 `selected_task_profile` 改名为 `selected_kernel_profile`，由
`UCOS2_inv` 的有效性层统一持有；TCB 特有的条件仍是 `tcb64_configuration`。
`selected_kernel_global_regions` 合并 core、条件模块、TaskReg 及所选 idle/stat/timer 系统栈，
`valid_selected_kernel_global_layout` 约束这些区间的范围与不重叠。
完整区间表的 44 个 `g_*` 地址各出现一次，当前 IEC 关闭配置实际启用 43 段；
`stable_glob_vars.v` 全文件固定 debug Load 已通过（rc=0，0.442 秒）。
`UCOS2_timer_unlink_preserves_validity` 已删除能由 profile 导出的额外单池 layout 前提；
模型/spec 的 profile 名称已同步，消费者整体仍待统一检查。
该静态区间声明不占有内存，尤其不能将系统栈再作为一份独立字节资源加入全局分离合取。
全局不变式持有共享/已发布资源；private TCB/QCB、调用栈、已分配 Memory block、输出数组等
通过 invocation 或应用资源接口持有，global 只保留不会重复占有这些字节的分区/借用记录。

每个 module/object/field 均提供原值 split/merge；更新需要如下实质条件：

```text
valid_module post /\ cross_relations post
residual old |-- residual post
updated_object_rep post ** residual old |-- kernel_inv post
```

residual 可以读取别的抽象字段。例如 Event 表示读取 Task 地址/优先级时，Task 更新应证明
这些依赖不变或证明更新后的表示运输；`EventState` 没变本身不足以 frame 整个 Event 断言。
跨多个模块的操作共同聚焦，不伪装成单 projection 的 atomic lift。

### 3.2 生命周期的共同形式

各池实例使用适用的 `free / private / published / retiring` 分区，不强迫每个池都具备所有阶段。
这些阶段的资源含义是：free 属池；private 属具体 invocation 且不可从已发布根访问；published
由共享模型拥有；retiring 记录源码尚未完成的解绑/回收。只有实际写入步骤可以改变归属。
free list、used map、private reservation 的有限域穷尽、互斥、`NoDup` 与数量守恒均为模块义务。

为一次阻塞调用保存的逻辑信息包括：原 invocation、Task slot/generation、所等待对象实例、
调用参数、已交出的节点/消息/输出资源、返回条件。超时、abort、delete 与重用发生后，以该
continuation 判定是否能恢复，不把重新读取的 `OSTCBCur` 或同地址新对象当成原调用者。

### 3.3 环境操作与平台契约

底层宽 STS 仍可作为逻辑载体，但不能由此推出所有环境动作保持新模型。扩展
`KernelClientCertificate`：每个真实操作族证明其 guard/effect、受影响模块有效性、非目标资源
运输以及 invocation 存活/终止关系；所有允许的 Task/IPC/Tick/Timer/ISR 操作实例共同生成 rely。
creation family 的已证明实例只覆盖创建族，不覆盖尚未加入的内核操作。
Suspend/Resume 的临界区实例位于对应函数 spec：`task_suspend_critical_client` 与
`task_resume_critical_client` 复用同一个 `KernelClientCertificate` 接口，不新建环境状态。
其 certificate 分别连接当前全局有效性、其他创建者的私有 reservation/storage frame 和
原 invocation 的 generation/非 retired 身份；共享的
`glob_task_set_usedtask_preserves_invocation_active` 只要求更新同一已存在实例并保持 generation。
这里的 active 不等于 ready，更不保证被挂起者立即返回。actor、Save/Restore 和这些原子
动作的真实源码嵌入仍由并发/平台绑定提供；这不自动把任意 trace 或 OS_Sched 纳入允许环境。

`KernelClientAction` 现分别记录 Task actor 与 Event allocation actor；它们是动作参数，
不是新增 OS 状态字段。`KernelClientCertificate` 增加 Event 私有分配 frame 义务，
Task 创建及 Suspend/Resume 已接入。统一的 `kernel_client_resource_trace` 带可选 Event
observer：旧 `kernel_client_trace` 是 observer=None 的接口，仍保留原 Task-only 定理签名；
Event 区间同时运输两个名字空间的资源身份。stopped 仍只表示原 Task 续体终止，不意味着
私有 ECB/QCB 被自动回收。各 source action 的 certificate 与整个内核的实际调用/空间
嵌入分开；不能仅凭这些纯轨迹定理断言任意 ISR 或 callback 不会改写私有字节。

TCBInit 模型消费者现已统一使用同一完整布局 image 完成 detach、取得、私有初始化与发布。
公共字段 initializer 由既有 layout lift 复用；Multi 开启时按源码在 EventPtr 后清零两个
额外指针，关闭时保留未观察的 image 项且不拥有这些不存在的 cell。初始化前后保留相同
allocation 的 FlagsRdy 和实际布局 padding，free/head links、priority table 与 used map
都使用配置化 slot 地址和完整节点表示。源序写入、retained/written 拆合及最终资源重组
已有证明，该增量在本轮字段/接口重构前通过完整依赖检查；当前检查状态见 foundation。
该布局增量覆盖 Multi 开/关，其他 scalar
开关仍取 native profile；全局保持仍受 selected profile 约束，不代表 Multi-enabled 全局
等待协议、平台/整调用组合或旧 C/manual 已迁移。

Create/CreateExt 的组合接口位于 `task_create_spec.v`、`task_create_lifecycle_spec.v`
和 `task_create_return_spec.v`：保持 IEC/priority/ISR/table 的源码顺序，原始 critical
关系不增加 lifecycle guard；由旧全局有效性、实际 caller origin 与 free table 观察导出
reservation 和 TCBInit entry。运行中 origin 绑定当时的 current Task/generation，Boot
origin 要求尚未 running；这不是额外 C 判断，也不凭空取得平台执行栈。失败回滚消费
当前表项实际写零后的资源、missing table 与其余全局资源，保留原 invocation；不恢复旧
全局快照。默认空 trace 宏不求值参数，成功后的 OSRunning 必须在 trace 后重新观察。
`task_stack_clear_spec.v` 为当前 growth=1/32-bit OS_STK 描述有序选项检查与清零循环，
复用 QCP UIntArray 和已有 copy-prefix 接口。四个原始独立 spec 及完整依赖的固定检查
在本轮字段/接口重构前已通过，历史证据与当前检查状态见 foundation；这不是对应 C 函数的
VC 证明完成。完整平台/空间调用嵌入、其他配置和旧证明迁移
仍属于原目标。

IRQ save/restore token 保留原保存值、调用者身份和嵌套状态；scheduler lock 只抑制切换，
不抑制 ISR。饱和计数不能隐藏：OSIntEnter/SchedLock 达 255 后不再增加，正常成对使用的
安全契约必须有未饱和余量，原始函数关系仍精确表达饱和分支。
`interrupt.v` 的四个计数 transformer 直接表达 running/ISR/零值/饱和条件，exit 的调度请求
唯一确定。`int_enter_spec`、`int_exit_spec` 与 `sched_lock_spec` 使用这些共同接口，而不是
在共享库另留一套无消费者的 `atomic_*` 整状态包装。Enter 的调用协议是中断已经关闭，
源码没有 Save/Restore；Exit/Lock/Unlock 则先在临界区外观察 running，true 分支才 Save，
随后读写当前计数。分支观察是 spec 的局部索引，不增加全局字段，也不假设两次观察间状态相等。
Exit 在 old nesting=0 或 1 且 lock=0 时都可进入选择；Unlock 只有 old int=0、lock=1 才请求
调度，old lock=0 不调度。Unlock 的请求跨 Restore 保留，但后续 OS_Sched 的选择依据必须
来自它自己的 Save 后状态，不能直接使用解锁前快照。
Exit 复用 Scheduler 的物理准备端点和有条件的全局重组，不表示源码调用了 OS_Sched，
也不包含 OSIntCtxSw、trace/TLS 或原 ISR 返回。计数的机器范围由已有 QCP UChar 存储
推出；一个通用 `interrupt_inv_merge_counters` 为这组 API 接回原有中断不变式。
未饱和配对恢复定理不能套在饱和路径上，也不能据此排除配对调用之间的真实环境步。
Restore/unlock/callback 边界关闭当前阶段所要求的共享表示；私有帧运输必须有不可达性/实例证据。

平台接口分别声明 CPU save/restore、初始栈、Task/ISR context switch、启动切换、hook/callback
的代码绑定、资源 footprint 与调用/返回或终止关系。两个已选 creation App hooks 可实例化空效果；
其他接口保留各自契约，不默认空调用，也不声称 ARM/BSP 实现已证明。

### 3.4 名称、消息和外部存储

NameSet 写的是指针，不复制字符串；多个对象可以指向同一个默认 `"?"`，所以不能在各对象
表示里分离合取一份完整字符串。设计采用 `NameResourceState`：`nameBytes : addr -> option Z`
是有限 byte map，`nameSources/nameReaders` 记录这些字节的应用/静态存储来源和存活读取；当前对象的
name references 从各模块状态导出，不另存一份可能不同步的指针表。字节表示只拥有每个地址
一次，因而也允许两个字符串视图共享后缀，而不要求所有字符串根地址的区间互斥。

`store_name_bytes` 用现有 map/byte 表示；`readable_name p bytes` 给出到首个 NUL 的有限路径，
以及这些字节均在共享 map 中的值关系。`name_publish` 从已有登记取得引用，或由调用者交入
新字节/明确的只读借用资源；`name_release` 只有没有对象/存活读取者仍引用时才归还。
其逻辑登记不增加 C 写入，来源是经验证调用者的存储协议，不能声称内核在运行时维护引用计数。
公开协议若允许应用随意释放/改写正在使用的字符串，则此来源不成立，须保留对应不安全行为。

NameGet/OS_StrLen 从这里取得读取权限并保留存活期，不从 `pname <> 0` 推出可读、终止或长度
小于 255。可独立验证的 OS_StrLen 仍可直接接受 caller-owned 字符串，不强迫该辅助函数修改
共享登记。本设计不依赖尚未提供的 fractional permission，也不新增操作系统 capability。

Queue/Mbox 传递的是 `void *` 值；内核不自动拥有指向的消息内容，也不按指针值去重消息。
若应用需要内容所有权转移，另加应用层消息协议，与内核精确 FIFO/直接唤醒语义分开证明。
系统栈、用户栈、Flag 栈节点和 partition buffer 也按实际借出/归还划分，不重复占有。

### 3.5 头文件中的全局资源归属

以下逐族覆盖 `ucos_ii.h` 的全部 `OS_EXT` 声明。条件对象只在相应配置下存在；表中 owner
负责它的实际 cell/数组，其他模块只借助标识和纯关系引用。`StableGlobVars` 仅登记地址和布局。

| 源码全局 | 唯一空间 owner | 关系或条件 |
|---|---|---|
| `OSIntNesting`、`OSLockNesting` | Intr | IRQ/调度锁计数；调度锁与中断屏蔽不是同一权限。 |
| `OSPrioCur`、`OSPrioHighRdy`、`OSTCBCur`、`OSTCBHighRdy` | Sched | native cache 与阶段；指向的 TCB 仍由 Task 拥有。 |
| `OSRdyGrp`、`OSRdyTbl`、`OSRunning`、`OSCtxSwCtr` | Sched | ready 编码、启动/切换与 u32 计数。 |
| `OSTCBTbl`、`OSTCBFreeList`、`OSTCBList`、`OSTCBPrioTbl`、`OSTaskCtr` | Task | published/free/private 的物理资源分区；private TCB 字节由创建调用持有，global 只保留 reservation。 |
| `OSTaskRegNextAvailID` | Task | Reg table size>0；分配下一个 register ID，不等于 Task ID。 |
| `OSTaskIdleStk`、`OSTaskStatStk`、`OSTmrTaskStk` | Task 栈资源接口 | 后两者分别受 stats/timer 开关控制；正在执行的栈帧及 Flag 节点按借用协议拆出，不把整个活动栈同时放入 global。 |
| `OSEventTbl`、`OSEventFreeList` | Event | `OS_EVENT_EN && OS_MAX_EVENTS>0`；Sem/Mutex/Mbox/Queue 共池。 |
| `OSQTbl`、`OSQFreeList` | Queue | Q 启用且容量>0；不包含用户消息所指的 heap。 |
| `OSFlagTbl`、`OSFlagFreeList` | Flag | Flag 启用且容量>0；节点来自调用栈，不来自组池。 |
| `OSMemTbl`、`OSMemFreeList` | Memory | Memory 启用且容量>0；分区 buffer 由调用者交入，已分配块由 loan 持有者所有。 |
| `OSTime`、`OSTickStepState` | Tick | 分别按 TimeGetSet 与 TickStep 条件存在；二者不是 Timer clock。 |
| `OSIdleCtr` | Statistics | 总是存在，u32 volatile；即使统计任务关闭也不能 frame 掉 Idle 的真实写入。 |
| `OSCPUUsage`、`OSIdleCtrMax`、`OSIdleCtrRun`、`OSStatRdy` | Statistics | stats 条件；逻辑采样阶段不增加 C cell。 |
| `OSTmrTbl`、`OSTmrFreeList`、`OSTmrWheelTbl`、`OSTmrFree`、`OSTmrUsed`、`OSTmrTime` | Timer | Timer 条件；free 与 wheel 链分别解释相同 timer 对象的 link 字段。 |
| `OSTmrSem`、`OSTmrSemSignal` | Timer（仅这两个指针 cell） | 指向的 Sem 对象由 Event 所有；初始化值、失败与存活期另有关系。 |
| `OSSafetyCriticalStartFlag` | Kernel control | `OS_SAFETY_CRITICAL_IEC61508` 条件；不是所有 safety-critical 宏都等价。 |
| `OSUnMapTbl[256]`、默认名称字节、debug const 数据 | 公共只读资源接口 | 前者不是 `OS_EXT`，在 core 定义；debug 常量由对应源文件/配置提供。已有 `store_osunmaptbl` 等表示只保留一份，组合时不得重复加入。 |

公共记录的具体最小接口为：`KernelControlState.safetyCriticalStarted : option bool`；
`None` iff 本配置无该 cell。`NameResourceState` 包含有限 `nameBytes : addr -> option Z`、
`nameSources : nat -> option NameStorageSource` 和 `nameReaders : nat -> option NameReadLease`。
来源记录给出字节域、静态/应用来源和归还条件；reader 身份是 `nameReaders` 的映射键，
record 只保留根地址和所读取域，不再重复存储 invocation。
对象引用由其 name 字段导出；共享后缀通过同一 byte map 解释。ghost 记录的分配/回收只伴随
真实资源的交入、读取结束或最后引用释放，不能凭空制造可读字节。

### 3.6 配置变化的具体增量

配置选择先检查源码预处理合法性，再证明布局和运行协议；合法预处理不代表 boot 资源充足。
源码检查包括 lowest priority<=254、至少启用一种 TaskCreate、TaskReg size<=255、
`2 <= OS_MAX_TASKS <= OS_LOWEST_PRIO-OS_N_SYS_TASKS+1`、Event/Q/Flag/Memory 容量<=65500；Timer max 为 2..65500、wheel
为 **2..1024**（按实际条件，不按旁边旧注释），并要求 Sem 启用。正 tick rate、存储区间和
当前启动所需两个 Sem/三个系统 Task 的可用性另由具体实例证明，不能称为已有宏检查。

| 条件变化 | 状态/资源增量 | 必须补的语义接口 |
|---|---|---|
| `OS_LOWEST_PRIO>63` | `OS_PRIO` 从 u8 变 u16，位图行数与 TCB/Event 布局变化 | 高/低 byte 的实际 OSUnMapTbl 查找、16-bit 位计算/更新；不复用 narrow 布局证明。 |
| `OS_EVENT_MULTI_EN` | TCB 的 MultiPtr/MultiRdy 字段、借出的 NULL 终止输入数组、等待集合/输出前缀 | register/wake/remove 全组操作、按顺序获取多个就绪资源、duplicate 输入的真实效果。 |
| Event/Task/Flag/Memory/Timer name | 相应对象的 pointer field；共享名称资源 | NameGet/Set 的 guard、长度读取、指针及存储存活期；Timer 没有独立 NameSet API。 |
| `OS_TASK_PROFILE_EN` | TCB 的 CtxSwCtr/CyclesTot/CyclesStart/StkBase/StkUsed | u32 cycle 差/计数、context-switch hook 的来源、StatStkChk 的真实写集合；不能只增字段不补平台更新契约。 |
| `OS_TASK_CREATE_EXT_EN` 与 TLS size>0 | Ext/stack/id/opt 与 TLS 数组；TLS 值为指针，析构和 allocator 属实际 TLS 实现 | Init/Create/Del/TaskSw 调用顺序、错误/不返回路径、每个 TLS slot 的资源协议。仅声明本内核的外部边界，不冒称 TLS 实现已建模证明。 |
| `OS_TASK_REG_TBL_SIZE` 改变 | 完整 u32 array 与 u8 next-ID cell | Init 清全部项、Get/Set 单项、ID 单调分配及耗尽；当前 Reg0 只是 size=1 的兼容投影。 |
| Arg-check 关闭 | 不新增字段 | 删除的运行检查不能继续作为返回分支；实际解引用前置权限仍由 caller 提供。 |
| Task delete / Flag clear-wait 关闭 | 真正消失的 TCB FlagNode/DelReq 字段及函数分支 | 单独布局，剩余 wait/timeout 协议；不能给被预处理删除的 API 空实现。 |
| Trace / app/CPU hooks | 由具体宏展开/port 实现决定是否有外部状态 | 实际位置、调用资源、可重入性和返回关系；只对选定空实现证明空效果。 |
| `OS_SAFETY_CRITICAL`、`OS_SAFETY_CRITICAL_IEC61508` | exception hook；后者另有 started cell | perr=NULL 分支与 runtime-create 禁止分支按各宏区分；exception 若可能返回，保留后续源码行为。 |
| `SAFETY_CRITICAL_RELEASE` | 联动配置实例，而非单一 bool 开关 | header 同时要求 arg-check 开、app hooks/debug/stats/tick-step/各 Delete 关、critical method=3 等；完整实例逐项检查，不能直接套当前 profile。 |

布局以字段清单、offset/size/alignment/padding 的配置函数设计；只对实际 ABI 编码给出
`<structure>_layout_valid` 和 typed/untyped byte 对应接口。`volatile` 表示真实可观察访问；
CSL 临界区协议不能代替 C 编译/平台对 volatile 和原子性的支持说明。

## 4. Task 与 Scheduler

### 4.1 状态与表示

继续以 `TaskID` 表示池槽，`OSTCBId` 是独立的 16-bit 应用 ID，优先级和 generation 均不能
混作 TaskID。保留现有 `TaskLifecycleState` 的 reservation/private image/active order/invocation
接口，扩展 deletion、blocked continuation、stack lease 和 register allocator，而非建立第二套 Task 池。

| 字段族 | 设计 |
|---|---|
| 原生 TCB image | `TCBLayoutField` 统一公共与条件字段，布局选择实际拥有的字节；`TCBField` 是已有公共字段投影。used/free/private 共用配置存储接口，free/private 允许旧值；used image 从既有 Task 导出。`TaskAbstractState.stat` 直接为 `Byte.int`；固定 TCB64 保留显式兼容视图。 |
| 调度观察 | `curPrio`、`dly`、suspend、pend result、event pointers、message、next/prev、del request 由对应 image/编码关系得到；不能把每个 raw 暂态强制解释为稳定 Task。 |
| 等待登记 | 单 Event、Flag node、EventMulti 分开。Multi 可同时有 SEM/MBOX/Q 和 MULTI 位，完整字节保留所有组合；`PendType` 只描述 mask 种类，不再充当状态字段。wait-set/phase 是实际字段与登记的关系，不自动增加第二份状态。 |
| 池与生命周期 | used/free/private/retiring、active NULL-terminated 双链、priority reservations、数量、generation、原 invocation 的 continuation；pending retirement 不伪装成一个正常 ready Task。 |
| 栈与扩展 | 原生指针/size/opt/extension 是值；存储使用独立栈区间/初始上下文/借出 frame 接口。TaskStkChk 需要有界扫描证据，不能从 TCB 中只有一个地址就得到整栈权限。 |
| 条件字段 | TaskReg 为长度受配置约束的数组，当前 Reg0 保留兼容观察；全局 `OSTaskRegNextAvailID` 属 Task。TLS/profile/name 字段和回调分别绑定条件实例。 |

状态字节操作已集中到 `lib/task_status.v`：使用真实的 OR、8-bit complement/AND，
明确区分 `PEND_ANY=55` 与 MULTI=128，超时只清前者。`task.v` 的旧编码名保留
兼容导出，普通与 Multi 操作共同消费 canonical 字节，而非维护平行的单等待 record。
`task_status_single` 只构造精确的单种类状态；从任意字节转换到该形状必须先证明 mask
相等，不能丢弃额外位。`task_non_suspension_bits` 保留 MULTI 和未使用的 bit 6，不混作
PEND_ANY。Pend 的 OR、Event wake 的指定 mask 清位与 Tick 超时均有 Task/image 对应；
Tick 还覆盖完整配置 image 和 registered→expired-linked 阶段。范围与截断复用 QCP
IntLib/CompCert，未新建通用位运算或分离逻辑系统。各批集成检查范围见 foundation。

TCB 字节表示现集中到 `lib/task_storage.v`，原定义从 `task.v` 抽取并重新导出，
不是复制另一套 Task 池。`tcb_layout_storage_rep` 已覆盖当前共同配置下的
Multi-off 64 字节和 Multi-on 72 字节局部对象：后者在 EventPtr 后加入两个真实指针，
后续字段移动 8 字节，两个 padding 位于 50/51。已证明字段清单的字节覆盖、无重复、
关闭 Multi 时与原表示等价，以及两指针拆出/写后合回。数值覆盖不代替 QCP 命名字段
地址与实际 ABI 的对应证明，也不把固定 64 字节视图改成另一种配置。
`tcb_multi_*_image` 已精确表达 Pend 前缀、Event wake、Tick 超时和正常 cleanup
的 TCB 写集合与 frame；不包含不存在的 EventPtr/Dly 清理，亦不覆盖提前返回路径。

配置 image 类型现归 `TaskStateDef` 所有，`TaskLifecycleState.taskFreeStorage` 和
`TaskPrivateAllocation.privateStorage` 已改用它，free→private 传递同一份字节观察，不另建
Task 池或条件字段旁表。`task_slot_storage_rep` 和 free-link 编码随 Multi 开关
选择 64/72 字节 stride；private 字段 split/merge 显式要求字段确实存在，直接复用
`tcb_layout_storage_*` 的 QCP 拆合。boot 使用共同 free 初始化 image，回收只更新
实际 Next 字段。`used_task_rep` 已把公共 used map、完整 Task 与字段级 residual
也接到同一个配置接口；updated merge 不再只能恢复固定 64 字节切片。
`task_slot_addr` 统一池内地址，active/free links、优先级表、当前/最高 ready 缓存、
Mutex owner 和 Flag node 的 TCB 回指都使用它。关闭 Multi 时的 slot、used rep 和 Mutex
owner 编码与旧 64 字节视图的对应已有引理，不把旧 profile 改称另一种布局。

`TaskAbstractState.tcbEventMultiPtr` 表示源码真实的 `OS_EVENT **` 值；原逻辑列表已改名
`eventMultiWaitEvents`，保留输入顺序及重复项，不能把首个 Event 当成数组地址。
`task_set_multi_fields` 只写两指针并更新该逻辑观察，保留公共字段；它的 image 对应和
公共 Task map 的两指针 split/updated merge 复用已证明的 layout 接口。指针值不提供
数组读取权，逻辑序列也不自动建立与真实数组、Event 登记的关系。
`task_prepare_multi_wait`、`task_multi_wake`、`task_multi_cleanup` 已在同一 Task 上表达
caller 前缀、唤醒与正常收尾，并与相应 raw image 对应；cleanup 不虚构 Dly/EventPtr 写入。
顶层 `selected_kernel_profile` 中的 `tcb64_configuration` 仍要求关闭 Multi：存储与字节迁移不等于完整
等待/ready 协议和 continuation 已闭合，也不代表此前 C 函数证据自动适配新模型。

Multi 的合法阶段不能仅由状态字节决定：SEM|Q|MULTI 被 Sem 唤醒后仍为 Q|MULTI，
却会在未 suspended 时加入 ready；超时只清 PEND_ANY，留下 MULTI，等待数组登记还待
后继清理。因此既有 `is_effectively_ready` 仍只描述普通/单等待的 ready 条件，不能
套在全部 Multi 状态上。完整字节与真实 MultiPtr/MultiRdy 已进入 used 表示；后续必须把
wait phase、数组借用和 ready membership 一起接入，不能把字节或结构引理当作完整
Multi 调度关系。尤其需要覆盖第10节的 Suspend→wake→Resume 组合，不能仅从
woken 字段与当前未 suspended 推出 ready membership。

Scheduler 拥有 ready bitmap、当前/最高 ready 指针与缓存优先级、`OSRunning`、`OSCtxSwCtr`。
状态同时保留 ready 的逻辑集合与位图精确编码，不假定 priority table 对 Task 单射：Mutex 可有 alias。
最高 ready 从位图挑选；对应该 slot 必须是 live Task，idle 提供运行态非空 ready 的建立/保持来源。

`sched_ready_structure` 单独提取 live Task、有效 priority、排序与 NoDup，供合法的
中间阶段使用；它不替换或弱化全局 Scheduler 不变式。`sched_wake_by_status` 按
源码仅测试真实 suspension 位，置位后的 OR 编码与 membership 分别证明；清 ready 的
编码也不再要求先把 Multi 字节投影为单一 PendType。状态协议与 ready 的双向关系仍须
在全局 Task/Multi 迁移时结合字段阶段和 Event 登记证明，不能只用结构关系代替。

Suspend/Resume 共用 `task_set_status` 的单字段更新，不增加 TCB 或 ghost 字段。
`task_status_suspend`/`task_status_resume` 分别按 OR/清位更新 SUSPEND，保留全部其他位；
完整配置 image 对应与原单等待 linked phase 的保持由同一字节接口证明。
`atomic_task_suspend_selected`/`atomic_task_resume_selected` 描述 priority-table 已选中 live TCB
后的核心更新，保留 Event/Flag 登记与调度缓存。Resume 的 ready 条件是 PEND_ANY 为零且
Dly 为零，不能替换成“整个状态字节为零”或“清除 suspend 后必然 ready”。这些接口不包含
API 的参数/SELF/错误前缀、后续 hook/OS_Sched 及跨调度续体；Resume 的结构保持也不声称
已建立完整 Multi ready 协议。

当前选定配置的 Suspend/Resume 全局保持及资源重组已接通：状态组合由
`cross_module_invariants.v` 中的 `task_suspend_state`/`task_resume_state` 提供，
Resume 的 ready 决策归 Scheduler 的 `sched_resume_task`，原子关系与全局证明
共用这些更新。`UCOS2_inv_merge_task_suspend`/`_resume` 消费写后的 Task/ready 资源，
利用 Event 位图下标等价和其他 owner 的真实 residual 恢复同一个全局不变式。

全局纯不变式增加 `task_reserved_bits_clear`，没有增加状态字段：根据本版
`ucos_ii.h:105–114`，bit 6 未定义，Multi 关闭时 bit 7 也不由这些内核操作置位。
boot、发布与实际 OR/清位/超时操作具有建立或保持证明。它把普通配置的 PEND_ANY 判定
与已有单等待 ready 判定连接起来；原始 Byte 仍能表示全部 256 个值，raw transformer
没有新增过滤。此事实随已有 Task 发布、Event Pend/wake、Flag 清理及不写 Task 的模块
操作一起保持，不把它作为每个 Resume 调用临时添加的假设。其他配置、外部自定义 hook
及完整 Multi 协议仍须按实际写集合和阶段证明，不能继承该普通配置结论。

函数专用的 Suspend/Resume 前缀位于 `VC/code_proof/task/spec/task_suspend_spec.v` 与
`task_resume_spec.v`，复用上述核心，不在共享库复制完整 API。参数错误在 Save 前判断；
临界区关系从 Save 后到 Restore 前，保留 NULL、reserved、未 suspended 和成功结果。
Suspend 从实际 `OSTCBCur->OSTCBPrio` 解析 SELF，并保存源码的 self 决策；不是读取
`OSPrioCur`，也不要求输入 table 索引等于选中 TCB 的 current priority（Mutex alias）。
当前该前缀要求 live current TCB；此项必须从实际 caller 协议建立，不是由当前缓存范围
自动推出。若调用可发生在仅有 raw/free-current 存储的阶段，应按真实读取补足接口，
不能把本阶段的 live 读域直接当作已经完整审计的公共输入域。
显式 idle 参数会被拒绝，但 SELF 解析后源码不重做 idle 检查；后续调用协议必须据实
处理这一入口，不能在操作关系里添加拒绝分支。Resume 保存临界区内的 ready 分支结果，
只在此分支退出后读取 `OSRunning`；其调度请求不由临界区的 running 值决定，也不在
Restore 后重新读取可能已变化的 TCB。源阶段已具有错误 frame、确定性和当前配置全局
恢复证明；完整 Save/Restore token、trace/callee contract、原 invocation 返回和调度续体
仍待组合。这些阶段模型及其保持证明不等于两函数的 C 验证。

Task 删除的共享接口位于 `lib/task_retirement.v`，专用阶段位于
`VC/code_proof/task/spec/task_delete_spec.v`。准备阶段只清实际 Dly/Stat/StatPend；
`sched_ready_except` 以参数表达已移出 ready、但仍 live 的目标，不增设删除字段。
`task_recycle` 按实际相邻节点、捕获的 priority、u8 count 和 free head 更新；
只清源码选中的 table 槽，不偷偷删除其他 alias。已证明 Task owner 的 partition、
active/free links、count、registration、generation/reuse 保持，以及该阶段回到普通 ready
关系的条件结论。非 idle 目标存在真实后继由 active list/idle-tail 推出，不虚构 NULL Next
成功路径；具体输入的 SELF/alias 解析仍须建立实际非 idle 来源。

单等待配置的 `task_delete_prepare_single_wait` 现组合无等待、单 Event、Flag 三类
实际分支：Event callee 清位图及 EventPtr，Flag callee 摘链及清 TCB node pointer，
最后才执行三字段准备；不提前回收 TCB。有效状态下所需 lookup 的存在性、Task/Event/
Flag owner 与跨模块关系保持、ready-excluded 阶段均有组合证明，不把 lookup 失败造为
C 错误返回。Event 与 Flag 登记互斥从既有跨模块关系推导，不加运行时 guard。
单 Event 与 Flag 的跨模块摘链证明已提取为共用引理，原 wake/timeout 结论原样复用。
Flag 分支保留实际摘下的 waiter 作为节点资源归还信息；它不是新 OS 字段，也不表示
该任务栈已释放。实际堆重组分别消费 ECB 写后 image/residual 与 Flag 写后邻居资源，
复用现有 QCP-backed owner 接口；纯有效性结论不能提供这些资源。此处仍是关闭中断
区间内的组合端点，不包含开启的 trace hook、Restore 窗口或整个 API 的调用嵌入。
当前 native 单等待关系可推出 live Task 的逻辑 Multi list 为空；这不是 Multi-enabled
实现的结论。完整 Multi 数组借用/清理与全局等待关系推广仍按全部配置目标继续。

回收 image 复用已有 `tcb_recycle_image` 后按配置更新 Name，其他字段和 padding
不清零。堆归还直接消费更新后的相邻节点 residual、TCB image、roots/count/table cells，
复用 QCP `store_map_missing_i_equiv`/`store_map_missing_equiv_store_map` 和已有 free-storage
接口；纯结构定理不产生资源。删除不释放应用栈，移除 live origin 不等于调用已经停止。

回收后的 Event/Flag/Mutex 跨模块关系现已有条件保持证明：准备阶段的 RDY/OK 与
既有 linked-wait 关系可推出目标没有 Event/Flag 登记，不再另加同形 annotation 前提。
邻居 Next/Prev 更新使用共享的非链接字段运输；Event 只要求实际 waiter 被运输，不再
要求无关或已删除 Task 仍 live。目标未持有 Mutex 时，既有 alias 协议推出其唯一真实
表槽是 current priority，因此只清捕获槽便可保留其他 owner 的 aliases 与 snapshots。
未持锁是 caller/protocol 的独立恢复条件，不是 OSTaskDel 新增 guard；另证删除仍持锁
的 Task 会破坏 owner 存活关系，不能由该条件定理宣称任意调用都正确。
`task_delete_recycle_preserves_relations` 连接 Task/Sched/Event 与上述跨模块结论；
`task_delete_recycle_event_rep_eq` 由 waiter 排除和既有编码接口运输未改写的 Event
位图资源下标。窗口之后的事实必须由保持定理运输，不能直接复用入口快照。
当前核心步闭包已证明整个删除 TCB、priority table、task count 和 lifecycle 保持，并运输
未持锁条件、原 invocation 的存活及已有 private-creation assertion；保存 token 的调用
身份保持，不把第二次 Save 产生的新 CPSR 值等同于第一次。实际 lock 增减已组合到回收
端点：未饱和时恢复原 lock，入口为 255 时精确得到 254；不假设 intNesting 也保持原值。
回收所需 count 上界从当前 22 槽池不变式推出。尚未加入的 ISR/hook 必须另证这些条件。

调用协议与实现分开：当前采用官方 [API Reference](https://micrium.atlassian.net/wiki/spaces/osiidoc/pages/163887)
对 Suspend/Resume 的 Task-only 标注；两函数源码未检查 ISR。官方
[Task Management](https://micrium.atlassian.net/wiki/spaces/osiidoc/pages/163900/Task+Management)
章节另有 ISR Resume 的叙述，与 API 表不一致，不能隐去该差异或宣称覆盖所有 ISR 用法。
已证明任意 Suspend→Resume 操作组合会重新加入删除目标；这不是上述 Task-only 协议下的
合法 ISR 反例。删除窗口中的正 lock 值能阻止现有 IntExit 模型请求调度；Tick 的单 cursor
更新已证明保留 zero-delay 删除实例和 ready-excluded 关系，仍允许其他任务超时（见 9.1）。
单 Event/Flag 唤醒也已证明保持该删除阶段及 Task/Event/Flag/Mutex 关系：选中 waiter 与
删除目标不同，是由准备阶段的登记清空和真实 Event 位图/table 或 Flag 节点/TCB 对应推出，
不是增加“ISR 只能选择其他任务”的前提。Flag 端点同时保留返回 false 时仍更新并摘链的行为。
共享阶段现复用 `UCOS2_state_inv_with_ready`：普通全局不变式与删除阶段
只在 ready 性质上取不同实例，其他 owner、跨模块关系及完整 `UCOS2_raw_rep`
保持同一资源清单；未把公开 TCB 伪装成 private frame，也没有新增 OS 字段。
清理可建立该阶段，Tick/Event/Flag/中断计数核心步的标准有限闭包保持该阶段和 lock，
正 lock 阻止 IntExit 请求调度；有条件回收恢复普通全局有效性。全局及 TaskDelete、
Suspend/Resume、Scheduler/Lock、IntEnter/Exit 规约模型在本轮字段/接口重构前已通过联合检查，
不替代 foundation 中本轮重构检查的结论。
该核心步集合不是全部 ISR API，纯 trace 也不产生实际 post-store 堆。其他合法 ISR
动作、真实 Save/Restore token 与调用嵌入、未持锁协议在实际调用处的来源及 hooks
仍须组合，不能把此结果称为完整 `OSTaskDel` 正确性。

`OSPrioCur` 是实际调度缓存，不能无条件等于当前 TCB 的最新 priority：ChangePrio 后且调度锁
未释放时可能仍是旧值。设计显式的 cache-valid/refresh-pending 关系，记录来源与下一次调度刷新；
不能把旧缓存简单从模型删除。删除和 timeout 也有“位图已改、对象/等待登记尚未收尾”的合法阶段。

`VC/code_proof/sched/spec/sched_spec.v` 将 `OS_Sched` 的源码准备阶段与平台切换分开。
原始选择只由 int/lock 为零控制；切换请求比较 `OSPrioHighRdy` 与实际 `OSPrioCur` 字节，
不增加 OSRunning、current-live 或非空 ready 的运行时 guard。不切换仍有两次 high-cache
写入；切换分支在外部调用之前将 UInt `OSCtxSwCtr` 加一并回绕，未提前写 current caches。
共享 `sched_increment_switch_counter` 及 counter 的原值/更新拆合复用既有 SL 规则。

`os_sched_prefix_physical_rep` 保留原始选择的 NULL/reserved 指针及空 ready 时对槽 0 的
读取；`os_sched_ready_checkpoint` 是有证明条件的逻辑接回点，不是另一个 source-total
解释器。只有当前范围/注册关系成立、且开启选择时 ready 非空，才能通过对应定理把真实
物理端点接回该逻辑状态。非空条件必须从实际 caller/idle 协议建立，不能补成源码中的
无操作分支。新的 `UCOS2_replace_sched_preserves_validity` 复用共享跨模块 frame，
要求新 Scheduler 有效且 running 不变，不能用任意 Scheduler 替换推出全局有效性。

选定 profile 的 TaskProfile/TLS 均关闭；启用后的 TCB 计数写入与 TLS 调用还须补足。
`os_sched_installed_destination_boundary` 只是在显式 cache-install 契约下描述被选任务，
不证明 ARM/BSP、栈与 TCB 保存、hooks 或原调用返回，不能当作整个 `OS_Sched` 的 Post。
旧 `atomic_sched` 暂供旧成果迁移使用；其 ready/任务 ID 简化条件只有在既有缓存一致性
桥的前提下才与字节比较对应，新 native 函数不能把这条简化直接用于缓存陈旧的阶段。

### 4.2 必需的接口族

- 固定视图的 `tcb64_fields_rep_split` / `tcb64_fields_rep_merge`，配置布局的
  `tcb_layout_storage_split_field` / `tcb_layout_storage_merge_field` 及更新 image 的重组，`store_*` 数组/map
  接口复用既有定义；重点覆盖全部字段/填充字节的 Query、cache 重写和条件数组。
- `task_allocates_private_slot`、`task_publishes_private_slot`、`task_retires_slot` 的源码关系，
  对应 partition/count/list/invocation 保持；底层关系不内置待证明的完整 invariant。
- `task_status_bits_encode_wait`、`task_wait_registration_consistent`：单等待、Multi、Flag、timeout
  cleanup 与 suspension 组合分别说明，不能把 pending-result 和仍有等待登记视为同一事实。
- `task_priority_update_preserves_<relation>`、`task_delete_preserves_<relation>` 与 Scheduler/Event/
  Flag transport；当前缓存、permanent/PCP alias、waiter 位图必须使用正确阶段的字段。
- `sched_bitmap_encodes_ready`、`sched_selects_highest_ready`、`sched_refreshes_current_cache`、
  context-switch continuation；`OS_Sched` 比较的是源码缓存，错误比较不能被抽象状态消除。
- `task_stack_scan_prefix` 与 `task_stack_scan_result`：按栈增长方向扫描连续 0 的前缀，保留
  首个非 0 的停止位置/存储、实际 nfree 和 `size - nfree` 的机器语义。无停止证据不能宣称有界。

等待登记接口区分 `NoWait | EventWait instance | EventMultiWait instances array_addr |
FlagWait group_instance node_addr`，阶段关系区分 registered、expired-linked、woken-unlinked、
resume-cleanup，但不预设每个 Task 必须额外保存一份登记枚举或 phase 字段。能够从真实
status/result/delay/MultiPtr/MultiRdy 和借用数组推出的事实采用关系谓词；只有不可从当前字节
恢复的原调用身份、被借资源/对象实例才保留有消费者的历史信息。当前
`task_multi_registered_fields/expired_fields/woken_fields` 已按此原则观察实际 image，
而不复制一个 status；Event 的 `event_multi_wait_set` 是有序数组成员集合的派生视图。
`instances` 仍须保留源码数组顺序/重复信息。`PendType` 保留为单等待/mask 接口，不能把
所有 Multi 状态投影为互斥枚举，也不能以局部字段关系替代完整的双向登记/ready 保持。

`task_stack.v` 已实现 `TaskStackLease`、创建/存活实例绑定、完整缓冲区的 QCP 数组表示，
以及 `store_parked_stacks` 的 park/take/switch 接口。lease 复用既有 allocation generation，
只描述 stack region/slot/generation，不是不可伪造权限，也不复制 TCB 的 pointer/size。
当前仍需连接完整的运行/发布/回收协议，尤其 Flag 栈上 node 和 Multi 借用数组：
它们的字节若已由其他模块持有，就不能同时放入整栈 `mixed_full`；`None` 仍是 undef
单元所有权，不表示被借走的洞。栈 extent、当前字节及真实 residual 必须由实际资源运输。
`TaskRetirement` 区分仍在活跃链
但已去就绪/等待、已解绑回收但 current cache 尚未切换、以及原 invocation 已终止的不同阶段。
private creation 沿用既有 `TaskCreationEntry`，不把所有这些情况塞进一个 initializing bool。

Flag 栈节点的字节借还接口现位于 `flag_stack.v`：8/16/32-bit Flag 的节点分别为
20/20/24 字节，即 5/5/6 个 32-bit 字。`task_stack_storage_split_region` /
`task_stack_storage_merge_region` 直接复用 QCP 的数组拆合，仅保留前后两段实际资源，
不保留旧中段 image 或用 None 假装资源洞。`kernel_resources.v` 的类型桥接复用
`StoreAux` 与字节表示，补齐所选 Arch32 的 UInt/Ptr 及异构字节组合；它们不证明
局部对象 provenance。`flag_node_borrow_stack_region_uninit` 只交出未初始化字段与
原栈 residual，六次实际 store 完成前不能得到初始化 node。返回接口消费当前实体节点
和同一 residual，保留四个 pointer 字及独立的 32-bit flags 字，其余尾字只遗忘值、不丢资源。
这不是把节点恢复成借出前的内容，也不宣称所有内核配置均已验证。

实际调用顺序还需完整接入：`OS_FlagBlock` 在六次节点 store 之前，就于
`os_flag.c:1104` 将 pnode 写入 TCB backlink。因此栈借出必须先于这次首次可达写入，
初始化和邻接/ready 更新期间使用临界区内的临时资源；不能等 group head 写入才借出，
也不能提前闭合全局不变式。`OSFlagPost` 和 `OSFlagDel` 在 `OS_FlagTaskRdy` 摘链后
仍继续读 node->Next，因此 loan 先回到直接调用者，完成读取后才能归还原任务栈。
原调用、真实 &node、栈区间与 residual 的身份对应不能由纯 invocation 编号产生。
abort 的再次 unlink 按既有修复变体处理，不因资源重组而宣称原版路径正确。
`flag/spec/flag_block_spec.v` 已完成联合端点、精确字段/frame 及 Task/Sched/Flag
三模块有效性的 15 条引理，并通过完整固定检查。parked-map 的真实片段组合已接入当前
模型，完整跨模块保持和调用级物理资源重组仍需实现；这些字节/端点规则不是完整 OSFlagPend 或
平台栈帧协议的验证结果。

停放栈全局化采用同一 Task 状态归属，不再增加平行的“补充字段”record：将已有
region/map 的纯类型移入 `TaskStateDef`，在 `Glob_TaskAbstractState` 直接保存停放片段表，
空间谓词仍在 `task_stack.v`，并在 `UCOS2_raw_rep` 中单独合取，不暗中塞入 TCB
`task_public_storage`。执行中的栈、未发布 Create buffer 和原调用续体继续显式传递。
片段保存 `(lo, hi, 当前字列表)`，直接复用 QCP `UIntArray.mixed_seg`；完整栈嵌入
`[(0, region.words, words)]`，保留现有完整-buffer 规则的长度约束，而不是把长度改成
`Zlength words` 后削弱原 take 的覆盖结论。几何合法性要求范围内、排序、不重叠；
真正整栈覆盖另需与 Flag/Multi 实体借用资源组成分区，不能从空表或任意 EX map 得到。
上述类型、直接字段 `parkedTaskStacks`、更新器 frame、boot 空表和全局拆合现已实现；
Create/切换的资源端点回写实际 Task 字段，Flag 两侧 residual 与片段表示建立双向等价。
`UCOS2_state_inv` 同时要求已登记片段的范围/排序和 publication/live-instance 对应；
Task 的私有 allocation 尚未出现在 publication history 这一性质并入既有
`task_generation_closure`，由实际 detach/commit/recycle 保持，不能凭新公理断言 key 空闲。
当前独立模型集成检查状态见 foundation。Create/切换的资源端点还不是完整全局端点：
后续须从同一个旧不变式拆出 map 一次，再消费更新后的 map 合回；不能另加一份 map
到完整旧 `UCOS2_inv` 上。保存帧覆盖、恢复资格、调用续体与完整资源分区仍需实现。

当前 ARMv7-A 的实际 `OSTaskStkInit`（`Ports/ARM-Cortex-A/ARMv7-A/os_cpu_c.c:389`）
忽略 opt；先对 ptos+1 向下作8字节对齐，再逐字压入PC、LR、通用寄存器/参数和CPSR。
是否增加FP帧来自链接的 `OS_CPU_ARM_DRegCntGet`，不是旧注释中的 opt 位：返回0/16/32
时分别写16/50/82个32位字。当前 GNU ABI 选择不等于已经选定其中一个VFP链接实例，
后续契约必须显式绑定它。接口继续作为已批准的外部平台契约，不宣称证明了汇编/ARM执行。
TCBInit失败66发生在栈初始化之后，Create只回滚priority，不恢复旧栈image；调用者应取回
实际初始化后的buffer。成功路径则必须在首次发布前将初始栈交给Task/调度协议，因为
新任务可能在Create返回前运行并修改栈；不能把初始frame作为caller私有资源保持到返回。
基本版Create向TCBInit传入的bottom/size均为零，实际栈extent必须从创建前的资源契约
运输，不能从这些TCB字段反推；Ext清栈后，StackInit的未写区域保持性相对清栈后的image。
StackInit本身不解引用p_arg，写帧契约不新增源码没有的NULL检查；任务真正开始执行时
所需的合法代码入口/参数资源由任务入口契约另行绑定。

Task/Scheduler 的全部函数映射见 [API 清单](ucos2-v2.93.01-model-api-map.md)；以上是全操作族的
目标接口，不能把已完成的部分当成整族完成。具体已实现/检查范围见
[实施记录](ucos2-v2.93.01-model-foundation.md)。

## 5. Event、Mutex、Sem、Mbox 与 Queue

### 5.1 Event 共同层

扩展现有 `Glob_EventAbstractState`，共同持有有限 Event 池、free 链、published 对象及创建中的
private Event；保留原始 type/pointer/count/group/table/name image。稳定 payload 采用带标签的
解释，确保 Sem/Mutex/Mbox/Queue 只有对应内容有效；旧 `FlagFields.flag_dummy` 已移除，
真实 Flag 资源由独立的组池和等待节点模型持有。
若为兼容保留多个 `option` 字段，其排他与 type 对应必须由统一关系证明，不给每个函数不同解释。

当前实现把 ECB 字节、池分区和分配身份放在 `lib/event_pool.v`，payload、Task 相关位图编码及
共同操作的组合留在 `lib/event.v`。`EventLifecycleState` 只保留 free image、private allocation
和两个新鲜身份计数器；private allocation 内保存 origin/invocation/generation，不另外复制
一张 invocation 表或无消费者的 publication 历史。`eventPrivateQueue` 仅记录同一调用已摘取
的可选 QCB：初始为 None，QCB pop 后为 Some qid，ECB 私有写入保留它，发布时随 private
allocation 一起移除；不再增加第二张 Queue owner 表或另一套代际计数器。身份是 ghost，
不代替实际字节权限，也不
自动保证旧 C 指针安全。发布必须把当前 allocation generation 和已初始化 image 接到新 payload。

`event_in_range` 已采用 used/private/free 三分区、free-link/type 一致性和身份有效性；
native raw 表示拥有完整的当前 20-byte ECB（含 padding），私有字节留在调用者的独占资源中。
可选 Name 的 24-byte 局部布局不等于 names-enabled 全局池配置已完成。历史 `verification_slice_event_in_range`
仍只服务尚未迁移的旧切片，不能用其两分区条件替代 native 生命周期。字段拆合统一适配 QCP
`store_map`/`store_map_missing_i`，不另建递归分离合取库。

`waitList` 必须与位图、Task 实例和实际等待登记对应，不仅是 TaskID 的任意 list。提供：

- `event_wait_bitmap_rep`、`event_waiter_registered`、`event_waiters_encode_bitmap`，按 Task 当前
  native priority/cache 所处阶段编码；同一个 waiter 的名字、表索引与指针必须可运输。
- `event_wait_select_highest` 精确解释 OSUnMapTbl 查找与 `OSTCBPrioTbl[prio]`，证明选中的是
  该 Event 的真正 waiter，不从一个任意 Task existential 关闭 wake 目标。
- `event_wait_register/remove/wake` 是不同动作：登记还移除 ready；wake 清 delay/pend bits、
  设置结果/消息，尊重 suspension，并在 Multi 场景从整组 Event 移除。timeout 后可能尚有
  bitmap/指针残留，使用 cleanup-pending 阶段而非与 `stat.pendType` 的无条件等价。
- used/free/private 的 split/updated-merge、删除循环已处理前缀/剩余 waiter 以及回收后的
  object generation/continuation 接口。C 的 `OSEventPtr` 在 free Event 上是 free-list link，
  不再按某种 active payload 解释。

当前单 Event、8 行位图实例已实现 `event_wait_priority` 与真实 priority-table lookup，
复用 Scheduler 既有最小置位位/排序定理，证明选中 canonical wait-list 的首项及其真实 TCB。
`event_task_rdy` 组合该读取与 `event_wake_state`；其 `None` 表示无法取得模型中的
live 对象/TCB，不是源码新增的错误返回。Task 前缀精确写 Dly/Msg/Stat/StatPend，EventPtr 的清零
仍属于后继 Remove；唤醒保留 suspension、已经 ready 的 timeout-linked 情况和未刷新物理缓存。
单 Event 原始端点使用 `sched_wake_by_status`，严格按源码只测试 suspension 位，
不以内置的完整 ready 条件排除残余 pending 位。普通单等待的保持证明从已有 Event/Task
登记关系取得实际等待阶段，再证明此处两种测试等价；全局消费者没有新增公开输入限制。
Event 移除及 Task/事件引用、Flag 互斥登记、Mutex alias/owner/PCP 等跨模块保持在本轮字段/接口
重构前已通过完整模型检查，没有把“更新后的整个状态有效”作为调用前提。窄位图的行清位/条件组清位已抽成 Scheduler
共享 OR 编码定理，复用 QCP 的整数截断引理；`event_remove_waiter_image_eq` 将逻辑删除
接到选定数值 ABI 下的 ECB 写后 image，保留其他字段、Name 与 padding。逐 store 的字段拆合
使用 QCP `store_map` adapter，原始 Event map residual 排除被更新对象，随后合回新 Event。
Queue owner 另证等待列表更新保留 QCB、实际 buffer 字节、发布绑定和 used/private/free 分区。
`UCOS2_inv_merge_event_wake_storage` 在本轮重构前已通过完整全局模型及当时依赖检查，消费真实的
写后 Task/Scheduler/ECB 资源并恢复既有全局不变式，未聚焦模块保持在 residual 中；不从纯
有效性生成堆权限。

与唤醒配对的单 Event 等待登记也已接通当前全局模型。`task_prepare_event_wait` 只包含 Pend
调用者的 Stat OR、StatPend=OK、Dly 三次写入；`event_wait_state` 接续 EventPtr 写入、
Event 行/组 OR 和 ready 行/条件组清位，保留 current/high-ready 物理缓存。源码顺序等式将
组合端点与先更新 TCB、再进入 helper 的两个阶段连接起来，不在 helper 入口强求已经恢复
完整 Scheduler 稳态。`event_insert_waiter` 的 remove/insert 只规范化逻辑集合，已证对应 OR
置位的幂等效果；优先级未变时新旧 Task 下标产生同一插入结果。

OR 不会删除原有等待位：单 Event 的精确 linked phase 必须从 Pend 前的 ready membership
及 Scheduler 有效性推出原等待位为空，再应用 `task_prepare_event_wait_pending_bits`。
该来源保留在全局 Pend 重组接口中，不在 raw transformer 增加状态过滤，也不把 OR 改成赋值。

`event_wait_resource_unavailable` 是 caller 的资源观察：Sem=0、Mbox 空、Queue 空或 Mutex
已占用，不是 helper 新增的 guard。新登记的原 TCB 无 Event/Flag 挂接、目标 Mutex 不由自己
持有等协议事实，与 Task/位图/双向引用保持分别处理。`UCOS2_inv_merge_event_pend_storage`
消费实际写后的 TCB、ready 和 ECB image，利用 QCP-backed 字段/map/数组接口恢复既有全局
不变式，并保持 Queue buffer 与其他 owner。相关正式模型及 `atomic_ops_lib.v` 在本轮重构前
已通过固定工具完整依赖检查（2026-09-10）。旧 `atomic_event_task_wait_kind` 已改用此组合，删除重复
record 构造、提前刷新 high-ready 缓存及保留旧 StatPend 的偏差；没有修改 C 实现。

完整阻塞续体、符号 C 字段地址/配置桥接、Multi/宽位图实例、其余操作族及旧 Pend proof
迁移仍是未完工作，不把这些模型定理当作全部 IPC 函数已验证。单等待的 mask/登记保持
定理仍有其适用域，不能直接充当 Multi 的整组登记和跨调度协议。

EventMulti 使用有顺序且 NULL 终止的输入 Event 数组；输出的 ready Event 数组和 message 数组
各有精确写前缀/未写后缀。扫描会取得所有当时可用的 Sem/Mbox/Queue 资源，不是“任取一个”。
阻塞分支才登记 Multi wait-set；唤醒后的单一结果与立即扫描得到的多项结果分别建模。
重复 Event 指针不能默默当成 `NoDup` 输入：按实际扫描/登记语义处理，必要协议条件单独说明。
`events_rdy_nbr` 是 `INT16U`，返回计数按模 65536 累积；输出指针的真实推进/写入前缀长度
与该窄计数分别记录。是否进入等待由独立的 `events_rdy` 布尔量判断，不能用返回计数非零
替代。该边界来自 `os_core.c` 的声明和逐资源 `++`，不凭空增加输入数组长度检查。

`event_wait.v` 的 `event_multi_wait_mask` 已表达 unavailable 类型的 OR 累积，并证明
append/重复项幂等、0..7 范围与非空时非零；`event_multi_prepare_wait_image` 将它接到
Stat/StatPend/Dly 前缀，保持其他已有 image 字段。这里是 Sem/Mbox/Q 均启用时的类型
实例，disabled primitive 必须遵循实际编译 guard。该计算不代替扫描中的资源取得、输出
写入或整个 PendMulti API，也不把有序数组替换成集合或以首个 Event 地址冒充数组地址。

`event_multi.v` 复用 QCP `PtrArray.full/missing_i` 表示真实基址上的 NULL 终止借用数组，
给出读出/归还、终止位置、下一索引界和减小量；`Forall2_nth_iff` 连接数组元素与 live Event
的 `(slot, generation)`。Task 的两项条件字段使用真实 C 字段地址，局部切片现已通过
`event_multi_borrowed_array_split_tcb/merge_tcb` 接到完整 72 字节局部 TCB；唤醒后
MultiPtr 已清零时，原借用数组仍由调用续体保留。跨调度的存活/rely 不是这些局部资源引理的结论。

整组登记/清理分别保留输入顺序的逻辑循环和 byte-image 循环。它们复用单 Event 的 OR/AND
写入及 QCP map/字段重组，证明与整组 endpoint 相同；重复指针通过登记/删除幂等处理，
清位还覆盖 Task 已不在该 Event 等待表中的情况。`event_used_images` 只是已有 Event
状态的投影，不是第二张存储表。`atomic_event_task_remove_multi` 保持所有非 Event 状态；
`atomic_event_multi_register_events` 仅对应 WaitMulti 中的 Event 循环，不含此前的两个 TCB
指针写入和之后的 ready 清除。`atomic_event_task_wait_multi` 则将这三部分接到同一全局
状态；`atomic_event_task_wake_multi` 对应已选定 Task 且 MultiPtr 非 NULL 的 wake 后缀，
组合 canonical Task、selected::原数组顺序摘链和仅按 suspension 的 ready 更新，不刷新
物理调度缓存。其字段对应、全组摘链及 Task/ready 结构保持与完整协议有效性明确区分。
当前位图定理针对既有数值 ECB 布局及 8 行 8-bit 位图；完整 Multi-enabled 全局协议、
发布/回收与数组借用、宽位图和 PendMulti 整体观察仍须接入。
`event_multi_wait_step` 现组合当前 Task 的两个指针写入、Event 循环与最后的 ready 清除，
保留所有 common TCB 字段和调度缓存；image-loop 对应要求实际读出的 TCB row/bit 与
priority 编码一致。`event_multi_wait_set` 记录该 Task 在整个 Event map 中的成员关系，
登记建立和整组清理均有接口。`event_multi_wake_selected_step` 只表示已完成真实选择且
MultiPtr 非 NULL 的后缀，保留 selected Event 首次 Remove 再遍历原数组的顺序，以及
写后 status 的 suspension 测试；不冒充整个 selector 或跨调度 continuation 的完成证明。

### 5.2 Mutex

复用 `MutexFields`、`mutex.v` 与已绑定的 `mutex_priority_spec.v`，细分三种信息：
`pcp`，当前 owner 的 Task 实例，以及 `OSEventCnt` low-byte 的实际保存优先级。
base/effective priority 和 priority-table aliases 由真实实现 variant 的解码/查找关系给出，
不能把 low byte 在所有阶段都当作 owner 当前 priority。

模型不另拥有 TCB、ready bitmap 或 priority table；由以下纯关系连接它们：

- `mutex_owner_live`、`mutex_pcp_slot_consistent`、`mutex_owner_priority_aliases`；enabled PCP 与
  `OS_PRIO_MUTEX_CEIL_DIS` 分开，永久/base slot 与提升后的 alias 来源可追踪。
- 所选 [nested-priority 变体](../source_variants/mutex-nested-priority/README.md) 的具体关系是：
  每个 live Task 有一个 permanent slot；额外别名只能是本 Task 拥有的 live Mutex 的更小编号
  enabled PCP。`mutex_base_priority` 为全部实际匹配 table slots 的最大值，稳定阶段 effective
  priority 为其最小值。获取新锁时的 count low byte 仍只是当时 current priority 的快照。
- `mutex_inheritance_recorded` 记录真实 qualifying Pend 留下的 PCP alias，包括已被更高提升
  掩盖的 demand；它不是“所有持锁”的集合，也不是“当前 waiter”的函数。timeout 不直接撤销
  alias，修改 waiter priority 不会重跑 promotion。Post 先把自己的 PCP 设 reserved，Delete
  先设 free，然后在剩余 actual slots 求 min；不按 LIFO 假定，也不改成沿旧 low byte 恢复。
- 已选 owner 协议要求持锁者不进入其他 Event 的阻塞等待、不在持锁期间被 ChangePrio 或
  Delete；允许获取立即可用的其他 Mutex，允许 suspended/non-ready owner 的 NO_PEND 删除。
  这些是合法客户端协议，不是 C 中新增的检查；不把它扩写为“只能持有一把锁”。`mutex_priority`
  helpers 的 raw max/min 观察证明不能独自建立 permanent slot、别名来源或协议保持。
- release→priority restore→wake/handover→Event/slot recycle 是 source-ordered 阶段关系；
  当前 owner、唤醒者、位图 owner 和下一 owner 不随意互换。每一更新点保留正确的旧值/新值。

public spec 区分 Accept 的 bool/错误码、Pend 阻塞结果、Post 的 owner/PCP 分支、Delete 的
NO_PEND/ALWAYS 与输出、Query 的 snapshot。原始源码已发现的问题和已批准修复保持不同
source-bound relations，不借新 invariant 声称原版错误路径已正确。

### 5.3 Semaphore 与 Mailbox

Sem 的稳定 payload 是 `count : Z`，范围 `0..65535`；Event waiter 登记为共同层所有。
Accept/Pend 的立即取得在 count>0 时减一；Post 在有 waiter 时 wake，否则增加 count，65535 时保持
不变并返回 overflow；Set 的 waiter/count 条件按真实源码单独定义。不能规定“只要 count
为 0 就必有 waiter”，也不能由一般 counted sem 导出二值锁协议。

Mbox 的稳定 payload 是 `None | Some message_addr`；empty、stored message 与直接递交 waiter
分开。Create 允许空或初始消息；Post/PostOpt 在有 waiter 时更新 Task.msg，不先存再取；无 waiter
时只在空 mailbox 写入，已有消息返回 full。广播是多个 Task 接收同一指针值，不推导这些 Task
各获得一份独占消息内容。PendAbort 与 Delete 复用 Event wake/cleanup，具体返回数量/错误码不混同。

两者的 Query/NameGet 在临界区取得 snapshot，输出值与那个观察点绑定；恢复后全局状态可以
变化，不能要求输出永远等于函数返回时整个内核状态。输出结构的字段和 padding 依据实际写集合。
Sem/Mbox/Queue 的 PendAbort 采用 `switch(opt)`：仅 `opt=OS_PEND_OPT_BROADCAST` 时广播，
其他值走单个 abort；不要与 PostOpt 的 bit test 混淆，也不生成不存在的 invalid-option 错误。
这三个源码同构的 critical 部分现共用
`VC/code_proof/event/spec/event_pend_abort_spec.v`，各模块 `spec/*_pend_abort_spec.v`
只绑定实际 type/mask。共同前缀保留 safety、条件参数检查及无条件 type 读取的顺序，
不增加 ISR/lock 拒绝。广播复用 `event_wake_spec.v` 的实际 bitmap/table 选择与有限循环。
计数使用 CompCert `Byte` 的真实 8 位窄化，已给出零值、每次递增和前缀追加接口；
当前全局 Task 池上界推出最多 22 个 waiter，从而当前配置的返回计数等于实际 abort 数。
共享结论包含无等待者零/NONE、非空 PEND_ABORT、精确 waiter/非 waiter TCB、Event payload
及 Queue buffer 保持、原 invocation 身份运输和真实写后堆的全局重组。abort 数不等于
新 ready 数，suspension 按源码保留。结果中的调度请求不是 OS_Sched 已返回，perr 写入
仍在 Restore/调度返回之后组合；旧 Sem slice spec/manual 尚未迁移，不继承其 acceptance。
SemSet 在当前 count>0 时直接写新 count，再考虑零 count 的 waiter 情形；不能替换成“有 waiter
一律拒绝”的新语义。MutexAccept 的 PCP_LOWER 错误码也不等于未获取 mutex，应绑定实际效果。

共享计数操作位于 `lib/sem.v`，沿用 Event-owned `SemFields`，不增加 Sem map 或新的
抽象字段。`sem_set_count` 只改变 count；原值/末次写入、计数增减保持和完整 native Event
保持分别提供接口。物理拆合直接实例化 Event 的 QCP FieldStorage：只更新 EventCntField，
保留同一对象的 type/ptr/wait/name/padding，原值 merge 和更新 merge 不混用。
全局 payload 更新桥运输 Task/Sched/Mutex 及其他所有模块，Event owner 必须先证明其
新状态合法；计数重组消费实际新 UShort cell，不用新的 whole-global 前提替代该证明。
未修改的 Queue 也通过其真实 Event-indexed storage 运输，不因操作名为 Sem 就忽略它。
`sem/spec/sem_accept_spec.v`、`sem_set_spec.v`、`sem_post_spec.v` 提供各自临界区端点。
Accept 返回旧 count，而非 boolean；Set 按 count-first/bitmap-second 执行，perr 先写
NONE，只有拒绝分支改写 TASK_WAITING，均在 Restore 前。Set 端点的 OSErrCode 是 perr
的最终观察，不是把原 C 函数的 void 返回改成错误码返回。Post 优先使用实际 bitmap/table
唤醒一个 waiter，参数为 NULL/PendSem/PendOK，不同时增加 count；否则增一或返回 SEM_OVF。
其调度位只表示后续调用 OS_Sched，不能推出新 ready 数为一或原调用已经返回。
存在性、确定性、全局保持、错误帧、invocation 和写后资源重组的实际检查见 foundation；
原 `lib/sem_*_spec.v` 与旧 manual 留待最终迁移，入口身份、trace/Save/Restore、perr 与
调度续体、Multi/其他配置以及剩余操作族仍属未完成范围。

`sem/spec/sem_pend_spec.v` 进一步将 Pend 分成首个临界区与返回临界区：前者按实际
count>0 减一，否则复用 Event 的准备/登记端点；后者按真实 StatPend 的 OK/ABORT/
TO/default 分支观察 perr。原调用的身份与返回时的 current/ready 边界独立于核心全局
不变式，不能从 OS_Sched 的函数名推导恢复运行，也不把相同 TCB slot 当成相同 generation。
等待域保留官方 non-idle 调用协议；ready 索引包括 idle，不能据此推导非 idle。
共享 `task_event_pend_cleanup` / `tcb_event_pend_cleanup_image` 按真实源码族
选择是否清空消息字段：Sem 不写 Msg，Queue 写 NULL；二者均不写 Dly/ready/cache。
该参数不是新增内核字段或运行时 guard，物理 image 保留 Stat/StatPend/EventPtr/条件
Multi/可选 Msg 的实际顺序。原 Queue 专用接口保持 statement，转用公共保持性证明。
timeout 通过已有 TCB EventPtr、reference closure 和 backlink 得到 live Event 与登记，
Remove 后再清理；OK/abort 不需要旧 Event 仍存活。全局 merge 消费真实写后的 TCB/ECB
堆，运输原 Scheduler 字节、Event 编码的 Task index 及完整其他模块 residual；不能从
纯端点产生内存资源。立即分支的 perr 写入位于 Restore 后，返回分支则在 Restore 前，
其完整调用/输出资源连接与 Multi-enabled 全局实例仍待组合；模型证据见 foundation。

SemDel/MboxDel 的同构 native 删除主体位于 `event/spec/event_delete_spec.v`，两模块的
`spec/*_delete_spec.v` 只绑定实际 type/mask。共同入口观察按 safety、IEC runtime、参数、
ENTER trace、type、ISR 顺序保留；Queue 仅复用这些入口观察，QCB/buffer 回收仍为独立模型。
NO_PEND 有 waiter 时返回原句柄/TASK_WAITING，不改状态；ALWAYS 逐次使用当前位图
和真实 abort 端点，随后将 ECB 的 Type/Ptr/Cnt 与 free-root 按源码回收。未知 opt 保留
INVALID_OPT；成功 NULL，调度请求取循环前的等待观察，而不是最终空位图或新 ready 数。
所有 perr/trace 与可能的调度返回仍在 Restore 后组合。Mbox 覆盖原消息指针不调用 free，
Sem count 清零也不能推导应用资源已经释放。
`queue_storage_event_entry_frame` 复用 QCP 的 store_map 拆合，证明无 Queue
payload 的 Event 项插入/替换/移除不改变真实 QCB、buffer 和 private Queue 归属。
Event owner 的 `non_queue_event_has_no_queue_fields` 从类型与现有字段一致性给出该
payload 事实，不增加公有函数前提或运行时 guard。全局回收以既有 backlink/reference
closure 和空 wait list 排除悬垂 TCB 引用，消费真实 Type/Ptr/Cnt/free-root 写后堆。
ECB-only 规则明确排除 Mutex 的优先级所有权协议；完整资源重组也不允许忘掉 Queue
的额外 owner。上述组合仍绑定当前 names-disabled native profile，完整调用/输出与
其他配置待补，不能直接记为 Sem/Mbox C 函数已验证；证据见 foundation。

SemCreate/MboxCreate 共同阶段位于 `event/spec/event_create_spec.v`：IEC flag 与 ISR 是
按源码时刻取得的入口观察；Save 内只摘取实际 free-head，Restore 后才写 Type/Cnt/Ptr、
条件 Name、Grp 与 table rows。不存在 scheduler-lock 拒绝或 perr 输出。源序字段序列
用既有 `event_private_write` 更新本次 allocation，不额外增加 OS 状态字段；
缺 private lookup 表示规约不适用，不是偷偷插入的 C guard。等待表循环的 prefix/step/
frame 与当前八行 UChar 写后合回在 Event owner，实例化既有 QCP FieldStorage，不能
将 typed loop 改写成 OS_MemClr 或假定 padding 已经初始化。
空闲摘取将真实 ECB 字节交给本 invocation，全局保留其他池/模块；private 字段更新只
修改该 image，公有 Event map、QCB bytes 和 Task/Sched 保持。发布是完成初始化后的
资源交接，不是新增 C store。共享全局接口由旧 reference closure 证明 private slot
没有 live TCB 回指，再建立空 wait list 新 Event 的关系；Mutex/table 的运输与等待关系
分开，沿用原更新/回收 wrapper 的 statement。Queue 的 map-entry frame 保留全部
QCB/buffer，并要求本 allocation 未另外占用 QCB，不能默默丢失私有 Queue 资源。
发布的物理匹配现在按 `event_fields false` 中真实字段逐一比较：关闭名称功能
时不要求 nonexistent Name 单元已写入，真实 padding 仍须逐字节保留。原 exact-image
接口委托该 extensional 规则，旧 Queue 模型可继续调用原签名。Sem/Mbox 绑定分别保存
INT16U count/NULL pointer 与 count0/任意消息；NULL 消息使用既有 Mbox 编码，不转移
应用消息内容。当前 record 中未观察的 Name=0 不是写入，也不是 names-enabled 证明。
私有字段序列的模型/保持证明不等于跨 Restore 的完整环境闭包：实际 invocation 来源、
non-owner 干扰、trace/call 契约、何时对 caller 公开 handle、名称存活及其他配置仍待
与整调用组合。具体检查状态与证据见 foundation，旧 C/manual 迁移顺序保持不变。
Event 保护现通过 `event_creation_view` 过滤既有 private map，并由
`kernel_client_frames_event_creation` 运输原 allocation 的 invocation/origin/generation、
ECB image 与 QCB 关联。视图不是新的存储表。QCB image 参数属于调用者局部观察，buffer
继续使用普通分离 frame；对应 storage 等式仅用于重接同一资源谓词，不凭空产生堆字节。
实际分配、私有 store、Sem/Mbox 发布及 Queue 二次分配/发布均有独立 action certificate；
第一阶段还给出原 ECB 的 UNUSED 类型，供 Queue 耗尽回滚使用。Event invocation 来自
自己的计数器，不能与 Task 的 nat 编号认作同一调用。2026-09-29 的消费者审查确认：
`eventPrivateOrigin` 虽保存 boot 或 Task slot/generation，却仅被赋值、复制和投影，
没有协议检查消费它；不能将“保存了标签”描述成“已建立调用绑定”。该冗余字段及其
传递参数正在独立精简，Task 调用上下文、Event invocation 的资源 frame 和实际环境
空间足迹继续由原调用协议承担，不删除有实质用途的身份或权限。

### 5.4 Queue

当前 native 创建生命周期见 `queue/spec/q_create_lifecycle_spec.v`，与尚未迁移的历史
`q_create_spec.v` 切片分开；后者的语义与资源接口使用 `verification_slice_OSQCreate_sem`
和 `verification_slice_q_create_*`，不与当前创建生命周期混称。第一次 ECB pop 复用 Event 创建阶段；第二次 Save 才观察
当时的 QCB free list。成功时只摘取 QCB 并记录私有关联，耗尽时把仍为 UNUSED 的 ECB
接到当前 ECB 空闲链，既不还原早先快照，也不回退 generation/invocation 计数器。
UNUSED 从第一次分配和跨环境 frame 推出，不增加公开输入限制；真正更新过的 root/link
和私有 cell 由 QCP 拆合规则重组全局资源。初始化复用既有六次 QCB store 和共同 ECB
store 序列，发布消费实际完成的两种控制块及 caller buffer，保留未清零的 OSQPtr 和
未使用槽位。零容量仍有模型；正基址、INT16U 范围、区间/运算有定义是资源条件，不是
新造的 runtime guard。完整 Save/Restore、trace、实际公开 handle 时刻与其他配置的
整调用组合仍待完成，不能据此给历史 QCreate 或整个函数重新记验收。

继续保留 `QueueFields` 的 `qID/qStart/qSize/qInIndex/qOutIndex/qMessages` 和
`publishedQueueBytes`；QCB 使用 free/private/published 分区与生命周期。private 关联从既有
Event allocation 投影，仍使用原 invocation/generation，私有 QCB 字节不放入共享 heap。
分区要求合法 QCB 域穷尽、free NoDup、公私互斥及 private owner 唯一。Event 到 QCB
一对一绑定，QCB 索引与 Event 索引不是同一个 ID；QCB free link 与 Event free link 分别表示。

稳定 ring 关系（size>0）为：

```text
entries = length messages; 0 <= entries <= size
0 <= in_index,out_index < size
in_index = (out_index + entries) mod size
messages[j] = slots[(out_index+j) mod size]    (0 <= j < entries)
OSQEnd = start + size * sizeof(void*)
```

`slots` 有 size 项；占用位置有对应消息，其他位置保留实际旧值/未定值。全满与全空均可能
in=out，由 entries 区分。尾插、头插、出队及 wraparound 提供各自 `queue_*_preserves_ring`。
头插先回退 out 后写槽；读出/Flush 只改源码明确写的指针/count，不删除仍分配的槽存储。

源码 QCreate 不拒绝 size=0。其单独的零容量表示为 size=entries=0、messages/slots 为空、
Start=End=In=Out；不套用上述正容量取模公式。无 waiter 时 Post 返回 full，但等待后的 direct
handoff 仍按真实路径建模。源码也未检查 start=NULL；`&start[size]` 是否有定义由所选指针语义
和 caller buffer 契约决定，不能把“不检查”误称“所有 NULL/size 输入都安全”。

Queue 的 Post/PostFront/PostOpt 不检查消息为 NULL，与 Mbox 的 NULL-message 拒绝不同。
因此队列元素域包含地址 0，`Some 0` 与未定存储 `None` 不同；success+NULL 与 empty/timeout+NULL
必须通过 perr/返回分支区分。不得从 `messages` 的元素直接推出非 NULL 或消息内容权限。

QCreate：Event 摘取、QCB 摘取/失败回滚、buffer 建立、发布分别给精确阶段；调用者给定 buffer
的 extent、可写权限与存活期不能由非 NULL 自动得到。QDelete 回收 Event/QCB 后，归还 buffer
的权限并关闭旧实例 continuation；源码不调用 allocator，因此不能声称它物理释放了 buffer。
Post/Front/PostOpt 优先走真实 waiter handoff，只有无 waiter 才改 ring；广播/NO_SCHED 的位测试
和没有显式拒绝的 option bits按源码处理，不能添加一个不存在的严格 enum 检查。

QCB 的七字段表示复用 `FieldStorage`/QCP `store_map`，24-byte 数值布局另有完整 byte inventory；
它不自动证明与 QCP 符号字段地址相等，仍消费已有 `queue_table_layout_prop` ABI 接口。
创建初始化按 Start/End/In/Out/Size/Entries 六次源码写入组织，保留未写的 OSQPtr。
摘取后的重组消费已更新的 free-root cell；发布重组消费实际 QCB 与 caller buffer，分别接回
Event 和 Queue 表示。空闲时未知的字段值不被虚构为零，空队列允许保留 caller buffer 的旧字节。
删除尾部也有联合重组：从已发布对象拆出 QCB/ring，residual 排除被删节点，消费实际更新后的
两个 free roots 和回收字段，再把原 `PtrArray.mixed_full` 权限交回 caller。QCB 只改 OSQPtr，
其余字段和 buffer 字节保持；删除 buffer 登记不表示调用 allocator 或清除消息内容。

环操作现已连接逻辑 FIFO、实际 slots 和 QCB 字段：尾插/头插只更新对应的一个槽，出队与
Flush 保留原 buffer 字节；队头可从 QCP `PtrArray` 拆出实际指针单元，包括合法 NULL 消息。
QCB 更新保留各源码写入顺序及回绕前的一过尾指针；`OSQPost` 的 count-before-wrap 与
`OSQPostOpt` 的 wrap-before-count 分别建模并证明字段后态相等。成功分支的 UShort count
增减范围另证，未写字段保持，不要求每个中间 image 都满足稳定 ring 等式。
同 QID 更新通过 `queue_update` 同步 canonical payload 与 `publishedQueueBytes`，
已证明 Event 有效性、Queue 分区/绑定保持、其他队列 residual 的双向运输及共享资源重组；
ECB 字节不因逻辑 FIFO 更新而发生虚构写入。重组消费已写后的真实 cells，不代替 C store。
直接复用 Event owner 的 `queue_fields_consistency`；旧 `queue_fields_consistency_total` 兼容名已删除。
整状态组合现使用 `cross_module_consistency_event_fields_update` 运输未修改的
kind/Mutex/waiter 关系，不为 Queue 复制 Task/Mutex 更新。全局的 Event/Queue 双向拆分
和 `UCOS2_inv_merge_queue_update` 将既有 QCB/ring 写后资源接回全部非目标
模块；same-QID 的 ECB image 保持直接复用 Queue owner 引理。Flush 的全局有效性从
原 payload 的 ring consistency 推出，允许零容量、有等待登记和残留 buffer 字节。
这些接口不把 pure validity 当成 Queue buffer 的所有权，完整调用的参数检查与
Save/Restore 仍由各函数规约组合。
Post 家族的函数级组合位于 `VC/code_proof/queue/spec/q_post_spec.v`，不在共享库复制
Queue 状态。参数 NULL 检查、ENTER trace、无条件 type 检查与 Save 后临界区分别保留；
`q_post_critical` 按实际 EventGrp 分支，优先唤醒，只有无等待者才检查 full 并入队。
Event owner 的 `encode_event_wait_grp_zero_iff_empty` 复用已有 Scheduler head-bit 引理，
从 canonical bitmap 推出空列表，而非直接将 C 条件替换为未经证明的列表条件。
广播逐次调用实际 bitmap/table 选择端点；有限执行存在、唯一性、迭代次数等于初始等待者
数量、最终等待列表为空、每个初始等待者收到原消息及非等待者 TCB 不变均有对应定理。
这套证明现提取到 Event 共同的 `event_wake_spec.v`，以实际 kind/message/result 参数化；
Post 保留既有观察定理 statement，并实例化共享证明，PendAbort 不复制另一套广播归纳。
Queue payload/实际 buffer 字节保持，完整 Task/Sched/Event residual 逐步运输；这里不
把 pure loop trace 当作 TCB/ready/ECB 写后的空间资源。入队复用 QCB/slot 更新及全局
重组接口，保留 Post 与 PostOpt 的不同写入顺序、合法 NULL 消息和未知 option bits。
返回二元组的布尔值精确表示源码随后是否调用 OS_Sched：仅唤醒分支且未设置 NO_SCHED
才请求调用；它不是“已经切换”或“必定返回”。这些结论止于 Restore 之前，前缀读取的
对象身份、trace/Save/Restore 的调用组合、调度返回和 Multi-enabled 全局实例仍分别证明。
Pend 的首个临界区与返回临界区位于 `VC/code_proof/queue/spec/q_pend_spec.v`，分别使用
实际 `Entries > 0` 和 `StatPend` 分支，不把跨 OS_Sched 的整段调用折成原子操作。
立即取消息复用 FIFO/head-slot 与 QCB 更新，保留整个 buffer 的原字节；等待分支复用
单 Event 登记。清理精确写 Stat=0、StatPend=OK、EventPtr=0、条件 Multi 字段及 Msg=0，
不写 Dly/ready/cache，不能套用 Sem 的不同收尾。超时的 Event 存活及 waiter membership
由原指针、全局 reference closure/backlink 推出；成功/abort 不再读取 Event，允许它已被
Delete(ALWAYS) 回收。两段的确定性、全局有效性与原 invocation 存活保持有模型证明；
返回点的当前任务/ready 事实由已有 `sched_task_call_boundary` 接入，不由 OS_Sched 名称假定。
原生优先级索引包含 idle，而合法 Pend 的等待协议排除 idle。该区别有
[Micrium 手册 §3.08（印刷页98）](https://datasheet.octopart.com/KRN-K2XX-PKG000-P-P1-Micrium-datasheet-27615537.pdf#page=124)
的明确依据：idle hook 不得调用 Pend/延时/挂起服务。等待保持定理显式要求非 idle，
不把它加进 raw transformer；实际 caller/hook 遵约、原调用跨调度恢复与输出资源仍须组合证明。
各增量的实际检查范围见 [实施记录](ucos2-v2.93.01-model-foundation.md)；仍需完整唤醒/调度续体、阻塞恢复、公开 API
观察与配置实例，不能用局部资源定理替代 QCreate/OSQDel 或其他 Queue C 函数的完整证明。

Delete 的分段模型现位于 `VC/code_proof/queue/spec/q_delete_spec.v`。保留 safety/IEC
runtime、参数、trace、type/ISR 检查的实际顺序；critical 模型先观察 tasks_waiting，再按
NO_PEND/ALWAYS/invalid 分支。NO_PEND 拒绝真实 waiter，ALWAYS 实例化共享 abort 广播，
非法 option 保留原指针并返回 INVALID_OPT，不套用 PendAbort 的 default 语义。
回收复用 `queue_recycle`，按源码先 QCB 再 ECB，保留未写字段并注销 buffer binding。
`cross_module_consistency_event_transport` 统一 payload 更新与非 Mutex 删除的关系
运输，旧更新定理 statement 不变；空等待列表经既有 Task reference backlink 排除所有
残留 TCB 引用，不增加调用者的 unreferenced 假设。全局的
`UCOS2_inv_merge_queue_recycle` 消费实际写后的 pool/root 资源，重新建立全局不变式，
并把原 `PtrArray.mixed_full` 归还 caller；不是从纯转换产生堆或调用 free。
临界区的有效性、原 invocation、ALWAYS 的准确 abort TCB 及调度请求均单独证明；
调度条件来自最初的 tasks_waiting，不等于最终 bitmap 或新 ready 数。上述分段接口仍不
替代配置 names/Multi、平台/trace/Save/Restore、perr 与调度返回的完整函数组合。

Accept/Query 的临界区模型位于 `queue/spec/q_accept_spec.v` 与 `q_query_spec.v`。
Accept 复用 Pend 的立即出队操作：非空读取真实 head slot、更新 QCB、保留全部 buffer
字节；空为 NULL/Q_EMPTY，成功允许 NULL/NONE。`perr` 在 Restore 前写入，不能套用
PendAbort/Delete 的退出后输出顺序。两者共用的有效性与写后全局重组已归入
`UCOS2_queue_dequeue_preserves_validity` / `UCOS2_inv_merge_queue_dequeue`，
Pend 原接口保持不变。Query 则保留整个临界区内核状态，只有非空分支读取真实槽；
快照包含 group、全部当前配置 wait rows、head message、count/size，不推进 Out。
调用者的 `OS_Q_DATA` 写入与内核所有权分开：先 group，再按 `OS_PRIO` 逐元素复制
table，最后 message/count/size；不误当成 OS_MemCopy 或复制整个含填充的结构体。
输出谓词使用 QCP 符号字段地址，padding 留在外部 frame；循环沿用 `copy_prefix_list`
和 QCP mixed-array 的原值拆分、写后 merge，未复制后缀保留原值或未定字节。
这些接口绑定当前八行 UChar profile，不声称已经支持 wider OS_PRIO/Multi，亦未以
临界区快照等式代替 Restore 后环境干扰、输出存活期和整调用组合。检查范围见 foundation。

## 6. Flag：独立组池与栈节点

Owner 为新 `lib/flag.v`。采用以下 record 字段族，ID 为组池索引、node key 为真实栈地址：

| record | 字段与类型 |
|---|---|
| `FlagGroupState` | `flagGeneration : nat`；`flagBits : Z`；`flagName : addr`；`flagWaitOrder : list addr`。 |
| `FlagWaiterState` | `flagNodeAddr : addr`；`flagTask : TaskID`；`flagTaskGeneration : nat`；`flagInvocation : nat`；`flagGroup : FlagID`；`flagGroupGeneration : nat`；`flagMask : Z`；`flagWaitMode : FlagWaitMode`。 |
| `FlagWaitMode` | `FlagClearAll`、`FlagClearAny`、`FlagSetAll`、`FlagSetAny`，对应源码 0/1/2/3；consume 是原 Pend continuation 的 bool，不是 node 中不存在的字段。 |
| `GlobFlagState` | `flagUsed : FlagID -> option FlagGroupState`；`flagFree : list FlagID`；`flagWaitNodes : addr -> option FlagWaiterState`；free group raw image；next generation。解绑节点的 raw image/结果转入原 invocation，不再由 live wait-map 占有。 |

`store_flag_group` 拥有 type/wait-head/bits/可选 name；`store_flag_wait_node` 拥有 next/prev/TCB/
group/mask/mode 及布局填充。`store_flag_wait_list` 是 NULL 终止双链，头插顺序不是 priority 排序。
Task 的 `OSTCBFlagNode` 只是回指；所有已发布节点字节只由 Flag wait representation 占有一次。

`flag_pool_partition`、`flag_wait_nodes_unique`、`flag_task_wait_consistency` 要求：每个 live 节点
恰在一个 live 组的链上，对应一个存活 Task/原 invocation；其 mask 位宽正确、mode 合法；
Task 的 FLAG bit/timeout/result 与阶段一致。timeout 后尚未 unlink 的节点有独立阶段，不能
无条件要求每个链上 Task 仍保留 FLAG bit。

定义 `flag_ready_bits value mask mode`：SET 取 `value & mask`，CLR 取 `(~value mod 2^w) & mask`；
ALL 测试结果等于 mask，ANY 测试非 0。mask=0 对 ALL 成功、ANY 不成功，不能假设 mask 非零。
`flag_consume_bits` 在 SET 模式清收到的位，在 CLR 模式设收到的位。需保留三处时刻差异：

1. Accept/立即 Pend 在当前临界区满足时 consume；Accept 的 ALL 不满足分支仍返回算出的
   部分 `flags_rdy` 并写 NOT_RDY，不统一改成 0。
2. Post 修改 group bits 后扫描全部节点，TaskRdy 保存 flags/result 并 unlink；**不在 Post 中
   consume**。因此多个 waiter 可以被同一组位唤醒。
3. 阻塞 Pend 成功恢复后才按原 consume/mode 再修改 group bits；Post 会先调度、重新进入
   临界区读 `flags_cur` 再返回，不能把返回值固定为最初 OR/AND 后的值。

`flag_task_rdy` 已组合真实节点/TCB 选择、写后状态和源码 BOOLEAN 返回。
`flag_task_rdy_selects_waiter` 从有效 Flag 配置与既有 Task 回指关系推出 lookup/unlink
存在，并核对节点中实际 TCB 地址；`None` 不是新增 C 分支。返回测试是整个 Stat 字节为零，
由 `is_effectively_ready_zero_delay_eq` 与现有 Scheduler 更新接通；该等式覆盖全部状态字节，
不预先抹掉残余位。false 仍完成 TCB 写入及 unlink；true 表示执行 ready 写入，不保证旧位
原先为零（timeout-linked Task 可能已经 ready）。当前端点沿用 TaskDelete-enabled 的
FlagNode 清理 profile，其他布局/宏组合仍须各自绑定。共用 `flag_linked_node_unlink_exists`
替代删除规约中重复展开的查找证明；没有复制节点所有权、TCB 更新器或存储框架。

接口族：`flag_wait_list_split_node/merge_node`、`flag_link_waiter_preserves_partition`、
`flag_unlink_waiter_preserves_links`、`flag_wake_preserves_task_sched`、`flag_consume_in_range`，
以及原 invocation 的 `flag_wait_resume_resources`。原版 Unlink 不清 node next/prev；再次调用
不具幂等性，设计不能给它一个假的“任意重复 unlink 安全”定理，见源码反例章节。

## 7. 固定分区 Memory

Owner 为新 `lib/memory.v`。不是 heap allocator，也没有源码中的 coalesce、size classes 或 Delete API。

| record | 字段与类型 |
|---|---|
| `MemoryPartitionState` | `memBase : addr`、`memBlockSize : Z`、`memBlockCount : Z`、`memFreeBlocks : list Z`（块下标）、`memAllocatedBlocks`（有限集合/loan map）、`memName : addr`、partition instance identity。 |
| `MemoryBlockLoan` | partition instance、block index、loan generation、归还所需的线性资源身份；这些是 ghost，不是写入用户块的额外 header。 |
| `MemoryPrivatePartition` | MCB slot、原 raw MCB、caller buffer extent、链初始化已处理前缀与剩余原字节；原无实质消费者的 invocation 标签已删除。 |
| `GlobMemoryState` | `memPartitions : MemID -> option MemoryPartitionState`、`memFreeControls : list MemID`、private allocations、free MCB images；控制块全局 root/cell 与分区内 free root 属不同层。 |

块 i 的地址是 `base + i * block_size`，`0 <= i < nblocks`。pool owns free blocks 的全部存储，
其中第一个 pointer word 编码下一空闲块；allocated block 的全部用户字节由 loan 持有者拥有，
global 只记录其已分配身份。`OSMemNFree = length freeBlocks`，free 与 allocated 对全部块
穷尽互斥，无重复 free index；完整 buffer 范围不溢出、不重叠且满足每个 pointer store 的对齐。

Create 在临界区摘 MCB，Restore 后在调用者 buffer 建链并写 MCB，最后返回发布 handle。
private slot 必须跨 Restore 仍不可由其他用户 handle 到达。初始化循环用“已写 link 前缀 +
最后 link location + 原始未写后缀”，不把全部区间提前当已建立的 free-list。

Get 成功摘 free head、count--，把整个块和 loan 交给调用者；错误/no-free 不改变 pool。
Put 成功要求调用者交回该 partition 的尚未归还 loan 和可写块，写 link、入栈、count++。
`memory_block_loan` 必须是包含整块字节权限与分配关系的空间断言；仅一个可复制的 nat/record
或纯 map-membership 事实不能代表线性所有权，也不能防止在逻辑中重复归还。
源码只检查 NULL 与 count>=nblocks；合法使用协议提供 membership/唯一归还，不把它冒充运行时
防错功能。若要验证任意 wrong-partition/double-free 输入也不破坏池，需要另行修复实现。

Create 只检查 base alignment 和 `blksize >= sizeof(void*)`，不检查 block stride 对齐；正确
typed storage 的 stride/extent 条件在合法 buffer 契约中说明，不能伪造 INVALID_SIZE 分支。
Query 的 `OSNUsed` 在 Restore 后由已复制的 `OSNBlks-OSNFree` 计算，不重新读取 live pool。
NameSet 仅换指针，MCB free image 的默认 name 由 OS_MemInit 建立。

接口族：`store_memory_blocks_split/merge`、`memory_free_list_split_head`、
`memory_get_transfers_block`、`memory_put_restores_block`、`memory_create_establishes_partition`、
`memory_query_snapshot_used_count` 以及 private-control 的环境 frame。Transfer 定理同时改变
global partition 与 caller assertion，不能只证明一条 count 算术等式就称 Alloc/Free 正确。

## 8. Software Timer

Owner 为新 `lib/timer.v`；Timer 状态与内核 `TickState` 分离。

| record | 字段与类型 |
|---|---|
| `TimerObjectState` | instance generation；`timerDelay/Period/Match : Z`（u32）；`timerMode`（one-shot/periodic）；`timerState`（stopped/completed/running）；`timerCallback : addr`、`timerCallbackArg : addr`、`timerName : addr`；raw Next/Prev 由链/阶段解释。 |
| `TimerWheelState` | 长度为 wheel-size 的 spoke list，每项为按真实 next 顺序的 TimerID list；`OSTmrEntries` 等于该 list 长度，头/prev/next 为其具体编码。 |
| `TimerScanState` | 仅保存 time、缓存的 next `(TimerID, generation)` 和 remaining 链。spoke 从 time/config 导出，current 是本次 dispatch 参数，已执行调用和 invocation 由 trace/Task continuation 保留；remaining 长度是进展度量。它是 ghost/local 游标，不增加 C 存储。 |
| `GlobTimerState` | used map、free list/free raw images、Alloc→Create 的 transient slot、wheel、u32 timer time、u16 free/used counts、两个实际 Sem 指针、timer task identity、next generation。 |

`timer_pool_partition` 连接 used/free/transient 与 counts；`timer_wheel_membership` 要求稳定阶段
running iff 恰在一个 spoke，spoke=`match mod wheel_size`，stopped/completed 不在 wheel。
free timer 的 type 仍为 100，其他字段按 Init/Free 的真实写集合解释，不能要求所有字段是 0。
Link/Unlink 过程中 state、链、count 暂时不同步，局部阶段表示精确到对应写步骤。

`timer_link_delay` 取 delay 非 0 时的 delay，否则 period；`timer_link_periodic` 总取 period。
match=`(timerTime+delta) mod 2^32`，再取 spoke；Unlink 根据当前 match 计算 spoke。
RemainGet 在 running 时做 u32 减法，stopped 时根据 delay/mode 计算初始剩余量，completed 为 0；
不能把所有状态统一解释成数学时间轴上的 `expiry-now`。

Init 真正调用 `OSSemCreate(1)`、`OSSemCreate(0)`，分别存 `OSTmrSem`、`OSTmrSemSignal`。
前者在本版 `os_tmr.c` 只初始化/可选命名，API 的保护实际是 OSSchedLock/Unlock；两者的 Event
存储仍由 Event owner 持有。InitTask 消耗同一 Task 池，优先级 61；源码忽略其创建返回码，
完整 boot 建立要有资源/优先级足够的来源，失败不能被虚构成不存在的 OSInit 错误码。

Signal 原样返回 `OSSemPost(OSTmrSemSignal)` 的结果；TimerTask 每次 SemPend 返回后推进一次
timerTime、扫描一个 spoke。不能只靠 `OS_TMR_CFG_TICKS_PER_SEC` 常量证明 signal 频率或永不丢积压。
TimerTask 先 unlink，再 periodic relink 或设 completed，然后 callback，最后使用缓存 next。

Callback 分两类：Stop 的显式回调和到期扫描回调，实参及调用前状态不同。Stop 在 RUNNING
分支先 unlink，即使 opt 无效/无 callback 也返回 TRUE 并给相应 perr；stopped/completed 也返回
TRUE+STOPPED，不能把 bool 当成 `perr=NONE` 的等价物。
callback 契约除 global invariant 保持，还须保护 caller 的 cached-next/实例 continuation；
任意保持 global invariant 的 TimerDel 回调并不自动满足后一条。接口允许证明安全的定制实例，
但未经确认不把该限制宣称为原版所有 callback 的官方承诺。
实际 read-frame 只保持待访问节点的 generation、Running 状态和 Next 链，以及当前 timer time；
不要求整个 timer image 不变。后续访问会重新读取的 Match/参数/name，以及允许变化的 Prev，
不被无依据冻结。该条件必须由实际 callback/body 证明；删除、重用或改变待访问 Next 的动作
有独立的失败结论，不能仅凭模块 invariant 保持就恢复游标。
Stop callback 还可重新 Start/Delete 当前 timer；回调返回后的最终 state 必须来自该调用的实际
关系，不能因为 Stop 之前做过 Unlink 就无条件承诺最终仍为 stopped。

接口族：`timer_wheel_split_timer/merge_timer`、`timer_link_preserves_wheel`、
`timer_unlink_preserves_wheel`、`timer_alloc/free_preserves_partition`、`timer_advance_unsigned`、
`timer_callback_preserves_scan_continuation`、`timer_signal_sem_relation`。它们需要真实实例证明；
原版在无限制 callback 下的反例另列，不能用强假设无声排除。

## 9. Tick、Time、Statistics 与 Core

### 9.1 Tick/Time

`TickAbstractState.ostime/tickStepState` 分别对应实际 `OSTime` 和 `OSTickStepState`。
此前额外保存的 `tickCtr` 只用于 history 等式／非负性传递，没有实际协议消费者；
2026-09-29 的清理候选已删除它并规范重生成两份受影响 Tick 目标，固定检查尚在进行，
主目录仍保留前一已检查版本。没有 Get/Set 的配置须单独处理该全局是否存在，
而非声明每个配置都拥有 OSTime cell。此删除不涉及端口的真实 `OSTmrCtr`。

OSTimeTick 先 hook、再 u32 time++，之后若 running 才按 step 模式遍历 Task；WAIT 跳过 Task
处理但不跳过 time++。逐 Task delay--，到 0 清 PEND_ANY、写 pend result、非 suspended 才设置
ready；它不直接清除全部 Event/Flag 等待登记。遍历 continuation 保存活跃链上的当前实例/
下一实例，并在每次 Restore 后证明仍可读；调用来自 ISR 与高优先级 Task 的干扰范围分别说明。

`lib/tick.v` 的 `tick_task_step` 组合一个实际 cursor 的 Task 写入和 Scheduler
位图端点：原 delay=0 整步不写 Task/Sched；非零时递减，只有归零才测试 suspension 并
按源码设置 ready。它直接复用 `tick_task_update` 与
`sched_wake_by_status`，没有为 Multi 残余位新增禁止唤醒的 guard。该端点不包含
前置 tick hook、ready trace hook、外层 running/step/idle 检查、游标读取或 Restore。
Task owner、Event owner、Event/Flag linked-wait 与 Mutex/table 跨模块关系已有保持证明；
未改写的 Event bytes 通过优先级观察相等运输，不要求整个 TCB 相等或提前清除超时登记。
Event 的字段/阶段运输提取为 `event_wait_entry_update_task` 与
`event_wait_object_update_task`，原有 status/Suspend/Resume 接口保持 statement，
直接作为该共用接口的特例，不重复一套 Tick 专用等待关系。

`task_retirement.v` 复用 ready membership/排序接口，证明在 ready-excluded 阶段中，
其他任务仍可正常超时置 ready，而已准备删除的 zero-delay 实例不会被 Tick 重新置 ready。
此普通 ready 关系的保持明确使用 no-Multi reserved-bit 协议；原始 Tick 更新仍保留
Multi 行为，不能把该保持定理外推为 Multi-enabled 的全局结论。删除规约组合当前 cursor
lookup、Task/status 协议、保存 generation 的阶段与 Event/Flag/Mutex 关系；每次迭代
仍需使用当时的状态，不能把一个迭代定理当作整个 Restore 窗口或遍历终止证明。

TimeDly/HMSM 是阻塞 continuation，ISR/locked 路径不延迟。HMSM 的源码计算式是：

```text
((hours*3600 + minutes*60 + seconds)*tick_hz
 + tick_hz*(ms + 500/tick_hz)/1000) mod 2^32
```

保留有序 zero/minute/second/ms 检查及每个整数运算宽度；不随意改成 ceiling，非零输入也可
取整为 0 ticks。DlyResume 设置 delay=0 并执行 timeout 风格更新，仍由恢复调用清理等待登记。
Get 绑定临界区 snapshot，Set 只写 ostime，不改变 Task delay 或重置软件 Timer time。

### 9.2 Statistics

Owner 为新 `lib/statistics.v`：`StatisticsState` 具有 `idleCtr : Z`（u32、始终存在）、
条件字段 `idleCtrMax/idleCtrRun : Z`（u32）、`cpuUsage : Z`（u8）、`statReady : bool`。
原校准/采样/停止 ghost phase 只有赋值与投影，已删除；采样的数值保存在局部
`StatisticsSample`，不带额外调用身份。系统 Task/stack 仍归 Task，不重复拥有。

`statistics_rep` 只提供真实字段与机器范围；`statistics_sampling_relation` 连接两个观察点、
采样窗口、分母校准与本次 quotient。OSStatInit 等 2 tick、清 idle counter、再等 tick_hz/10，
将观察值存 Max 并设 ready。OS_TaskStat 首先 Max/=100；Max=0 时自我 suspend 或延迟循环。
若 suspended task 随后恢复，源码会继续，不能由一次 guard 得到分母永远非零。

usage 使用 INT8S 的两次转换/赋值语义，不能把 `100-(INT8S)(Run/Max)` 简化为无界整数
百分比；只有实际 quotient 范围足够时才推出 0..100。默认模型保留精确机器结果，额外的
“有效 CPU 百分比”定理需要校准/调度假设。Max 的负 usage 修正路径也要保持非零来源。
Idle 的 u32 counter++ 与 hook 分开；StatStkChk 的遍历调用 TaskStkChk，不能跨读取点假设同一
priority slot 仍是原 Task；当前 TaskProfile=0 时它不写 profile 栈统计字段。

接口族：`statistics_idle_advance_unsigned`、`statistics_calibration_snapshot`、
`statistics_usage_cast_result`、`statistics_sample_preserves_resources`，以及 zero-denominator
安全条件的明确来源。上述 source path 无法建立该条件时保持未闭合，不新增统计协议公理。

### 9.3 Core/初始化/只读辅助

Core 不增加重复的模块 heap。OS_InitMisc/Ready/TCB/Event/Flag/Mem/Q、Idle/Stat/Timer 创建
依源码顺序组成 `kernel_boot_transition`；TLS 初始化失败的 early return 另有 partial-boot post。
OSStart 的源代码只设置选择/当前指针与 priority，`OSRunning=true` 来自已声明的平台启动契约。
boot 资源包括静态存储/初始化值、足够的 Event/TCB/priority、系统栈与 hook 所需资源。

OSIntEnter/Exit、OSSchedLock/Unlock、OS_Sched/New 使用 Intr/Task/Sched 接口，准确保留 no-op、
饱和和真正切换分支。OS_MemClr 是按字节清零，OS_MemCopy 是源码方向的逐字节复制；重叠场景
不能自动当 memmove。OS_StrLen 要表达 unsigned 8-bit 累计值和停止依据。OS_Dummy 无状态效果。
OSDebugInit 只取得地址以保留调试符号；相应 `const` 值从配置/sizeof 推导，不改变运行态 heap。
`OSSafetyCriticalStart` 本身只有 flag=TRUE 的赋值，没有 critical wrapper；同步/调用阶段必须由
实际调用者契约提供。`OS_StrLen(NULL)=0` 仅在 ArgCheck 开启时成立，关闭配置保留真实解引用。

条件 TLS、Task profile、EventMulti、名称、Trace、safety-critical 的模型增量要体现在同一个
配置参数化接口及函数映射中，不以当前关闭为由永远跳过。外部 TLS/trace 实现不在这十个内核
实现单元内时，给出明确 callee/资源契约，后续选择具体源码实例再证明，不伪装内部代码为空。

## 10. 实现缺陷、协议条件与设计的诚实边界

除明确链接的后续源码回归外，以下是设计时的静态源码轨迹/建模反例，不是 Coq 反例定理。详细设计保留这些
行为和必需接口；它不能使有真实反例的原版自动满足所期望的 invariant。

| 情况 | 具体证据与影响 | 设计处理 |
|---|---|---|
| FlagDel→Pend 再次 unlink | `os_flag.c` 的 ALWAYS 经 TaskRdy/Unlink 摘节点，再把 group.WaitList 用作 free-list link；abort Pend 恢复再次 Unlink，旧 node next/prev 未清。单节点、原 free root 非 NULL 时可把该 root 截断。 | live/detached/free-group 阶段及原 invocation 必须分开；不为原版给出重复 Unlink 幂等定理。后续 [最小修复与源码回归](../source_variants/flag-abort-cleanup/README.md) 已落实：abort 恢复跳过第二次摘链，正式保持证明待完成。 |
| Flag 延迟 consume/最终回读 | 成功 waiter 已被 Post 摘链，但 Pend 恢复仍使用原 group 指针 consume；Post 也会调度后重读 group。其间 Delete/Create 可改变同地址的对象身份。 | 需要真实 group lifetime/call protocol 或实现处理；只有 ghost generation 不能阻止实际读写新对象。该项是允许干扰集待绑定的协议挑战，不等同于已运行的错误测试。 |
| Timer callback 删除 cached-next | TimerTask 缓存 B 后执行 A 的 callback；callback 删除 B 仍可保持普通全局池不变式，但 caller 继续用 B。time 回绕为 0、A/B match=0 时，Free 清 B.match/prev 后，扫描可能再次 Unlink B 并经 NULL prev 写入。 | callback 需要 caller continuation 的保持接口，不能只要 global-invariant-preserving；无限制重入和更窄实例分开，源码修复范围另定。 |
| Memory stride/loan | Create 没有检查 block_size 对齐；Put 没有检查分区 membership 或 double-free，count 未满时可把同一块再次放入 free list。 | 精确保留 guard；typed buffer/linear loan 属调用者合法资源协议。若要防御违约输入，需要实现支持，不能伪造错误分支。 |
| Statistics 分母与窄化 | Max/=100 后为 0 时自我 suspend；重新 Resume 可继续走除法。`Max=1, Run=229` 在选定 8-bit signed cast 语义下可给 usage=127，而非 0..100。 | 区分数据范围、采样有效性和系统任务协议；不添加“Max 始终正”或“CPUUsage 始终<=100”的无来源全局条件。 |
| TaskReg/Stack | RegGet/Set 的 priority lookup 没有完整 NULL/reserved 检查；StkChk 先清输出，扫描循环没有 size 上界。 | API 的实际可读 slot/栈停止证据明确入资源契约；没有证明就不能把不存在 Task、全零栈等路径当作已安全处理。 |
| Multi 唤醒与 Resume 的 ready 条件不同 | `os_core.c:1115` 起 EventTaskRdy 只清指定 mask、只测试 SUSPEND；`os_task.c:870` 起 Resume 清 SUSPEND 后测试 PEND_ANY 与 Dly。SEM\|Q\|MULTI\|SUSPEND 经 Sem wake 再 Resume，仍有 Q 位，因此不置 ready；未 suspended 的同类 wake 却置 ready。 | 这是源码组合轨迹，当前尚非完整 C 反例证明。不能从相同 woken 字段及未 suspended 无条件推出 ready，也不能用单一枚举丢掉剩余位。全操作族协议须保留真实分支与历史/续体；若承诺任意该类交错均能恢复运行，还需实现或公开使用协议的依据。 |
| Task/Mutex 的已知原版问题 | 原始 no-pend delete、priority handover 等与已批准修复版不能共享同一个“源码相同”声明。 | 模型/协议与实现 variant 显式绑定，适配旧证明时消费对应版本的真实证据。 |

对超出所选公开使用协议的场景，保留 raw read/write/失败路径及反例；对已选协议范围内仍有
反例的路径，记录为实现缺口。设计允许给出条件定理接口，但不能以该条件偷偷缩小“原版全函数
安全”的声明。用户已授权按真实语义需要选择最小 C 修复；每个变体仍需保留具体差异、源码
绑定、回归与后续形式化证明，不能把这项授权解释成任意改写实现或自动获得证明结论。

## 11. 落地路径与设计核对

模型实施分成以下实际依赖单元，直接修改并检查，不新增 controller 轮次或替代审批状态：

1. `stable_glob_vars.v` / `ucos2_verify_state_def.v` / `error_codes.v`：配置/新状态/控制与资源记录、完整结果编码、所有 replace
   的字段保持；`kernel_resources.v`：名称字节和条件控制资源。现有 helpers/MapLib/ArrayLib
   足够的结构不另抄；公共链段只在实际复用时抽取。
2. 现有 Task/Sched/Event/Queue/Mutex/Tick owners：补上述源码阶段、multi-wait、alias/cache、
   register/stack、private/public、loop continuation；保留真实绑定的旧可复用表示/引理。
3. 新 `flag.v`、`memory.v`、`timer.v`、`statistics.v`：落实字段/资源、初始化与原值/更新接口，
   同时给跨模块关系与 operation-family 保持定理的确切证明目标。
4. `cross_module_invariants.v` / `ucos2_verify_inv.v`：组合所有当前启用模块及公共资源，
   完成 boot 建立、残余资源运输、全部实际环境动作的证书实例；不能只留创建族证书。
5. 函数 spec 归 `VC/code_proof/<module>/spec/`，统一 L5 状态变换/返回/输出与 L6 annotation
   消费；`lib` 中的旧函数专用声明按依赖迁移。旧 controller 成果保留，相关依赖稳定的受影响
   函数分批迁移并建立当前版本证据，不等待上述全部模型单元完成。

设计核对包括：全部 126 个源定义及条件 API 的模型映射；header 的字段/全局资源归属；新增
ghost 的来源与用途；每个层次的 split/updated-merge/保持接口；跨模块/外部调用关系；已知
反例的处理边界。设计完成不意味着这些定理已证明；实际模型引理须通过必要 Rocq 检查，
不以函数级 controller 流程作为本次模型开发的前置条件。

## 12. 接口签名、代表 API 与后续扩充

### 12.1 表示、更新与证明接口

以下是待实施的签名形状；`M` 是某个上述已确定模块，不是把未知资源塞进 `OtherInv` 的接口。
`image` 是实际物理字段值，`a` 是有明确编码关系的抽象对象，`Assertion` 使用当前 QCP CSL。
当前已有相同语义的声明优先复用；名称可沿所在 owner 的既有词族，不另造重复定义。

```text
valid_<module>             : StableGlobVars -> ModuleState -> Prop
store_<object>             : StableGlobVars -> addr -> ObjectImage -> Assertion
<object>_image_represents  : Config -> ObjectImage -> ObjectState -> Prop
<module>_raw_rep           : StableGlobVars -> ModuleState -> Assertion
<module>_inv               = pure(valid_<module>) && <module>_raw_rep

<module>_split_object      : lookup i state = Some a ->
                            module_rep state |-- object_rep i a ** module_missing_i state i
<module>_merge_object      : lookup i state = Some a ->
                            object_rep i a ** module_missing_i state i |-- module_rep state
<module>_missing_i_update  : actual_other_objects_unchanged old post ->
                            module_missing_i old i = module_missing_i post i
```

字段层同样区分旧值 split/merge 与 updated image 的 merge。上述 entailment 只搬动/重组资源，
不执行 C 写入；不能从 `old_rep` 直接推出内存值已变的 `post_rep`。写入通过真实操作的 Hoare
规则/状态语义建立，之后才使用重组引理。source-ordered phase 的 raw rep 可拥有暂时不满足
稳定对象等式的字段，不用删除这些字段或临时将 invariant 设为 True。

全局更新接口沿现有 `UCOS2_inv_merge_updated_*` 扩展：

```text
validity_bundle cfg post
focused_rep post ** residual cfg post |-- kernel_inv cfg post

residual_transport_<operation> :
  operation_step args old post -> actual_frame_conditions args old ->
  residual cfg old |-- residual cfg post
```

这里 `operation_step` 只记录实际 guard、写入顺序和值，不能包含“post 已有效”作为隐藏过滤器。
`<operation>_preserves_<property>` 则单独从入口性质、合法调用协议和该 step 证明 post 性质。
其 `actual_frame_conditions` 逐个列明未聚焦表示读取的字段/实例不变、或相应关系的运输来源。
若 residual 的空间值也被该操作写了，就应扩大 focused set，而不是给一个假的 frame 等式。

### 12.2 代表 API 的 Pre/Post 设计

这些描述 public/callee 规格的具体资源和观察点；每个 API 的全部有序 guard/返回分支还须与
[126 函数清单](ucos2-v2.93.01-model-api-map.md) 一起消费。这里不是已证明的 Hoare triples。

| 代表接口 | Pre 的资源/协议 | 成功 Post 与错误/不返回 |
|---|---|---|
| `OSTaskCreateExt` / `OS_TCBInit` | 平台允许的初始调用、实际 task entry 与参数、所需栈字节、priority/私有分配阶段；TCBInit 使用已建立的 reservation，不凭空假设槽空。 | 完整字段初始化与 publication 同一实例；失败时释放本次 reservation/私有资源且不破坏并发 creator；running 成功路径有真实调度，原调用若被删除则不伪造返回。 |
| `OSSemPend` | 可读错误码位置或所选 safety 分支、有效/错误类型的真实 Event 存储、调用身份及临界区接口；阻塞时保存 Event/Task instance。 | count>0 立即消费一个；否则 registered→wake/timeout/abort→cleanup，perr 和资源绑定该 invocation。不能把 time=0 的无限等待解释为必定终止。 |
| `OSQPostOpt` | Event/QCB/ring 表示与指针值（允许 NULL）；若额外验证 payload ownership，需应用层可共享协议。 | waiter 优先、精确 broadcast/no-sched/front bit 行为；无 waiter 才 ring 更新，full 保留 slots；调度边界后的全局状态由环境关系得到，不要求总等于原子修改刚结束的快照。 |
| `OSFlagPend` | 真实栈 `OS_FLAG_NODE` 的可写字节、Task/组 instance 与 mode/mask/consume、continuation；合法组存活协议不能由非 NULL 推出。 | 立即/阻塞匹配、flags_rdy 与 consume 时刻分别精确；借出的 node 在 unlink 后归原 invocation。原版 DeleteAlways double-unlink 不能满足期望安全 Post，保留第10节明确缺陷。 |
| `OSMemCreate/Get/Put` | Create 交入对齐且有完整 extent 的 buffer；Get 可打开 live partition；Put 交回该 partition 实例的唯一未归还 block loan 和整块字节。 | Create 建立 partition/free 链；Get 从 free 移至 allocated 并交出整块，Put 接回整块后写首字、移回 free。错误不消费有效 loan；源码未验证的 wrong partition/double-free 不声称会拒绝。 |
| `OSTmrStart/Stop` | 实际 timer image/状态与 scheduler-lock 调用条件；Stop callback 必须绑定真实程序、资源作用与返回行为。 | Start 重启/插入 exact spoke；Stop 先摘链，TRUE 可伴随错误，回调后 state 来自 callback relation；不可凭 Stop 名称要求最终 stopped。 |
| `OSTmr_Task` | 实际 signal Sem、Timer Task/栈、初始化好的 wheel，进入循环的资源。 | 每个 SemPend 返回推进一次；扫描的 cursor/next instance 和回调关系连到下一迭代。只证明部分正确性/安全时不声称恒定时间、无丢信号或无限循环活性。 |
| `OSTaskQuery` / `OSMemQuery` | 输出结构完整可写区及别名条件，输入对象的实际可读权限和 guards。 | TaskQuery 按正向 copy 得到全 native 字节快照；MemQuery 第六项由已复制五项推导。未写输出/padding 保留，写后错误不自动 no-change。 |
| `OSInit` / `OSStart` | 静态/BSS 初值、各池和系统栈、合法配置、明确 hook/platform 资源；不是入口假设 running invariant。 | 按实际 boot 顺序建立各模块与 cross relations，处理部分启动退出；Start 的运行态与切换来自已绑定平台契约。重复 OSInit 不能当作对任意运行态的安全 reset。 |

阻塞 API 的关系采用有限执行前缀、原 invocation 的返回或终止分支；无限等待/任务循环用
相应 trace/安全性质。调度公平、时限保证、信号速率和 callback 终止是另外的性质及所需假设，
不从资源不变式或一个 `Qed` 自动推出系统全活性。

### 12.3 跨模块关系的确切消费者

`cross_module_consistency` 的成员按实际关联分开命名并导出投影，不让函数展开整个全局 record。
以下每行都是待建立/保持的关系族；读关系的函数可用 frame，写相关字段者需提供保持性。

| 关系族 | 稳定/阶段含义 | 主要写入操作族 |
|---|---|---|
| `task_sched_consistency` | eligible live Task 与 ready bits 双向对应；current/high cache 按 source phase 解释 | Task create/delete/change/suspend/resume；所有 pend/wake；Tick；实际 scheduler。 |
| `task_event_wait_consistency` | Event bitmap→唯一真实 TCB，与 Task 的登记反向对应；expired-linked、woken-unlinked 阶段分别列明 | Event Wait/Remove/Rdy/Multi；各 IPC Pend/Post/Abort/Del；Task change/delete；Tick/DlyResume。 |
| `mutex_priority_alias_consistency` | permanent 与 creator/PCP slots 分区，actual alias 的 max/min 与记录的 demand；raw low-byte 快照不充当 base | Task create/change/delete；Mutex Create/Pend/Post/Del/RdyAtPrio。 |
| `event_queue_consistency` | live Queue Event 与 published QCB/ring 一一对应；private ECB/QCB 不要求已经互相发布 | QCreate/rollback/Delete；Event/Queue 初始化；Queue 各更新。 |
| `task_flag_wait_consistency` | 栈 node↔原 Task invocation↔group instance，FlagsRdy/timeout/suspend 与 phase 对应 | Flag Block/Rdy/Unlink/Pend/Post/Del；TaskDel；Tick/DlyResume。 |
| `timer_system_resources_consistency` | 两个 handle cells 指向实际 Event Sem；Timer TCB/栈实例属于 Task；signal trace 连到 Timer 迭代 | Timer Init/Signal/Task；Sem family；Task lifecycle；真实外部 signal 源。 |
| `statistics_task_consistency` | idle/stat Task identity、采样窗口和 counter 观察一致；不额外假设 Max 恒正 | Init/Idle/Stat/StatInit；Time；Task suspend/resume/delete；实际 hooks。 |
| `name_storage_consistency` | 所有当前 name 引用及 live readers 所用字节有实际来源，允许重叠字符串视图 | NameSet/Create/Init/Del；NameGet/StrLen 的 reader 生命周期；经验证的应用字节资源交入/归还。 |
| `caller_resource_partition` | free/private/global/loan 字节唯一归属，generation 与当前 invocation 一致 | 全部 allocator/create/delete/stack/Flag/callback 借用接口及其合法客户端。 |

### 12.4 增补不变式时保留的扩展接口

1. 新增模块内部性质 `P` 时，将它加入 owning module 的 validity，并补该模块 init 建立与
   上表实际写入族的 `preserves_P`；原值 split 不改内存语义，updated merge 消费新有效性证明。
   保留字段读取、对象 lookup 和原 `valid_*` 性质的稳定导出接口。
2. 新增跨模块性质时将它作为独立有名 conjunct 加入 cross bundle；根据它读取的 projection、
   字段、实例和借用信息确定实际 writer 集。未写任何相关观察的动作可用已证明的 frame lemma，
   不能仅凭“C 文件属于别的模块”判断不受影响。
3. 新增真实模块/资源时同时扩展 state/config/layout、raw rep、全部 replace、boot 和环境动作
   证书；全局层提供 `missing_<module>` 与 updated merge。没有实例证据前不得用 opaque
   `Parameter`、`True` 或 `emp` 把启用模块接入后宣布完整。
4. `KernelClientCertificate` 扩展为对每个实际 action family 的源 guard/effect、入口协议保持、
   focused/cross validity、residual transport、原 invocation 正常恢复/终止的证明接口。组合 rely
   只消费真实已证明的实例；未验证客户端如需作为外部契约，必须显式列明，不以证书类型存在
   或“环境会保持 invariant”的定义替代证明。
5. 本设计避免无关函数展开新 record，但不承诺以后零适配。若新增性质被合法源码路径反驳，
   应修正性质/模型阶段或明确实现/协议选择；不能通过加强所有调用者的无来源前提强行通过。
   已完成函数的旧版本证据保留，受实际语义变更影响的模型/spec consumers 一并适配并做
   针对性检查；后续 C case 验收另行绑定最终模型版本。

后续正式 C 验证先稳定以上接口和所有已知缺口，再按一个 source-goal-version 全量分诊/尝试独立 VC，
聚合 earliest loss point 后统一修 annotation。该批量反馈规则不替代实际模型保持或验收证明。

### 12.5 设计阶段的检查与保留事项（历史记录）

该设计阶段只改设计文档；source-only owner 写自己的报告，未改正式 C/Coq/generated 文件，未启动
symbolic execution 或重编译旧证明。独立源码定义清点与 API 映射均为126项、无遗漏/额外条目；
`ucos_ii.h` 的43个 `OS_EXT` 全局均进入唯一归属设计；本组三份文档的本地链接、代码块和
空白检查通过。数目检查不替代语义审查，原始/修复变体及当前/条件配置仍明确区分。

仍待后续实施/证明处理的是：新 `.v` 声明和全量保持定理、具体配置的 boot/平台/client
实例、已知 Flag/Timer/Statistics 路径的实现或合法协议选择，以及受影响旧函数的版本化迁移。
这些已在设计中给出位置、所需接口和诚实边界，不作为已完成模型或已验证成果交付。
