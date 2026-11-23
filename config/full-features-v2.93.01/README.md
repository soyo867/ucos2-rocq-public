# 原始源码入口：Multi、Event 名称与 Task profiling 联合配置

使用 profile.json 固定的 uC/OS-II V2.93.01 Git 对象、原始 Source、ARMv7-A
端口头文件和 Cfg/Template。模板本身已经同时打开这三个开关；不另维护展开后的
os_cfg.h、结构体或内核函数副本。Coq 对应值为 full_features_kernel_configuration；
旧 selected_kernel_configuration 不变。

## 重建输入

从仓库根目录执行，OUTPUT 和 CASE 必须是尚不存在的目录：

    python3 uC-OS2_verify/tools/prepare_source_input.py \
      --upstream /tmp/ucos2-official-audit-20260802 \
      --profile uC-OS2_verify/config/full-features-v2.93.01/profile.json \
      --output OUTPUT
    python3 uC-OS2_verify/tools/project_source_functions.py \
      --source-input OUTPUT --keep OSSemCreate --output CASE

第二步保留原始 master translation unit Source/ucos_ii.c 及其 include 结构；
只将其他函数的定义体替换成同签名声明。选中函数的参数、执行体、宏和 #if
不变，原头文件中的 static/extern 和调用接口不靠重新拼写恢复。它不是链接产物，
更不是其他函数的实现证明；被调用函数仍须有正确契约和必要的源码证明。
目前支持本版本实际采用的普通 ANSI C 函数定义，不是通用 C 解析器。

遗漏函数体内若有 #define/#undef/#include/#pragma 等预处理副作用，工具拒绝
提取，不静默删除。跨函数体边界的条件指令、目标不存在或定义不唯一也拒绝。
工具不会覆盖现有目录。先准备/叠加明确 annotation patch，再重新投影；
不要直接长期维护生成目录中的函数副本。新增 patch 仍须遵守当前任务的写权限。

QCP 实际入口为 CASE/Source/ucos_ii.c，include 顺序为
CASE/Cfg/Template、CASE/Source、CASE/Ports/ARM-Cortex-A/ARMv7-A/GNU，
并保留仓库要求的 QCP_demos_LLM include/SLP、--arch=32、--endian=little。
annotation/策略、canonical 输出参数和正式检查继续由当前验证路线提供；
这里的脚本不会替代 controller 或固定 Rocq 检查。

## 两项已记录适配

- app-cfg-freestanding.patch 只去掉应用模板的 stdarg.h/stdio.h includes；
  当前选中内核没有使用其 printf/varargs 接口，应用宏本身保留。当前 QCP
  无法解析宿主 stdarg.h 中的 __builtin_va_list，不能用宿主 libc 冒充 ARM ABI。
- port-extern-declarations.patch 将 os_cpu.h 中 OS_CPU_EXT 的声明用法显式写成
  extern，保留声明类型、条件、所有平台调用和临界区宏。此入口不编译定义
  OS_CPU_GLOBALS 的 CPU 实现单元；若误用，明确 #error，而不是改变其定义语义。
  具体原因是当前 QCP 对条件附近展开为 extern 的宏报 token 错误。

这不是操作系统算法修复，也没有将平台调用视作空操作。12 个内核 C 单元在
适配前后从 BOOLEAN 类型声明起的完整 GCC 预处理文本相等；精确命令、诊断与
局限保存在 reports/kernel-model-20260927/source-input。它不替代编译器正确性证明。

## 当前范围

29 个 Coq 配置值已经逐一对照实际宏；联合配置的 GCC ILP32 检查为 92 字节 TCB、
24 字节 ECB，名称指针偏移 20。多等待指针偏移 32/36，profiling 五字段偏移
64/68/72/76/80；任务名称与寄存器表移到 84/88。不要把这些数值当成已经完成
ARM/BSP 实现验证，也不要直接套用旧 64/72 字节空间谓词。

OSSemCreate、OSEventNameGet/Set、OS_TCBInit 已完成原始函数体对应和无契约前端
诊断。OSEventPendMulti 尚未通过该诊断；其未声明局部变量报错与缺少 annotation
的执行上下文有关，不能据此改写 switch。最小反例补充诊断契约后消失；
真实函数仍需完整资源契约和循环断言，不允许移植这个弱诊断契约。

共享模型的 profiling 字段/92 字节空间表示、相关不变式与实际 C 证明仍未完成。
本目录表示可重建输入和配置对应，不表示三个新增功能或整个 goal 已验证完成。
