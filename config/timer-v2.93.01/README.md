# Timer 原选定配置的可复现源码入口

此 profile 将同一固定 uC/OS-II V2.93.01 源码用于历史 Timer 证明迁移。
与 `full-features-v2.93.01` 相比，仅显式关闭 Event multi、Event names、
Task profiling；Timer names 仍开启。产生的 `os_cfg.h` 与
`queue-v2.93.01-first-round/os_cfg.h` 逐字节相同，29 个配置值与
`selected_kernel_configuration` 一致。这不是新增 Timer 特有模型。

两个 QCP 头文件兼容补丁与 full-feature profile 相同；各 profile 自包含，
以便现有 preparer 归档并重放相对路径补丁，不依赖构建目录外的文件。
它们不修改内核算法、不删除平台调用，也不提供 ARM/BSP 实现证明。

## 重建 OSTmr_Alloc 输入

在仓库根目录执行。`PREPARED`、`CASE`、`VC` 是尚不存在的输出目录；
`UPSTREAM` 是包含 profile 所列固定 Git 对象的只读源码仓库。

```sh
python3 uC-OS2_verify/tools/prepare_source_input.py \
  --upstream "$UPSTREAM" \
  --profile uC-OS2_verify/config/timer-v2.93.01/profile.json \
  --output "$PREPARED"
python3 uC-OS2_verify/tools/project_source_functions.py \
  --source-input "$PREPARED" --keep OSTmr_Alloc --output "$CASE"
patch --batch --fuzz=0 --forward -p1 -d "$CASE" \
  -i "$PWD/uC-OS2_verify/annotated_C/overlays/timer/tmr_alloc.patch"
mkdir "$VC"
/lib64/ld-linux-x86-64.so.2 "$PWD/linux-binary/symexec" \
  --arch=32 --endian=little \
  --goal-file="$VC/tmr_alloc_goal.v" \
  --proof-auto-file="$VC/tmr_alloc_proof_auto.v" \
  --proof-manual-file="$VC/tmr_alloc_proof_manual.v" \
  -I"$CASE/Cfg/Template" -I"$CASE/Source" \
  -I"$CASE/Ports/ARM-Cortex-A/ARMv7-A/GNU" \
  -IQCP_examples/QCP_demos_LLM/ \
  -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
  -slp uC-OS2_verify/ Ucos2Verify \
  --coq-logic-path=Ucos2Verify.VC.code.timer \
  --input-file="$CASE/Source/ucos_ii.c" --no-exec-info
```

每条命令须成功后再执行下一条；未叠加 annotation 的前端返回零不算该规约的
生成结果。overlay 仅添加验证头文件和原有低层契约/断言，保留函数签名、
static 链接性、宏、条件编译及所有执行语句。其他函数只投影为原签名声明；
它们没有因此被验证。`OSTmr_Alloc` 没有函数调用，调用者须提供互斥保护。

生成 skeleton 的 `Admitted`/`Abort` 不是完成证明；只迁移实际目标的旧证明体，
用完整 `tmr_alloc_goal_check.v` 和固定 `coq_tooling.py` 检查。保留原证明文件。
当新 goal/auto/所有有效依赖和已检查 proof 字节相同时可复用已有证据；
不要仅为换一个报告目录再从零编译。

本次选定配置的结果见 reports 中
`kernel-model-20260927/source-input/tmr-alloc-source-faithful-selected-r2-20261003/`。
它覆盖 Alloc 的低层字段/计数规约，不代表整个 Timer API、联合配置或全局初始化
验收完成。全配置探针亦能生成相同低层 VC，但不能据此套用限定旧配置的
`tmr_alloc_source_binding` 和全局保持性结论。

## 其他已迁移 Timer 函数的 overlay

`uC-OS2_verify/tools/annotation_overlay.py` 可在同一 projected 原始
`Source/os_tmr.c` 上复现 `OSTmr_Free`、`OSTmr_Link` 和 `OSTmr_Unlink` 的
annotation overlay。它先比较选中函数的可执行 token 及声明/链接性，再只
复制 `/*@ ... */` 和 derived-spec 声明；如果实现、宏分支或声明不一致会拒绝
生成 patch。当前三份准备结果记录在
`reports/kernel-model-20260927/source-input/timer-source-overlay-preparation-20261003.md`。
