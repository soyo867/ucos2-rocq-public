# Flag abort cleanup variant

本变体基于 [已绑定的 V2.93.01 profile](../../config/queue-v2.93.01-first-round/profile.json)，
只修改 `Source/os_flag.c` 的 `OSFlagPend` 阻塞恢复分支。原始源码保持只读；补丁仅在隔离构建目录采用。
这是用户授权的全内核模型实现工作中的最小源码修复，不是原版源码已经正确的证明。

## 原因与修改

`OSFlagDel(OS_DEL_ALWAYS)` 经 `OS_FlagTaskRdy` 对每个等待节点调用 `OS_FlagUnlink`，
再把 group 放回空闲链。原版 `OSFlagPend` 从 abort 恢复时再次摘除自己的栈节点，
可能把已经用作 free-list link 的 `OSFlagWaitList` 改成 NULL 或旧等待节点地址。

补丁仅让 `OS_STAT_PEND_ABORT` 恢复路径跳过第二次摘链；timeout 及原来的其他非 OK
状态仍执行清理。返回值、错误码、任务恢复及成功后的 consume 行为不变。
`OS_FlagUnlink` 的前提仍是节点尚在链上，不改成任意指针上的容错操作。
节点旧 `Next`/`Prev` 不清空：Delete/Post 的遍历在摘链后仍读取旧 `Next`。

## 检查和边界

运行 `bash uC-OS2_verify/tests/flag_abort_cleanup/run.sh`。
测试编译真实原版及打补丁后的 `os_flag.c`，覆盖单/双等待节点 abort、timeout cleanup、
正常 Post/consume；scheduler、CPU 临界区和 MemClr 是显式宿主测试夹具。
它检查源代码路径，不是 ARM/BSP 调度器测试，也不替代 QCP/Rocq 证明。

后续 Flag 模型须分别证明：abort 状态来自已经完成摘链的 Delete，timeout 恢复仍持有
待清理节点，以及空闲 group 与栈节点的资源分离。该补丁不解决 Post 调度后回读或
成功 Pend 延迟 consume 与 Delete/Create 重用之间的全部生命周期问题；这些仍需独立
模型/调用协议或进一步有真实依据的实现修复。
