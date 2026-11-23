# Errors and fixes

本目录保留每个源码修复的 patch 和说明。下面列出公开版本中包含的缺陷类别，详细的触发条件、原始行为和修复位置见对应目录中的 `README.md`。

| 模块 | 缺陷与修复摘要 |
|---|---|
| Flag abort | 清理等待者时修正链表摘除和状态恢复，避免残留等待关系。 |
| Flag delete | 删除事件对象前重新验证引用关系，避免失效对象继续被使用。 |
| Flag pend | Pend 路径重新检查对象和等待状态，避免检查与使用之间的不一致。 |
| Flag post | Post 唤醒路径修正事件状态和等待者更新顺序。 |
| Mutex create | 创建过程先完成对象发布，再允许其他路径观察对象。 |
| Mutex current priority | 优先级变化后使用当前任务的真实优先级，避免使用旧缓存。 |
| Mutex delete | 删除前重新验证对象状态，避免并发路径使用已失效对象。 |
| Mutex nested priority | 嵌套互斥锁释放时修正优先级恢复和持锁关系。 |
| Statistics sampling | 统计采样处理零除数，避免除零和百分比越界。 |
| Task atomic publication | 任务控制块发布保持为原子可观察状态，避免半初始化任务被调度。 |
| Task current priority cache | 修改当前任务优先级时同步更新全局当前优先级。 |
| Task delete saturated lock | 删除任务时修正饱和锁计数，避免临界区状态失衡。 |
| Task idle protection | 保护空闲任务和保留优先级，避免非法任务选择。 |
| Task register lookup | 校验任务寄存器索引和配置条件，避免越界访问。 |
| Task transition safety | 任务状态转换保持等待、就绪和删除路径的一致性。 |

这些摘要用于说明修复方向。公开证明源仍以 `proofs/` 中的 Rocq 文件和固定配置为准。
