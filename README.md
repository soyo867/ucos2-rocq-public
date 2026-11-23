# AI赋能 μC/OS-II 验证公开仓库

这个仓库保存 µC/OS-II V2.93.01 在本项目中采用的修正版 C 源码、对应 Rocq 证明源文件、配置和错误修复说明。

## 内容

- `src/` 修正后的 µC/OS-II C 源码
- `include/` 证明所需的头文件和配置头
- `proofs/lib/` 共享 Rocq 模型与逻辑库
- `proofs/VC/code_proof/` 函数规格、验证条件和手工证明源文件
- `config/` 当前验证配置和模型说明
- `source_variants/` 每个已确认源码问题的补丁与说明
- `ERRORS_AND_FIXES.md` 缺陷与修复的简要汇总

## 编译前提

本仓库使用 [QCP](https://github.com/QinxiangCao/QualifiedCProgramming) 生成验证条件，并使用 Rocq 检查证明。QCP/SeparationLogic 依赖没有复制进本仓库。建议将本仓库与 QCP 仓库代码放在同一父目录，并按 `_CoqProject` 中的路径调整依赖根目录。

```text
workspace/
├── QualifiedCProgramming/
└── ucos2-rocq-public/
```

在 QCP 依赖和 Rocq 环境安装完成后，先根据当前机器路径调整 `_CoqProject`，再使用仓库规定的固定 Rocq 检查入口执行检查。

## 版本边界

证明对应 µC/OS-II V2.93.01、项目记录的固定配置和 `src/` 中的修正版实现。底层 ARM/BSP 汇编接口按项目平台契约处理。

## 开源项目链接

- [QCP 工具](https://github.com/QinxiangCao/QualifiedCProgramming)
