# Measure

Measure 是一门物理理论自洽性证明语言，基于 Lean4 内核的 fork 构建。修改后的 CIC 内核原生支持 ≈[ε] 近似等价判定，使物理证明成为一等公民。

## 核心能力

- **量纲一致性证明** — `dim_check` tactic，编译期验证物理方程量纲正确性
- **守恒律证明** — `conserve` tactic，通过 C++ ConservationChecker 验证守恒律
- **近似合理性证明** — `approximate` tactic，≈[ε] 内核判定验证误差界
- **对称性证明** — `by_symmetry` tactic，利用对称性简化证明
- **极限证明** — `limit_of` tactic，验证物理极限过程的正确性
- **理论自洽性** — `theory` 块，隔离公理上下文并检查兼容性
- **Scratch Mode** — `.msr` 文件，物理计算如草稿纸般自然
- **不确定度传播** — 区间算术、高斯传播、仿射算术
- **外部引擎集成** — 透明委托 Julia / Python / Mathematica
- **CODATA 物理常量** — 内置最新推荐值

## 前提条件

- CMake >= 3.16
- C++17 编译器
- elan / Lean4 工具链

## 快速开始

```
-- hello.msr
let m = 10.0 kg
let a = 9.81 m/s^2
let F = m * a
emit force: F

let g = 9.8067 +/- 0.0001 m/s^2
let L = 1.000 +/- 0.002 m
let T = 2.0 * pi * sqrt(L / g)
emit period: T
```

## 项目结构

```
Measure/
  ARCHITECTURE.md           # 系统架构文档
  DESIGN.md                 # 设计文档
  grammar.ebnf              # 语言形式文法 (EBNF)
  measure-toolchain.json    # 工具链配置
  CMakeLists.txt            # 顶层构建配置
  docs/                     # 技术文档
    architecture.md         #   架构概览
    kernel-modification.md  #   内核修改详解
    language-reference.md   #   语言参考
    quickstart.md           #   快速入门
    syntax-and-integration.md # 完整语法规范与集成协议
    theory-system.md        #   理论模块系统
    type-system.md          #   类型系统
  measure/
    src/
      kernel/               # C++ 内核扩展
      Measure/              # Lean4 库
        Dim/                #   量纲系统
        Quantity/            #   物理量类型
        Error/              #   不确定度模型
        Theory/             #   理论模块系统
        Conservation/       #   守恒律 & Noether
        Scratch/            #   Scratch Mode 前端
        Syntax/             #   语法扩展 & tactics
        Kernel/             #   C++ FFI 桥接
        External/           #   外部引擎集成
        LSP/                #   编辑器支持
        Unit/               #   单位系统
        Pkg/                #   包管理
        Doc/                #   文档生成
        Constants.lean      #   CODATA 物理常量
        Repl.lean           #   交互式 REPL
    lib/measure/            # Lake 项目配置
```

## 文档

- [快速入门](docs/quickstart.md)
- [语言参考](docs/language-reference.md)
- [语法规范](docs/syntax-and-integration.md)
- [架构概览](docs/architecture.md)
- [类型系统](docs/type-system.md)
- [理论系统](docs/theory-system.md)
- [内核修改](docs/kernel-modification.md)
- [形式文法](grammar.ebnf)

## 许可证

Apache 2.0
