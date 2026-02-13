# Measure 语言架构与语法指南

Measure 是基于 Lean4 + Mathlib 的物理形式化库。编译即验证：量纲一致性、守恒律、理论自洽性在编译期自动检查。

---

## 1. 类型系统

### 1.1 量纲 (Dim)

物理量的灵魂是量纲。Measure 用 7 维 SI 向量表示量纲：

```lean
structure Dim where
  L : QExp := QExp.zero  -- 长度 (Length)
  M : QExp := QExp.zero  -- 质量 (Mass)
  T : QExp := QExp.zero  -- 时间 (Time)
  I : QExp := QExp.zero  -- 电流 (Current)
  Θ : QExp := QExp.zero  -- 温度 (Temperature)
  N : QExp := QExp.zero  -- 物质的量 (Amount)
  J : QExp := QExp.zero  -- 发光强度 (Luminosity)
```

`QExp` 是有理指数，支持 L^(1/2) 这样的分数维度：

```lean
structure QExp where
  num : Int    -- 分子
  den : Nat    -- 分母 (≥ 1)
```

预定义的常用量纲：

```lean
def dimLength   : Dim := { L := QExp.one }
def dimMass     : Dim := { M := QExp.one }
def dimTime     : Dim := { T := QExp.one }
def dimVelocity : Dim := { L := QExp.one, T := QExp.mk' (-1) 1 }
def dimAccel    : Dim := { L := QExp.one, T := QExp.mk' (-2) 1 }
def dimForce    : Dim := { L := QExp.one, M := QExp.one, T := QExp.mk' (-2) 1 }
def dimEnergy   : Dim := { L := QExp.mk' 2 1, M := QExp.one, T := QExp.mk' (-2) 1 }
```

量纲运算：
- `Dim.mul d1 d2` — 指数相加（物理量相乘）
- `Dim.div d1 d2` — 指数相减（物理量相除）
- `Dim.pow d n` — 指数缩放（物理量求幂）

### 1.2 物理量 (Quantity)

```lean
structure Quantity (d : Dim) (c : Certainty) where
  value      : Float         -- 数值
  error      : ErrorData c   -- 误差数据（由 Certainty 决定类型）
  provenance : Provenance    -- 来源追踪
```

`d` 是编译期幽灵参数——运行时零开销，但编译器会检查所有量纲运算的一致性。

两种确定性：

```lean
inductive Certainty where
  | exact                    -- 精确量（SI 定义常数、理论推导值）
  | uncertain (model : Type) -- 测量量（携带误差模型）
```

快捷别名：

```lean
abbrev ExactQ (d : Dim) := Quantity d .exact
-- ExactQ 的 error 字段是 Unit，零开销

-- 创建精确量：
def mass := ExactQ.mk dimMass 10.0

-- 创建带不确定度的量：
def g := UncertainQ.mk dimAccel 9.8067 (Gaussian.fromSigma 0.0001)
```

### 1.3 实数物理量 (PhysReal)

用于 Mathlib 形式化证明的 ℝ 值物理量：

```lean
structure PhysReal (d : Dim) where
  val : ℝ
```

`PhysReal` 是 `noncomputable` 的，只用于证明，不用于计算。通过 `Bridge.lean` 与 `Quantity` 互转：

- `Float.toReal` — Float → ℝ（精确，IEEE 754 位解码）
- `Real.approxFloat` — ℝ → Float（近似，公理）

### 1.4 物理常量

```lean
-- 精确常量（SI 2019 定义）：
def c   : ExactQ dimVelocity := ExactQ.mk _ 299792458.0
def h   : ExactQ dimAction   := ExactQ.mk _ 6.62607015e-34
def k_B : ExactQ dimBoltzmann := ExactQ.mk _ 1.380649e-23
def N_A : ExactQ dimAvogadro  := ExactQ.mk _ 6.02214076e23
def e   : ExactQ dimCharge    := ExactQ.mk _ 1.602176634e-19

-- 测量常量（CODATA 2022，带 1σ 不确定度）：
def G   : UncertainQ dimGravConst Gaussian := ...  -- (6.67430 ± 0.00015) × 10⁻¹¹
def m_e : UncertainQ dimMass Gaussian      := ...  -- (9.1093837015 ± 0.0000000028) × 10⁻³¹
def α   : UncertainQ dimDimensionless Gaussian := ... -- (7.2973525693 ± 0.0000000011) × 10⁻³
```

---

## 2. 不确定度传播

三种误差模型，统一接口：

```lean
class UncertaintyModel (α : Type) where
  fromIndependent (value sigma : Float) : α
  add / sub / mul / div / pow / neg : ...
  centralValue : α → Float
  uncertainty  : α → Float
  toInterval   : α → Float × Float
```

### 2.1 Gaussian（一阶线性传播）

追踪每个独立噪声源的偏导数 ∂f/∂zᵢ · σᵢ，最终 σ = √(Σ dᵢ²)。当 σ/|μ| > 10% 时自动警告（一阶近似失效）。

### 2.2 Affine（仿射算术）

用噪声符号 εᵢ ∈ [-1, 1] 表示误差，保留相关性信息。非线性运算引入新噪声符号。

### 2.3 Interval（区间算术）

保守闭区间 [lo, hi]，保证包含真值。最保守但最安全。

---

## 3. 理论模块系统

### 3.1 定义理论

```lean
theory NewtonianGravity where

  axiom newton2 (m : ExactQ dimMass) (a : ExactQ dimAccel)
    : ExactQ dimForce

  axiom gravForce (m₁ m₂ : ExactQ dimMass) (r : ExactQ dimLength)
    : ExactQ dimForce

  axiom energyConservation
    (ke₁ pe₁ ke₂ pe₂ : ExactQ dimEnergy)
    (h : ke₁.value + pe₁.value = ke₂.value + pe₂.value)
    : ke₁.value + pe₁.value = ke₂.value + pe₂.value
```

编译时自动执行 6 阶段检查：
1. 父理论存在性 + 严格度兼容性
2. 注册到 C++ TheoryRegistry
3. 与已加载理论的冲突检测
4. 低严格度父理论自动降级为近似
5. 严格度"最弱环节"传播
6. 自洽性验证（量纲一致 + 守恒律 + 汇总报告）

### 3.2 理论继承

```lean
theory SpecialRelativity extends ClassicalMechanics where
  -- ClassicalMechanics 自动降级为 SpecialRelativity 的近似（v/c → 0）
  axiom lorentzInvariance ...
```

### 3.3 严格度等级

```lean
inductive RigorLevel where
  | strict      -- 数学严格证明
  | approximate -- 近似有效（有误差界）
  | empirical   -- 经验公式（实验拟合）
  | numerical   -- 数值计算（无解析保证）
```

严格度遵循"最弱环节"规则：如果理论 A（strict）依赖理论 B（approximate），则 A 的有效严格度降为 approximate。

### 3.4 理论关系

```lean
inductive TheoryRelation where
  | approx source target bridge    -- A 是 B 的近似（含极限过程和误差界）
  | conflict left right witness    -- A 与 B 矛盾（含冲突证据）
  | extension child parent axioms  -- A 扩展 B（添加新公理）
  | compatible left right          -- A 与 B 兼容
```

冲突检测 4 阶段流水线（C++ 实现）：
1. **缓存** — 查已知结果
2. **句法** — 字符串级矛盾检测（¬A vs A）
3. **语义** — 结构化公理比较（∀x.P vs ∃x.¬P）
4. **SMT** — 外部求解器（TODO）

### 3.5 属性标注

```lean
@[rigor strict]           -- 标注严格度
@[uncertainty Gaussian]   -- 标注误差模型
@[conservation energy]    -- 标注守恒量
@[conservation momentum]
@[conservation charge]
```

---

## 4. Tactics

### 4.1 dim_check — 量纲检查

```lean
-- 验证等式两边量纲一致
theorem force_is_ma : dimForce = Dim.mul dimMass dimAccel := by
  dim_check

-- 验证假设的量纲
example (h : some_dim_equation) : ... := by
  dim_check at h
```

### 4.2 conserve — 守恒律验证

```lean
-- 验证能量守恒
example (ke₁ pe₁ ke₂ pe₂ : ExactQ dimEnergy)
    (h : ke₁.value + pe₁.value = ke₂.value + pe₂.value) :
    ke₁.value + pe₁.value = ke₂.value + pe₂.value := by
  conserve ke₁ pe₁ ke₂ pe₂

-- 跨变换守恒
example ... := by
  conserve momentum across lorentzTransform
```

底层调用 C++ ConservationChecker，3 遍分析：分解 → 计算 delta → 残差分析。

### 4.3 approximate — 近似推理

```lean
-- 忽略小量
example ... := by
  approximate neglect x y

-- Taylor 展开
example ... := by
  approximate taylor x around 0

-- 指定阶数
example ... := by
  approximate taylor x around 0 to_order 2
```

使用 C++ ApproxEqChecker 计算误差界，内核原生支持 ≈[ε] 判定。

### 4.4 by_symmetry — 对称性论证

```lean
example ... := by
  by_symmetry rotational       -- 旋转对称
  by_symmetry translational    -- 平移对称
  by_symmetry gauge            -- 规范对称
  by_symmetry Lorentz          -- Lorentz 对称
  by_symmetry time_reversal    -- 时间反演
```

查询 C++ TheoryGraph 中注册的对称性公理，自动应用。

### 4.5 limit_of — 极限过程

```lean
-- 取极限
example ... := by
  limit_of v -> 0        -- v → 0 极限

-- 远小于极限
example ... := by
  limit_of v << c        -- v/c → 0（非相对论极限）
```

---

## 5. 信任边界

C++ FFI 结果不能直接作为 Lean 证明。Measure 通过两个受控公理桥接：

```lean
axiom ffiInconclusive    -- C++ 返回 "inconclusive"（非 "violated"）
axiom epsilonOverflow    -- epsilon tracker 溢出
```

这两个公理受 `TrustToken`（私有不透明类型）保护，只有 tactic 内部能构造实例，用户代码无法绕过。每次使用都会记录警告日志，可审计。

---

## 6. 物理领域

25 个子领域，每个都是独立的 Lean 模块：

| 领域 | 模块路径 | 严格度 |
|------|----------|--------|
| 经典力学 | `Physics.ClassicalMechanics` | strict |
| 电磁学 | `Physics.Electromagnetism` | strict |
| 量子力学 | `Physics.QuantumMechanics` | strict |
| 狭义相对论 | `Physics.Relativity` | strict |
| 广义相对论 | `Physics.GeneralRelativity` | strict |
| 量子场论 | `Physics.QFT` | approximate |
| 热力学 | `Physics.Thermodynamics` | strict |
| 统计力学 | `Physics.StatisticalMechanics` | strict |
| 凝聚态 | `Physics.CondensedMatter` | approximate |
| 流体力学 | `Physics.FluidMechanics` | strict |
| 光学 | `Physics.Optics` | approximate |
| 原子物理 | `Physics.AtomicPhysics` | strict |
| 粒子物理 | `Physics.ParticlePhysics` | strict |
| 量子引力 | `Physics.QuantumGravity` | numerical |
| 弦理论 | `Physics.StringTheory` | numerical |
| 天体物理 | `Physics.Astrophysics` | approximate |
| 等离子体 | `Physics.PlasmaPhysics` | approximate |
| 生物物理 | `Physics.Biophysics` | empirical |
| 地球物理 | `Physics.Geophysics` | empirical |
| 材料科学 | `Physics.MaterialScience` | empirical |
| 非线性动力学 | `Physics.NonlinearDynamics` | numerical |
| 量子信息 | `Physics.QuantumInfo` | strict |
| 前沿物理 | `Physics.Frontier` | numerical |
| 历史理论 | `Physics.Historical` | empirical |

每个领域包含：结构定义、公理声明、定理证明、示例。

---

## 7. C++ FFI 内核

9 个 C++ 源文件，60+ 个 FFI 函数，通过 Lake `extern_lib` 编译链接：

| 模块 | 功能 |
|------|------|
| `conservation.cpp` | 守恒律 3 遍静态分析 |
| `theory_graph.cpp` | 理论冲突 4 阶段检测 |
| `epsilon_tracker.cpp` | ε 误差追踪树 |
| `approx_eq.cpp` | 近似等价判定 |
| `ffi_bridge.cpp` | Lean ↔ C++ 桥接层 |
| `theory_module.cpp` | 理论注册表 |
| `rigor_propagation.cpp` | 严格度传播 |
| `measure_metadata.cpp` | 元数据管理 |
| `is_approx_eq.cpp` | ≈[ε] 谓词实现 |

---

## 8. 完整示例

```lean
import Measure.Syntax.Theory
import Measure.Syntax.Tactics
import Measure.Physics.Dimensional
import Measure.Constants

open Measure.Dim
open Measure.Quantity

-- 定义牛顿引力理论
theory NewtonianGravity where

  axiom newton2 (m : ExactQ dimMass) (a : ExactQ dimAccel)
    : ExactQ dimForce

  axiom kineticEnergy (m : ExactQ dimMass) (v : ExactQ dimVelocity)
    : ExactQ dimEnergy

  axiom potentialEnergy (m₁ m₂ : ExactQ dimMass) (r : ExactQ dimLength)
    : ExactQ dimEnergy

  axiom energyConservation
    (ke₁ pe₁ ke₂ pe₂ : ExactQ dimEnergy)
    (h : ke₁.value + pe₁.value = ke₂.value + pe₂.value)
    : ke₁.value + pe₁.value = ke₂.value + pe₂.value

-- 量纲一致性证明（编译通过即验证）
theorem force_dim_check
    : dimForce = Dim.mul dimMass dimAccel := by
  native_decide

-- 使用物理常量
def earthMass := ExactQ.mk dimMass 5.972e24
def earthRadius := ExactQ.mk dimLength 6.371e6
```
