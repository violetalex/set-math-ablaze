# P5 优先级排序：哪条引理值得形式化

> 本文档只回答「哪条引理值得形式化」，**不涉及数学正确性判断**。文中的成本（easy / medium / hard / not-feasible）是对 Lean/Mathlib 落地工作量的评估，不是对命题真伪的判断；个别条目的原文陈述本身有误，会单独标注（那属于论文要改的地方，不属于形式化能力问题）。

## 0. 口径与结论速览

**口径**

- **被引用次数** = 本批 31 条评估中，把该条列入 `depends_on` 的其他条目数（只算内部引用，不含 KNSS、Stroock–Varadhan 这类外部文献）。
- **陈述长度** = `quantifier_shape` 的字符数（中文按 1 计）。总表在成本分组内按 **被引用次数 × 陈述长度** 降序排列；乘积并列（多为 0）时，先按「骨架已实测」优先、再按陈述短者优先（对应判据 (b)：陈述越短越值得做）。
- **骨架实测** 指 `Scratch/Probe1.lean`、`Probe2.lean`、`Probe3.lean` 的 `lake env lean` 真实结果（EXIT=0），不是估计。
- **去重**：`thm:main2` = `thm:main` 的重述、`thm:weights2` = `thm:weights` 的重述、`thm:star2` = `thm:star` 的重述。31 条分片去重后是 **28 条独立引理**。

**结论速览**

| 成本 | 条数（去重前 / 后） | 代表 |
|---|---|---|
| easy | 0 / 0 | ——（本批没有真正便宜的条目） |
| medium | 8 / 8 | `prop:bound`、`prop:W`、`prop:timedep`、`cor:tradeoff` |
| hard | 14 / 12 | `prop:lift`、`prop:product`、`thm:weights` |
| not-feasible | 9 / 8 | `thm:KNSS`、`thm:main`、`thm:star`、`prop:2d`、`prop:shear`、`prop:zeroadv` |

真正卡住整个主结论的，是一个**单一的、Mathlib 完全没有的理论层**：线性抛物方程在有界漂移下的 Feynman–Kac 表示 / 抛物极值原理（等价地，鞅问题适定性 + Itô）。`thm:main`、`thm:star`、`prop:dual` 以及依赖它们的条目全部倒在这一步。这是本次评估最重要的结论，不是形式化失败。

---

## 1. 总表

### easy（0 条）

无。最便宜的三条（`prop:bound` 211 行、`cor:tradeoff` 344 行、`prop:timedep` 点态部分 536 行）都已落在 medium。

### medium（8 条）

| 引理 | 成本 | 被引用次数 | 缺口 | 一句话理由 |
|---|---|---|---|---|
| `prop:bound` | medium | 5 | 无（骨架已过）；字面版仍需 sup 挤压 + 由 H1–H3 推 `\|ω^ζ\|≤C₁/R` | 全表最接近纯实分析：一次带参区间积分估计，211 行、常数逐字、无 sorry。 |
| `prop:W` | medium | 3 | Mathlib 无 stream function，ψ 需自建 | 只有链式法则 + 一维积分估计 + 有界差 Cesàro 极限。 |
| `prop:timedep` | medium | 0 | Δ_μ 乘积法则须自建；sup / FK 收尾未做 | 点态恒等式骨架已证（536 行），是整套权重方法的引擎。 |
| `cor:tradeoff` | medium | 0 | **原文两处陈述为假，须先改论文** | rpow 求导工具齐备，344 行全证；但「sup<∞ ⇔ a≥2」与「h''≤h'/ρ ⇒ h≤Cρ²」均不成立。 |
| `prop:mode` | medium | 0 | 需自写「单坐标函数的 Δ₅」引理 | 全是显式计算，数学 20 行；不是 NS 反例，只是模式。 |
| `prop:min` | medium | 0 | 依赖 `prop:product`（hard） | 一维 ODE 比较 + FTC，工具齐备，约 300 行。 |
| `lem:no1d` | medium | 0 | 柱坐标词汇全缺（ρ、ζ、b^ρ、轴正则、V₀） | 分离变量两行；成本全在搭定义。 |
| `prop:radial` | medium | 0 | 无 ODE 求解 API，须手工做 `(ρp)'=0` | 一维 ODE + 点态代数；`is_const_of_deriv_eq_zero` 已确认存在。 |

### hard（14 条）

| 引理 | 成本 | 被引用次数 | 缺口 | 一句话理由 |
|---|---|---|---|---|
| `prop:lift` | hard | 8 | SO(4)-不变提升、径向 Laplacian、柱坐标链式法则全缺 | 恒等式本体 3 行代数，但搬到 ℝ⁵ 并从 3D NS 推出 Γ 输运要从零搭；代数核心已被 Probe3 覆盖。 |
| `prop:product` | hard | 4 | 无关键工具缺失 | 全是一维实分析，但链条长（隐函数 + 分部积分 + Cesàro + ODE 矛盾），>500 行。 |
| `thm:weights2` | hard | 2 | 二阶判别法 + 「a.e. 达到 ⇒ sup 不增」 | 与 `thm:weights` 同条，只多补证明文字；关键步论文自认需空间无穷远信息。 |
| `lem:zeromean` | hard | 1 | 陈述缺 C¹ / 轴正则，字面版无法证，须先重述 | 参数区间积分工具在（已 #check），但需 C¹ 型假设才成立。 |
| `prop:ballavg` | hard | 1 | ℝ⁵ 球上散度定理（Mathlib 只有方体版） | 唯一硬点是球上散度定理，其余是代数 + 极限。 |
| `thm:weights` | hard | 1 | 抛物极值原理 + 二阶判别法 | 代数容易，「极值处 \|w\| 不增」缺二阶判别与抛物框架。 |
| `prop:NC` | hard | 0 | 一般区域散度定理缺（fderiv 分部积分已有） | 数学一行，形式化是带权二阶分部积分的可积性簿记。 |
| `prop:periodic` | hard | 0 | 圆上 Poincaré–Wirtinger 须自证 | 一维工具齐备，需自建圆上 Poincaré 不等式。 |
| `cor:const` | hard | 0 | 继承 `prop:ballavg` | 本质两行矛盾，但必须先有 `prop:ballavg`。 |
| `prop:1d` | hard | 0 | log-cosh 渐近、Φg 单调比较须自建 | 一维微积分齐全，但三块要自己造，400–700 行。 |
| `prop:periodicflat` | hard | 0 | Bochner Fatou、圆上总变差须自建 | 分部积分 + Hölder + 总变差下界，工作量大。 |
| `prop:periodicgen` | hard | 0 | Bochner Fatou 缺（只有 lintegral 版） | 分数阶幂的一致渐近 + Fatou，须自建 Bochner 版。 |
| `prop:examples` | hard | 0 | 数值常数（1.972、k^k e^{-k}）须手证 | 长但初等，无缺理论。 |
| `prop:average` | hard | 0 | 函数型 Cesàro 均值及其求导法则全缺 | 均值、求导、边界项、极限全要自建。 |

### not-feasible（9 条）

| 引理 | 成本 | 被引用次数 | 缺口 | 一句话理由 |
|---|---|---|---|---|
| `thm:star2` | not-feasible | 2 | Feynman–Kac / 抛物极值原理（整套缺失） | 与 `thm:star` 同条（重述 + 证明）。 |
| `thm:star` | not-feasible | 4 | Feynman–Kac / 鞅问题 / 抛物极值原理 | 全部实质内容都在「sup 向前不增」一步，Mathlib 无此理论。 |
| `thm:KNSS` | not-feasible | 2 | NS 弱解、抛物正则性、ℝ⁵ 极值原理 | CITED 外部定理，只能整条公理化为 citation。 |
| `prop:dual` | not-feasible | 1 | Laplacian 链式法则 + `thm:star` 的全部机器 | 结论 Γ≡0 就是 `thm:star2`，身份部分再便宜也救不了。 |
| `thm:main` | not-feasible | 1 | 同 `thm:star` + KNSS 收尾 | 核心一步无路可走。 |
| `prop:zeroadv` | not-feasible | 0 | n 维调和中值 / 可去奇点 / Weyl 引理 | Mathlib 只有复平面（2 维）版本的 Liouville。 |
| `prop:2d` | not-feasible | 0 | Itô / 鞅问题 / Dynkin / 连续时间可选停时 | 证明全在随机分析。 |
| `thm:main2` | not-feasible | 0 | 同 `thm:main` | 重复陈述。 |
| `prop:shear` | not-feasible | 0 | 尺度函数 / 击中概率 / Bessel 轴击中 | 核心是一维扩散击中概率，Mathlib 无此分支。 |

---

## 2. 可形式化的候选

以下每条写清：**要证什么 / 需要哪些新定义 / Mathlib 已有什么（真实名字）/ 骨架实测到哪一步**。Mathlib 名字均在本机 `.lake/packages/mathlib/Mathlib` 里核对过行号；`#check` 确认成功的才写进来。

### 2.1 骨架已实测（3 条）

**`prop:bound`（medium，被引 5）——最推荐**
- 要证：`|Φ(t,ρ,ζ)| ≤ C₁/(2(1+√(−t)))`，Φ=Γ/ρ²。
- 新定义：`R(ρ,t)=1+ρ+√(−t)`、`omegaZeta(Γ,ρ)=deriv Γ ρ/ρ`、`Phi(Γ,ρ)=Γ ρ/ρ^2`。
- Mathlib 已有：`intervalIntegral.norm_integral_le_of_norm_le_const`（`MeasureTheory/Integral/IntervalIntegral/Basic.lean:771`）、`intervalIntegral.integral_deriv_eq_sub`（FTC）、`Real.tendsto_sqrt_atTop`、`tendsto_inv_atTop_zero`、`tendsto_neg_atBot_atTop`。
- 骨架实测：`Probe1.lean`，211 行，EXIT=0，`#print axioms` 只依赖 `propext / Classical.choice / Quot.sound`（无 sorryAx）。已证 `deriv_Gamma_eq`、`abs_Gamma_le`、`abs_Phi_le`、`bound_tendsto_zero` 以及主定理 `prop_bound`（L195-207），常数 `1/2` 是真的（对 `∫₀^ρ C₁r/(1+√−t)` 积分，没有把 `1/R` 放大成上确界）。
- **已显式降级**：(1) Γ 当作固定 `(ζ,t)` 的一元剖面 `Γ(·,ζ,t):ℝ→ℝ`，不是 ℝ³ 上的场；(2) `(H2)⇒|ω^ζ|≤C₁/R` 直接作为假设 `hbound`，不从 3D 涡量推；(3) `eq:axis` 只留 `Γ(0)=0`；(4) 「`‖Φ(t)‖∞→0`」未形式化，只证了界本身的衰减。数学核心零损失。

**`cor:tradeoff`（medium，被引 0）**
- 要证：`Δ_μ ρ^a = a(a−2)ρ^{a−2}`、`b·∇ρ^a = aρ^{a−1}b^ρ`，以及阈值 / 衰减 / 两者只在 a=2 同时成立。
- 新定义：`DeltaMu`、`bDotGrad`、`RadialPowerWeight a = fun ρ _ => ρ^a`。
- Mathlib 已有：`Real.deriv_rpow_const`（`Analysis/SpecialFunctions/Pow/Deriv.lean:467`，无条件）、`Real.rpow_sub`、`tendsto_rpow_atTop`、`tendsto_rpow_neg_nhdsGT_zero`、`antitoneOn_of_deriv_nonpos`、`Real.exp_pos`。
- 骨架实测：`Probe2.lean`，344 行，EXIT=0，17 条声明，无 sorry。
- **两处必须写进论文勘误**（Lean 发现原文为假，不是工具缺口）：(A)「`sup_{ρ>0} ρ²/ρ^a < ∞ ⇔ a≥2`」应为 **`⇔ a=2`**（ρ→0⁺ 一侧被漏掉）；原文的 `a≥2` 只在尾部 `ρ≥1` 成立（已证 `decaySupBddTail_iff : ↔ 2≤a`）。(B)「`h''≤h'/ρ ⇒ h≤Cρ²`（ρ>0）」为假，反例 `h=1−ρ²`；正确版本只是 `ρ≥1` 处的二次增长（已证 `radial_growth_at_infinity`）。

**`prop:timedep`（medium，被引 0）**
- 要证：在 w 的临界点 `∂_t w = νΔ_μ w + G·w`，`G = ν(Δ₅f+\|∇₅f\|²) − b·∇₅f − 2b^ρ/ρ − ∂_t f`；以及 `G≤0 ⇔ ∂_t f ≥ R`。
- 新定义：`DeltaMu`、`Delta5`、`grad5Sq`、`bDotGrad`、`V0`、`CriticalPoint`、`TransportEq`、`wgt f = ρ²e^f`。
- Mathlib 已有：`deriv_mul`（自建 `Δ_μ` 乘积法则的基础）、`Laplacian` 只有 `laplacian_add/sub/smul/neg`，**无乘积法则**（`Analysis/InnerProductSpace/Laplacian.lean:343/351` 只有 `laplacian*_smul`）。
- 骨架实测：`Probe3.lean`，536 行，EXIT=0，50 条声明，无 sorry，`#print axioms prop_timedep` 干净。已自建 `Δ_μ` 乘积法则 `DeltaMu_mul`、lift 恒等式 `DeltaMu_rhoSq_mul`、`Δ₅(e^f)=e^f(Δ₅f+\|∇₅f\|²)`，主定理 `prop_timedep`（L442-448）通过。
- **降级**：sup 步骤 `c'(t)≥sup_x R(x)`、「backward decay forces c'≤0」未做（后者与 `thm:star2` 共享 FK 层，成本会升到 hard），加性族改写未做。点态核心 0% 弱化。

### 2.2 medium，未实测（5 条）

**`prop:W`**
- 要证 `V₀=2b^ρ/ρ=∂_ζW`（`W=−2ψ/ρ²`）、`\|W\|≤C₀`、`V₀` 的对称 Cesàro 均值为零。
- 新定义：`stream ψ`（`b^ρ=−ψ_ζ/ρ, b^ζ=ψ_ρ/ρ`）、`W`、`cesaroMean`、`AxisRegular`。
- Mathlib 已有：`intervalIntegral.norm_integral_le_of_norm_le_const`、`Filter.Tendsto`。
- 缺口：**二维 Poincaré 引理（流函数存在性）Mathlib 没有**（`grep StreamFunction` 0 命中），ψ 只能从速度场显式构造；`|ψ|≤C₀ρ²/2` 靠沿 ρ 的一维积分。

**`prop:mode`**
- 要证：对 `b=(0,0,β)`、`V₀<0`，`Φ=e^{ikζ+λt}` 是有界非平凡古代解，且与 (H1)–(H3) 不相容。
- 新定义：抽象线性提升类、`mode k β V₀ ν`、`IsBoundedAncientNonconstant`、`Γ=ρ²Φ`。
- Mathlib 已有：`Complex.exp`、`Complex.norm_exp`（`‖exp z‖=exp(Re z)`）、`HasDerivAt` 链式法则、`iteratedFDeriv`。
- 缺口：无「只依赖一个坐标的 Laplacian = 二阶导数」现成引理（`grep laplacian.*radial` 0 命中），需用 `iteratedFDeriv` + 标准基展开一次。

**`prop:min`**
- 要证：`h` 在 ζ₀ 有非退化极小 ⇒ 不存在有界光滑加权无散 V 解。
- 新定义：`DeltaMu`、`Afun`、`kfun`、`WeightedDivFree`、`BoundedSmoothField`。
- Mathlib 已有：`intervalIntegral.integral_deriv_eq_sub`、`intervalIntegral.integral_nonneg`、`MeasureTheory.Integrable.mono`、`MeasureTheory.integral_mono`、`MeasureTheory.MemLp`、`Convex.norm_image_sub_le_of_norm_deriv_le`。
- 缺口：无关键缺失；需自写一段从 `|φ''−φ'/ρ+ω²φ|≤Cφ'` 出发的一维积分比较。依赖 `prop:product` 的表示步骤。

**`lem:no1d`**
- 要证：只依赖 ρ 或只依赖 ζ 的有界轴正则无散极向场，必有 `b^ρ=0`、`V₀=0`。
- 新定义：`PoloidalFromStream`、`DivFreeAxisym`、`AxisRegular`、`DependsOnlyOnRho/Zeta`。
- Mathlib 已有：`is_const_of_deriv_eq_zero`（`Analysis/Calculus/MeanValue.lean:751`，根命名空间）、`ContDiff`。
- 缺口：柱坐标词汇全部缺失，必须先搭。

**`prop:radial`**
- 要证：径向伴随密度 `n=B+Cρ^{−2}`，且 `B b^ρ≡0`；可容许的 n 必为常数、只在 `V₀≡0` 存在。
- 新定义：`StreamFunction`、`RadialField`、`AxisRegular`、`V0`。
- Mathlib 已有：`is_const_of_deriv_eq_zero`、`ContDiff`；无 ODE 求解 API，`(ρp)'=0 ⇒ p=D/ρ` 须手工。
- 缺口：无积分、无缺工具，四段短引理。

### 2.3 hard，未实测（14 条）

**`prop:lift`（被引 8，最高）**
- 要证：`Δ_μ(ρ²A)=ρ²Δ₅A`（`Δ₅=∂ρ²+3ρ⁻¹∂ρ+∂ζ²`）与 `∂_tΦ+Div₅(bΦ)=νΔ₅Φ`、`V₀=Div₅b=2b^ρ/ρ`。
- 新定义：`DeltaMu`、`Delta5`、`liftToR5`、`SO4Invariant`、`div5`、`V0`、`Phi`。
- Mathlib 已有：`InnerProductSpace.laplacianWithin`（`Laplacian.lean:133`，但**无径向 / SO(4)-不变公式**）；`div5/∇₅` 0 命中。
- 骨架：`Probe3.lean` 已证代数核心 `DeltaMu_rhoSq_mul`（lift 恒等式）；欠的是提升到 ℝ⁵ 的光滑性、Div₅ 定义、从 3D NS 推输运方程。

**`prop:product`（被引 4）**
- 要证：乘积类 `G=φh` 中不存在有界解（水平图参数化 + Cesàro + ODE 矛盾）。
- Mathlib 已有：`Asymptotics.IsBigO/IsLittleO`、`intervalIntegral.integral_mul_deriv_eq_deriv_mul`、`integral_deriv_eq_sub`、`HasDerivAt.comp`、`Filter.Tendsto.comp`、`Analysis/Calculus/Implicit.lean`（反函数/隐函数）。
- 缺口：无关键缺失；链条长，>500 行。

**`thm:weights` / `thm:weights2`（被引 1 / 2）**
- 要证：权重恒等式 + 极值处 `\|w\|` 不前增 + 「sup 在 a.e. t 达到 ⇒ sup 不前增」+ 一致后向衰减 ⇒ Γ≡0。
- Mathlib 已有：只有**一阶** `IsLocalMaxOn.fderivWithin_nonpos`、`IsLocalMax.lineDeriv_eq_zero`；无二阶判别法，无抛物极值原理（`grep 'maximum principle'` 只命中凸函数与全纯版）。
- 缺口：二阶判别法 + 抛物框架 + 可测选择。

**`lem:zeromean`（被引 1）**
- 要证：`\|(2Z)⁻¹∫_{−Z}^{Z}V^ρ\|≤‖V‖_∞ ρ/(2Z)`，对称 Cesàro 均值消失。
- Mathlib 已有：`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`（已 #check，参数积分求导）。
- 缺口：字面陈述只有「有界」，但证明要对 ρ 在积分号下求导（需 C¹ + 控制函数），且 ρ→0 处需轴正则；**须先重述命题**才能证。

**`prop:ballavg`（被引 1）**
- 要证：`∫_{B_R}(V₀+\|b\|²/(4ν)) ≥ −νC\|∂B_R\|` 及 liminf ≥0。
- Mathlib 已有：`Measure.toSphere`、`InnerProductSpace.volume_ball`、`MeasureTheory.integral_fun_norm_addHaar`（极坐标分解）；散度定理只有方体版 `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`（`MeasureTheory/Integral/DivergenceTheorem.lean:266`，域是 `Set.Icc a b`）。
- 缺口：**球上散度定理须自建**（方体版不能直接给球）。

**`prop:NC`（被引 0，短）**
- 要证：`ν∫\|∇₅f\|²m ≤ ∫V₀m`，m-均值负 ⇒ (★) 不成立。
- Mathlib 已有：`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`（`Analysis/Calculus/LineDeriv/IntegrationByParts.lean:226`，**存在真正的多维分部积分**）、`integral_bilinear_fderiv_right_eq_neg_left_of_integrable`。
- 缺口：一般区域散度定理缺；工作是可积性簿记 + 5 坐标 × 2 阶展开。

**`prop:periodic` / `prop:periodicgen` / `prop:periodicflat`（被引 0）**
- 要证：正周期 h 下 `P(c)→+∞`，从而乘积类刚性。三条逐层放宽（有限阶极小 → 任意 C² 周期 → 平坦极小）。
- Mathlib 已有：`intervalIntegral.integral_mul_deriv_eq_deriv_mul`（圆上分部积分基础）、`MeasureTheory.lintegral_liminf_le`（lintegral Fatou）、`ENNReal.lintegral_mul_le_Lp_mul_Lq`（Hölder）、`IsCompact.exists_isMinOn`、`Real.rpow`、`Asymptotics.IsLittleO`。
- 缺口：**圆上 Poincaré–Wirtinger（须自证）**、**Bochner 版 Fatou 缺**（`MeasureTheory.integral_liminf_le` #check 报 unknown）、**圆上总变差定义缺**。三条都 >500 行。

**`cor:const`（被引 0）**
- 要证：常数 `V₀<−\|b\|²/(4ν)` ⇒ 无 f 满足 (★)。
- Mathlib 已有：`InnerProductSpace.volume_ball`、`Measure.toSphere_apply_univ`。
- 缺口：继承 `prop:ballavg` 的球散度定理；本质两行矛盾。

**`prop:1d`（被引 0）**
- 要证：`b=−b₀tanh x`、`V₀=b'` 时无有界 f 满足 (★)。
- Mathlib 已有：`Real.tendsto_exp_atBot`、`monotone_of_deriv_nonneg`、`intervalIntegral.integral_hasDerivAt_right`（注意：`integral_hasDerivAt` 这个名字 **#check 报 unknown**）。
- 缺口：`log(cosh)` 渐近（`grep 'tendsto_cosh|cosh_atTop'` 0 命中）、Φg 单调比较、变号矛盾，三块自建。

**`prop:examples`（被引 0）**
- 要证：两组显式场使 (★) 成立。
- Mathlib 已有：`Real.mul_exp_neg_le_exp_neg_one`、`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`、`Real.exp_pos`。
- 缺口：数值常数（`1.972`、`k^k e^{-k}` 极大值）须手证；Laplacian 无乘积 / 链式法则，展开要手写。长但初等。

**`prop:average`（被引 0）**
- 要证：对称 ξ-Cesàro 均值下的平均方程与 `C=⟨b^ρG⟩` 的两个界。
- Mathlib 已有：`Filter.Tendsto.cesaro`（**只对 `ℕ→ℝ` 序列**，`Analysis/Asymptotics/SpecificAsymptotics.lean:191`）、`integral_fun_norm_addHaar`。
- 缺口：**函数型 Cesàro 均值与其求导法则全缺**、均值与 `d_ρ/d_τ` 交换缺、框架变换缺。

---

## 3. 明确不可形式化的部分

这一节要诚实：**论文里大部分「分析性」结论都会落在这里，这本身是结论，不是失败。** 分三类。

### 3.1 缺的是整套理论（不是缺一条引理）

- **线性抛物方程的 Feynman–Kac / 抛物极值原理**。`thm:main`、`thm:main2`、`thm:star`、`thm:star2`、`prop:dual` 全部倒在这一步。Mathlib 现状（逐条 #check / grep 确认）：
  - `grep -rn Feynman` → 只有 `MeasureTheory/Integral/CurveIntegral/Basic.lean:64` 一句注释；
  - `grep -rni 'heatKernel|heat kernel'` → 0；
  - `grep -rni 'maximum principle'` → 只有 `Analysis/Convex/Jensen.lean`（凸函数）与 `Analysis/Complex/OpenMapping.lean`（全纯最大模）；
  - `MeasureTheory.Martingale` 存在（`Probability/Martingale/Basic.lean:53`），但**没有**鞅问题适定性 / SDE / Itô 公式；`IsBrownianReal` / `IsPreBrownianReal` 只是过程律。
- **Navier–Stokes 弱解 + 抛物正则性**。`thm:KNSS` 是 CITED：`grep -rli 'navier|stokes'` 只命中 `Analysis/BoxIntegral/DivergenceTheorem.lean` 的一句注释。陈述它就需要 Bochner/抛物空间 + ℝ⁵ 极值原理，超出「证明」范围，只能整条公理化为 citation。
- **随机分析**：`thm:main2`、`prop:2d`、`prop:shear` 依赖 Itô / Dynkin / 鞅问题 / 连续时间可选停时。Mathlib 的可选停时 `Submartingale.expected_stoppedValue_mono`（`Probability/Martingale/OptionalStopping.lean:43`）是 **ℕ-指标（离散时间）** 的，连续时间没有。
- **n 维调和函数理论**：`prop:zeroadv` 需要一般维数的中值性质、直线（余维 4）可去奇点、Weyl 引理。Mathlib 只有 `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant`（**复平面 2 维**）；`HarmonicAt` 只有 add/sub/neg/smul。
- **一维扩散的尺度函数 / 击中概率 / Bessel 轴击中**：`prop:shear` 的核心。`grep 'Bessel|Feller|scale function'` 在 `Mathlib/Probability` 只命中 `Process/HittingTime.lean`（一般命中时刻定义）。

### 3.2 因依赖「无法 #check 确认存在」的库名而降级（反例登记）

按本次规则：**若某条的「可形式化」依赖一个无法用 `#check` 确认存在的 Mathlib 名称，就不算可形式化。** 本批的落实情况：

- 没有任何 medium/hard 条目是靠一个**虚构的库名**撑起来的——它们要么明确给出已确认的名字，要么明说「须自建」。
- 真正因此**降级**的：`prop:zeroadv`（依赖 ℝ⁵ 调和可去集 / Weyl 引理这两个 Mathlib 不存在的对象，且 `re` 是整块理论）、`prop:dual`（结论即 `thm:star2`，后者依赖 FK 整套）、`prop:2d` / `prop:shear`（随机分析整套）。这些已在上表 not-feasible。
- **记录三个实测到的「名字陷阱」**，供后续 SPEC 避开：
  1. `InnerProductSpace.Laplacian` / `InnerProductSpace.laplacian` **#check 报 unknown**；可用的只有 `laplacianWithin`（`Laplacian.lean:133`），`Δ` 记号是 `scoped notation "Delta" => Laplacian.laplacian`（`Analysis/Distribution/DerivNotation.lean:273`）。任何候选都要自建 `Δ₅`。
  2. `intervalIntegral.integral_hasDerivAt` **#check 报 unknown**；存在的是 `integral_hasDerivAt_right` / `integral_hasDerivAt_of_tendsto_ae_right`。
  3. `MeasureTheory.integral_liminf_le`（Bochner 版 Fatou）**#check 报 unknown**；只有 `MeasureTheory.lintegral_liminf_le`（lintegral 版）。
- **未降级的说明（防止误判）**：`prop:average` 的函数型 Cesàro 均值、`prop:periodic*` 的圆上 Poincaré / TV、`prop:ballavg` 的球散度定理、`prop:product` 的隐函数——这些是「**要自建的定义/引理**」，不是「依赖不存在的库名」，所以仍留 hard，没有移入不可形式化。若后续发现无法自建，再降级。

### 3.3 重复条目

`thm:main2`、`thm:weights2`、`thm:star2` 分别是 `thm:main`、`thm:weights`、`thm:star` 的重述，形式化时只做一次。

---

## 4. 推荐

**唯一建议：先做 `prop:bound`。**

- **为什么是它**（三条判据全过）：(a) 它被主结论 `thm:main` 直接依赖（提供 `‖Φ(t)‖∞→0` 的后向衰减）；(b) 陈述短（被引 5，medium）；(c) 它的分析核心**不依赖任何 Mathlib 缺失的分析工具**——全部落在已确认的 `intervalIntegral.norm_integral_le_of_norm_le_const` + FTC + 极限链上。而且它是全表**唯一有完整、无 sorry、常数逐字**骨架的 medium 条目（`Probe1.lean` 211 行）。
- **不做 `prop:lift` 的理由**：它被引最多（8）、陈述更短（62 字），确实是结构骨架；但它是 hard，且缺 SO(4)-不变提升理论、径向 Laplacian、柱坐标链式法则三块，没有骨架支撑。作为第二优先，而不是第一。
- **主候选 / 降级方案**：主候选是论文原样的场版本（ℝ³×(ζ,t) 上、由 (H1)–(H3) 推出输入界）；若「由 H1–H3 推 `\|ω^ζ\|≤C₁/R`」这一 3D NS 部分证不动，**退到剖面版仍然算数**——它正是 `thm:main` 后向衰减所需的那条数值不等式，且已编译通过。
- **再退一步**：即使 `‖Φ(t)‖∞→0` 的 sup 挤压没做完，只要 `\|Γ(ρ)\|≤C₁ρ²/(2(1+√−t))`（`abs_Gamma_le`）成立，乘上 `1/ρ²` 后 `\|Φ\|≤C₁/(2(1+√−t))→0`，后向衰减结论不受影响。

**可以直接抄进 SPEC 的推荐陈述（剖面版，量词完整）**

> 对任意 `Γ : ℝ → ℝ`（固定 `(ζ,t)` 的经向剖面）、`C₁ t : ℝ`，若
> `0 ≤ C₁`、`t ≤ 0`、`Γ 0 = 0`、`∀ x, 0 ≤ x → DifferentiableAt ℝ Γ x`、
> `∀ ρ, 0 ≤ ρ → IntervalIntegrable (deriv Γ) volume 0 ρ`、
> `∀ r, 0 ≤ r → |deriv Γ r| ≤ C₁ * r / R r t`，其中 `R r t = 1 + r + Real.sqrt (-t)`，
> 则 `∀ ρ, 0 ≤ ρ → |Phi Γ ρ| ≤ C₁ / (2 * (1 + Real.sqrt (-t)))`，其中 `Phi Γ ρ = Γ ρ / ρ ^ 2`。
>
> 对应 Lean：`theorem prop_bound (Γ : ℝ → ℝ) (C₁ t : ℝ) (hC₁ : 0 ≤ C₁) (ht : t ≤ 0) (hΓ0 : Γ 0 = 0) (hdiff : ∀ x, 0 ≤ x → DifferentiableAt ℝ Γ x) (hint : ∀ ρ, 0 ≤ ρ → IntervalIntegrable (deriv Γ) volume 0 ρ) (hbound : ∀ r, 0 ≤ r → |deriv Γ r| ≤ C₁ * r / R r t) : ∀ ρ, 0 ≤ ρ → |Phi Γ ρ| ≤ C₁ / (2 * (1 + Real.sqrt (-t)))`

**风险**

1. 剖面版丢掉了 ζ、t 的真正依赖与 ℝ³ 场结构；若项目之后要求「逐字对应论文」的场版本，需要补 3D 柱坐标 NS 框架（hard，且 `thm:KNSS` 那条仍是 not-feasible）。
2. `\|Φ(t)\|∞→0` 的 sup 挤压需要 `sSup` 的 `BddAbove` 簿记（moderate，约 100–200 行），这是剖面版之外的唯一剩余缺口。
3. 输入界 `hbound` 是假设而非导出；若不允许把 `(H2)` 的后果当假设，成本会升到 hard。
