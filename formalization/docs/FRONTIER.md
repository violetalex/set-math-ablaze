# 审计面（frontier）

> 由 `mathlean frontier` 生成，不要手改。
>
> 口径：从台账 `PROVED` 行出发，沿本项目内部的声明做传递闭包，收集它们直接引用的外部常量；到 Mathlib 边界为止，不展开。

## 总览

| 目标 | 项目内声明 | 外部引用 | 公理 | 数学定理 | 策略支撑 | 定义与实例 | 语言基础 |
|---|---|---|---|---|---|---|---|
| `Liouville.PhiExt_bound` | 10 | 404 | 1 | 79 | 90 | 161 | 73 |
| `Liouville.PhiExt_bound_tendsto` | 11 | 437 | 1 | 95 | 91 | 170 | 80 |

全部目标合并后：外部引用 437 条（公理 1、数学定理 95、策略支撑 91、定义与实例 170、语言基础 80）。

## 公理

- `propext`（Init.Core）

## 数学定理

本工程之外、非策略产生的命题。**这一节就是审计面。**

### `Mathlib.Algebra.Group.Basic`（2）

- `div_one`
- `sub_zero`

### `Mathlib.Algebra.Group.Monoid`（2）

- `mul_one`
- `one_mul`

### `Mathlib.Algebra.GroupWithZero.Basic`（3）

- `div_zero`
- `instIsCancelMulZero`
- `zero_pow`

### `Mathlib.Algebra.GroupWithZero.Defs`（3）

- `GroupWithZero.toNontrivial`
- `IsCancelMulZero.toIsLeftCancelMulZero`
- `MulZeroClass.mul_zero`

### `Mathlib.Algebra.GroupWithZero.NeZero`（1）

- `NeZero.one`

### `Mathlib.Algebra.NeZero`（1）

- `one_ne_zero`

### `Mathlib.Algebra.Order.Archimedean.Basic`（1）

- `instIsCodirectedOrder`

### `Mathlib.Algebra.Order.Archimedean.Real.Basic`（1）

- `Real.instArchimedean`

### `Mathlib.Algebra.Order.Field.Basic`（2）

- `LinearOrderedSemiField.toDenselyOrdered`
- `abs_div`

### `Mathlib.Algebra.Order.Floor.Defs`（1）

- `FloorSemiring.instCharZero`

### `Mathlib.Algebra.Order.Group.Defs`（1）

- `neg_neg_of_pos`

### `Mathlib.Algebra.Order.Group.Unbundled.Abs`（2）

- `abs_of_pos`
- `abs_zero`

### `Mathlib.Algebra.Order.GroupWithZero.Basic`（8）

- `MulPosReflectLE.toMulPosReflectLT`
- `PosMulReflectLE.toPosMulReflectLT`
- `div_le_div_of_nonneg_left`
- `div_le_iff₀`
- `div_nonneg`
- `mul_nonneg`
- `mul_pos`
- `pow_pos`

### `Mathlib.Algebra.Order.GroupWithZero.Defs`（2）

- `MulPosStrictMono.toMulPosReflectLE`
- `PosMulStrictMono.toPosMulReflectLE`

### `Mathlib.Algebra.Order.Monoid.Defs`（1）

- `IsOrderedAddMonoid.toAddLeftMono`

### `Mathlib.Algebra.Order.Monoid.Unbundled.Basic`（1）

- `add_pos_of_pos_of_nonneg`

### `Mathlib.Algebra.Order.Ring.Defs`（4）

- `IsOrderedRing.toPosMulMono`
- `IsStrictOrderedRing.toMulPosStrictMono`
- `IsStrictOrderedRing.toPosMulStrictMono`
- `instNoMaxOrderOfNontrivial`

### `Mathlib.Algebra.Ring.Nat`（1）

- `Nat.instCharZero`

### `Mathlib.Analysis.Normed.Group.Real`（1）

- `Real.norm_eq_abs`

### `Mathlib.Analysis.Normed.Order.Lattice`（2）

- `HasSolidNorm.orderClosedTopology`
- `instHasSolidNormReal`

### `Mathlib.Analysis.Real.Sqrt`（2）

- `Real.sqrt_nonneg`
- `Real.tendsto_sqrt_atTop`

### `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`（1）

- `integral_id`

### `Mathlib.Basic.Real.Basic`（5）

- `Real.instIsOrderedAddMonoid`
- `Real.instIsOrderedRing`
- `Real.instIsStrictOrderedRing`
- `Real.instNontrivial`
- `Real.instZeroLEOneClass`

### `Mathlib.Data.Nat.Cast.Defs`（2）

- `Nat.cast_one`
- `Nat.cast_zero`

### `Mathlib.Data.Nat.Init`（1）

- `Nat.instAtLeastTwoHAddOfNat`

### `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`（3）

- `Continuous.intervalIntegrable`
- `intervalIntegral.integral_const_mul`
- `intervalIntegral.norm_integral_le_of_norm_le`

### `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`（1）

- `intervalIntegral.integral_deriv_eq_sub`

### `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`（1）

- `Real.locallyFinite_volume`

### `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`（1）

- `MeasureTheory.Measure.instOuterMeasureClass`

### `Mathlib.Order.Basic`（2）

- `LT.lt.le`
- `eq_or_lt_of_le`

### `Mathlib.Order.Defs.LinearOrder`（4）

- `le_of_not_gt`
- `lt_of_not_ge`
- `min_le_left`
- `min_le_right`

### `Mathlib.Order.Defs.PartialOrder`（3）

- `le_of_lt`
- `le_trans`
- `ne_of_gt`

### `Mathlib.Order.Filter.AtTopBot.Basic`（1）

- `Filter.eventually_atBot`

### `Mathlib.Order.Filter.AtTopBot.Group`（2）

- `Filter.tendsto_atTop_add_const_left`
- `Filter.tendsto_neg_atBot_atTop`

### `Mathlib.Order.Filter.Basic`（1）

- `Filter.Eventually.of_forall`

### `Mathlib.Order.Filter.Defs`（2）

- `Filter.mp_mem`
- `Filter.univ_mem'`

### `Mathlib.Order.Filter.Tendsto`（2）

- `Filter.Tendsto.comp`
- `Filter.Tendsto.eventually`

### `Mathlib.Order.Interval.Set.Basic`（1）

- `Set.Ioc_subset_Icc_self`

### `Mathlib.Order.Interval.Set.UnorderedInterval`（1）

- `Set.uIcc_of_le`

### `Mathlib.Topology.Algebra.GroupWithZero`（1）

- `Continuous.div_const`

### `Mathlib.Topology.Algebra.Monoid.Defs`（2）

- `Continuous.const_mul`
- `Filter.Tendsto.const_mul`

### `Mathlib.Topology.Algebra.Order.Field`（1）

- `tendsto_inv_atTop_zero`

### `Mathlib.Topology.Algebra.Order.Group`（1）

- `Filter.Tendsto.abs`

### `Mathlib.Topology.Algebra.Ring.Basic`（3）

- `IsSemitopologicalRing.toIsSemitopologicalSemiring`
- `IsSemitopologicalSemiring.toSeparatelyContinuousMul`
- `IsTopologicalRing.toIsSemitopologicalRing`

### `Mathlib.Topology.Algebra.Ring.Real`（1）

- `instIsTopologicalRingReal`

### `Mathlib.Topology.Continuous`（2）

- `Continuous.comp'`
- `continuous_id'`

### `Mathlib.Topology.MetricSpace.Pseudo.Lemmas`（1）

- `instOrderTopologyReal`

### `Mathlib.Topology.NhdsWithin`（1）

- `self_mem_nhdsWithin`

### `Mathlib.Topology.Order.DenselyOrdered`（1）

- `nhdsGT_neBot`

### `Mathlib.Topology.Order.OrderClosed`（4）

- `eventually_le_nhds`
- `instClosedIciTopology`
- `instClosedIicTopology`
- `le_of_tendsto`

### `Mathlib.Topology.UniformSpace.Real`（1）

- `Real.instCompleteSpace`

## 策略支撑

`ring` / `field_simp` / `norm_num` 等策略展开产生的引理，共 91 条，按模块：

- `Mathlib.Tactic.Ring.Common`：32
- `Mathlib.Tactic.FieldSimp.Lemmas`：24
- `Mathlib.Tactic.NormNum.Result`：14
- `Mathlib.Tactic.Linarith.Lemmas`：7
- `Mathlib.Tactic.NormNum.Basic`：4
- `Mathlib.Tactic.Ring.Basic`：3
- `Mathlib.Tactic.NormNum.Pow`：2
- `Mathlib.Tactic.NormNum.Inv`：1
- `Mathlib.Tactic.NormNum.Eq`：1
- `Mathlib.Tactic.Positivity.Core`：1
- `Mathlib.Tactic.CancelDenoms.Core`：1
- `Mathlib.Tactic.Linarith.Preprocessing`：1

## 定义与实例

定义、结构、实例投影等，共 170 条。它们不是命题，通常不需要逐条核对，但**它们决定了定理在说什么**——定义被改过，定理就换了意思。

- `Mathlib.Basic.Real.Basic`：30
- `Mathlib.Algebra.Ring.Defs`：18
- `Mathlib.Algebra.GroupWithZero.Defs`：12
- `Mathlib.Algebra.Group.DivInvMonoid`：11
- `Mathlib.Algebra.Field.Defs`：9
- `Mathlib.Analysis.Normed.Field.Basic`：8
- `Mathlib.Data.Nat.Cast.Defs`：6
- `Mathlib.Algebra.Group.Monoid`：6
- `Mathlib.Order.Lattice`：6
- `Mathlib.Analysis.Normed.Group.Defs`：5
- `Mathlib.Algebra.Group.Defs`：3
- `Mathlib.Order.Filter.Defs`：3
- `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`：3
- `Mathlib.Analysis.Normed.Ring.Basic`：3
- `Mathlib.Order.Defs.PartialOrder`：3

## 每个目标的项目内闭包

### `Liouville.PhiExt_bound`

- `Liouville.PhiExt_bound`
- `Liouville.R`
- `Liouville.PhiExt`
- `Liouville.Phi_bound`
- `Liouville.Phi`
- `Liouville.abs_Phi_le`
- `Liouville.abs_Gamma_le`
- `Liouville.R_ge`
- `Liouville.one_add_sqrt_pos`
- `Liouville.PhiExt_of_pos`

### `Liouville.PhiExt_bound_tendsto`

- `Liouville.PhiExt_bound_tendsto`
- `Liouville.R`
- `Liouville.PhiExt`
- `Liouville.one_add_sqrt_pos`
- `Liouville.PhiExt_bound`
- `Liouville.Phi_bound`
- `Liouville.Phi`
- `Liouville.abs_Phi_le`
- `Liouville.abs_Gamma_le`
- `Liouville.R_ge`
- `Liouville.PhiExt_of_pos`
