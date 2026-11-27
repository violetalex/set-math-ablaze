/-
挑战文件：`statement` 门用的独立陈述。

原则：这里写的是"我们声称证了什么"，与 `CnnExplain/Basic.lean` 里的证明无关。
写法上刻意逐字对应 `docs/SPEC.md` 的定义台账，而不是照着 Lean 源码抄。

命名约定：`Challenge.<Lean 声明名>`。

**量词结构必须与声明一致**（含 implicit/explicit，以及类型类绑定的顺序）。
这是这道门的已知局限：它比数学更严，`∀ (n : ℕ)` 与 `∀ {n : ℕ}` 在数学上是同一句话，
在这里不是。第一次跑就被它拦下过，记在这里，别当成 bug。

索引类型是任意的 `G`：一维取 `G := Fin n`，二维取 `G := Fin h × Fin w`。
-/

import Mathlib
import CnnExplain

namespace Challenge

/-- 台账 C1：仿射复合的线性部分是矩阵乘积，常数项是 `A_f b_g + b_f`。 -/
def CnnExplain.Affine.comp_apply : Prop :=
  ∀ {G : Type*} [Fintype G] (f g : CnnExplain.Affine G) (x : CnnExplain.Vec G),
    (f.comp g).apply x = f.apply (g.apply x)

/-- 台账 C2：单层仿射网络就是该仿射映射本身。 -/
def CnnExplain.net_affine_apply : Prop :=
  ∀ {G : Type*} [Fintype G] (f : CnnExplain.Affine G),
    CnnExplain.Net.apply [CnnExplain.Layer.affine f] = f.apply

/-- 台账 C3：ReLU 层的输出等于按自身模式线性化后的值。 -/
def CnnExplain.ReLU.apply_eq_linear : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (x : CnnExplain.Vec G),
    (CnnExplain.Layer.relu).apply x
      = (CnnExplain.ReLU.linear (CnnExplain.ReLU.pattern x)).apply x

/-- 台账 C7：坐标非正时，模式判为关，两边取同一个值。 -/
def CnnExplain.ReLU.boundary_agrees : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (x : CnnExplain.Vec G) (i : G),
    x i ≤ 0 →
      (CnnExplain.Layer.relu).apply x i
        = (CnnExplain.ReLU.linear (CnnExplain.ReLU.pattern x)).apply x i

/-- 台账 C9：池化是选择——每个坐标的池化值等于窗口内某个坐标的值。 -/
def CnnExplain.Pool.is_selection : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (w : G → Finset G)
    (hw : ∀ i, (w i).Nonempty) (x : CnnExplain.Vec G) (i : G),
    (CnnExplain.Layer.pool w hw).apply x i = x (CnnExplain.Pool.choice w hw x i)

/-- 台账 C8：卷积与循环平移可交换。 -/
def CnnExplain.Conv.convOp_shift : Prop :=
  ∀ {G : Type*} [AddCommSemigroup G] [Fintype G] [DecidableEq G]
    (k : CnnExplain.Vec G) (t : G) (x : CnnExplain.Vec G),
    CnnExplain.Conv.convOp k (CnnExplain.Conv.shiftVec t x)
      = CnnExplain.Conv.shiftVec t (CnnExplain.Conv.convOp k x)

/-- 台账 C4：归纳步。模式序列相同 ⇒ 在同一点处的值等于线性化的值。 -/
def CnnExplain.eval_eq_lin : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (net : CnnExplain.Net G)
    (x y : CnnExplain.Vec G),
    CnnExplain.patternOf net y = CnnExplain.patternOf net x →
      CnnExplain.Net.apply net y = (CnnExplain.linOf net x).apply y

/-- 台账 C5（主定理）：每个输入都有一个精确解释。 -/
def CnnExplain.exists_explanation : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (net : CnnExplain.Net G)
    (x : CnnExplain.Vec G),
    x ∈ CnnExplain.regionOf net (CnnExplain.patternOf net x) ∧
      ∀ y ∈ CnnExplain.regionOf net (CnnExplain.patternOf net x),
        CnnExplain.Net.apply net y = (CnnExplain.linOf net x).apply y

/-- 台账 C6：预测由激活模式决定（取 y = x）。 -/
def CnnExplain.eval_self : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (net : CnnExplain.Net G)
    (x : CnnExplain.Vec G),
    CnnExplain.Net.apply net x = (CnnExplain.linOf net x).apply x

/-- 台账 C10：CNN 的完备解释定理。 -/
def CnnExplain.cnn_explanation : Prop :=
  ∀ {G : Type*} [AddCommSemigroup G] [Fintype G] [DecidableEq G]
    (K : CnnExplain.Vec G) (w : G → Finset G) (hw : ∀ i, (w i).Nonempty)
    (x : CnnExplain.Vec G),
    x ∈ CnnExplain.regionOf (CnnExplain.cnn K w hw)
        (CnnExplain.patternOf (CnnExplain.cnn K w hw) x) ∧
      ∀ y ∈ CnnExplain.regionOf (CnnExplain.cnn K w hw)
        (CnnExplain.patternOf (CnnExplain.cnn K w hw) x),
        CnnExplain.Net.apply (CnnExplain.cnn K w hw) y
          = (CnnExplain.linOf (CnnExplain.cnn K w hw) x).apply y

/-- 台账 C11：二维 CNN 的完备解释定理（`G := Fin h × Fin w`）。 -/
def CnnExplain.cnn2d_explanation : Prop :=
  ∀ (h w : ℕ) (K : CnnExplain.Vec (CnnExplain.Grid h w))
    (win : CnnExplain.Grid h w → Finset (CnnExplain.Grid h w))
    (hw : ∀ i, (win i).Nonempty) (x : CnnExplain.Vec (CnnExplain.Grid h w)),
    x ∈ CnnExplain.regionOf (CnnExplain.cnn K win hw)
        (CnnExplain.patternOf (CnnExplain.cnn K win hw) x) ∧
      ∀ y ∈ CnnExplain.regionOf (CnnExplain.cnn K win hw)
        (CnnExplain.patternOf (CnnExplain.cnn K win hw) x),
        CnnExplain.Net.apply (CnnExplain.cnn K win hw) y
          = (CnnExplain.linOf (CnnExplain.cnn K win hw) x).apply y

/-- 台账 C12：二维卷积与二维循环平移可交换。 -/
def CnnExplain.conv2d_shift : Prop :=
  ∀ (h w : ℕ) (K : CnnExplain.Vec (CnnExplain.Grid h w))
    (t : CnnExplain.Grid h w) (x : CnnExplain.Vec (CnnExplain.Grid h w)),
    CnnExplain.Conv.convOp K (CnnExplain.Conv.shiftVec t x)
      = CnnExplain.Conv.shiftVec t (CnnExplain.Conv.convOp K x)

/-- 台账 C13：零填充破坏平移等变（显式反例）。 -/
def CnnExplain.ZeroPad.breaks_shift : Prop :=
  ∃ (K x : CnnExplain.Vec (Fin 3)) (t : Fin 3),
    CnnExplain.ZeroPad.conv1 K (CnnExplain.Conv.shiftVec t x)
      ≠ CnnExplain.Conv.shiftVec t (CnnExplain.ZeroPad.conv1 K x)

/-- 台账 C14：ReLU 的局部符号稳定。 -/
def CnnExplain.Local.relu_pattern_stable : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] {x y : CnnExplain.Vec G} {ε : ℝ},
    0 < ε → (∀ i, ε < |x i|) → CnnExplain.Local.Close ε x y →
      CnnExplain.ReLU.pattern y = CnnExplain.ReLU.pattern x

/-- 台账 C15：池化的局部选择稳定。 -/
def CnnExplain.Local.pool_choice_stable : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (w : G → Finset G)
    (hw : ∀ i, (w i).Nonempty) {x y : CnnExplain.Vec G} {δ : ℝ},
    0 < δ →
      (∀ i j, j ∈ w i → j ≠ CnnExplain.Pool.choice w hw x i →
        δ < x (CnnExplain.Pool.choice w hw x i) - x j) →
      CnnExplain.Local.Close (δ / 2) x y →
        CnnExplain.Pool.choice w hw y = CnnExplain.Pool.choice w hw x

/-- 台账 C16：局部半径。 -/
def CnnExplain.Local.stable_of_bounds : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    (net : CnnExplain.Net G) (x : CnnExplain.Vec G) {R : ℝ},
    0 < R → CnnExplain.Local.Bounds net x R → CnnExplain.Local.Stable net x R

/-- 台账 C17：完备解释的局部版本。 -/
def CnnExplain.Local.local_region : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    (net : CnnExplain.Net G) (x : CnnExplain.Vec G) {R : ℝ},
    0 < R → CnnExplain.Local.Bounds net x R →
      ∀ {y : CnnExplain.Vec G}, CnnExplain.Local.Close R x y →
        y ∈ CnnExplain.regionOf net (CnnExplain.patternOf net x)

/-- 台账 C18：感受野——线性化矩阵的非零元落在依赖集合内。 -/
def CnnExplain.Field.mem_rowSupport : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (net : CnnExplain.Net G)
    (x : CnnExplain.Vec G) (i j : G),
    (CnnExplain.linOf net x).A i j ≠ 0 →
      j ∈ CnnExplain.Field.rowSupport net x i

/-- 台账 C19：仿射映射在球上的延拓唯一性。 -/
def CnnExplain.Unique.affine_ext_on_ball : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] {f g : CnnExplain.Affine G}
    {x₀ : CnnExplain.Vec G} {r : ℝ},
    0 < r →
      (∀ y, CnnExplain.Local.Close r x₀ y → f.apply y = g.apply y) → f = g

/-- 台账 C20：解释的唯一性。 -/
def CnnExplain.Unique.explanation_unique : Prop :=
  ∀ {G : Type*} [Fintype G] [DecidableEq G] (net : CnnExplain.Net G)
    (x : CnnExplain.Vec G) {R : ℝ} [Nonempty G],
    0 < R → CnnExplain.Local.Bounds net x R →
      ∀ {g : CnnExplain.Affine G},
        (∀ y, CnnExplain.Local.Close R x y → g.apply y = CnnExplain.Net.apply net y) →
          g = CnnExplain.linOf net x

end Challenge
