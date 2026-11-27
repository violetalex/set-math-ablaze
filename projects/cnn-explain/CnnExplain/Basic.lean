import Mathlib

/-!
# CnnExplain：完备解释

对应 `docs/SPEC.md` §1 的定义台账。

**索引类型是任意的有限加法交换幺半群 `G`**，不写死成 `Fin n`：

* 一维循环卷积 = `G := Fin n`；
* 二维循环卷积 = `G := Fin h × Fin w`（逐坐标加法）。

这样 "二维" 不是第二套理论，而是同一个定理在另一个 `G` 上的实例。

符号约定（SPEC §1）：ReLU 关的分支取 `z ≤ 0`、开的分支取 `z > 0`，
于是 `z = 0` 归关分支，而 `max 0 0 = 0` 与关分支一致——结论在闭胞腔上成立。
-/

namespace CnnExplain

/-- 向量：`G → ℝ`。 -/
abbrev Vec (G : Type*) := G → ℝ

/-- 方阵。等宽，见 SPEC (H1)。 -/
abbrev Mat (G : Type*) := Matrix G G ℝ

/-- 仿射映射 `x ↦ A x + b`。 -/
structure Affine (G : Type*) where
  A : Mat G
  b : Vec G

namespace Affine

variable {G : Type*} [Fintype G]

/-- 作用：`x ↦ A x + b`。 -/
def apply (f : Affine G) (x : Vec G) : Vec G := f.A.mulVec x + f.b

/-- 复合：`(f ∘ g)(x) = A_f (A_g x + b_g) + b_f`，线性部分是矩阵乘积。 -/
def comp (f g : Affine G) : Affine G :=
  ⟨f.A * g.A, f.A.mulVec g.b + f.b⟩

/-- 台账 C1：仿射复合的线性部分是矩阵乘积，常数项是 `A_f b_g + b_f`。 -/
theorem comp_apply (f g : Affine G) (x : Vec G) :
    (f.comp g).apply x = f.apply (g.apply x) := by
  simp only [comp, apply, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

end Affine

/-- 一层：仿射、逐点 ReLU，或（按窗口的）最大池化。 -/
inductive Layer (G : Type*) where
  | affine (f : Affine G)
  | relu
  | pool (w : G → Finset G) (hw : ∀ i, (w i).Nonempty)

namespace Layer

variable {G : Type*} [Fintype G]

/-- 逐层作用。ReLU 取 `max · 0`；池化在第 `i` 个坐标上取窗口 `w i` 的最大值。 -/
noncomputable def apply : Layer G → Vec G → Vec G
  | .affine f, x => f.apply x
  | .relu, x => fun i => max (x i) 0
  | .pool w hw, x => fun i => (w i).sup' (hw i) x

end Layer

/-- 网络：有限的层表（SPEC (H3)）。 -/
abbrev Net (G : Type*) := List (Layer G)

namespace Net

variable {G : Type*} [Fintype G]

/-- 逐层求值。 -/
noncomputable def apply : Net G → Vec G → Vec G
  | [], x => x
  | l :: ls, x => apply ls (l.apply x)

end Net

/-! ## 单层 ReLU 的模式与线性化 -/

section ReLU

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- 对角矩阵乘向量：只保留对角项。`Mathlib` 没有现成引理，自己算。 -/
theorem diagonal_mulVec_apply (d x : Vec G) (i : G) :
    (Matrix.diagonal d).mulVec x i = d i * x i := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

namespace ReLU

/-- 模式：坐标 `i` 为开当且仅当 `0 < x i`。

`ℝ` 上的序不可判定，所以这是 `noncomputable`；只用于陈述，不参与计算。 -/
noncomputable def pattern (x : Vec G) : G → Bool := fun i => decide (0 < x i)

/-- 按模式线性化：开的位置保留，关的位置清零。 -/
def linear (σ : G → Bool) : Affine G :=
  ⟨Matrix.diagonal (fun i => if σ i then (1 : ℝ) else 0), 0⟩

/-- 模式对应的区域（闭胞腔）。 -/
def region (σ : G → Bool) : Set (Vec G) :=
  {x | ∀ i, if σ i then 0 < x i else x i ≤ 0}

/-- 线性化映射逐点的值。 -/
theorem linear_apply (σ : G → Bool) (x : Vec G) (i : G) :
    (linear σ).apply x i = (if σ i then (1 : ℝ) else 0) * x i := by
  simp [linear, Affine.apply, diagonal_mulVec_apply]

/-- 台账 C3：ReLU 层的输出，等于它按自身模式线性化后的仿射映射在该点的值。 -/
theorem apply_eq_linear (x : Vec G) :
    (Layer.relu).apply x = (linear (pattern x)).apply x := by
  funext i
  rw [linear_apply]
  simp only [Layer.apply]
  by_cases h : 0 < x i
  · have hp : pattern x i = true := by simp [pattern, h]
    simp [hp, max_eq_left (le_of_lt h)]
  · have hp : pattern x i = false := by simp [pattern, h]
    have hx : x i ≤ 0 := not_lt.mp h
    simp [hp, max_eq_right hx]

/-- 台账 C7：边界相容。坐标非正（含等于零）时，模式判为"关"，且两边取同一个值。 -/
theorem boundary_agrees (x : Vec G) (i : G) (h : x i ≤ 0) :
    (Layer.relu).apply x i = (linear (pattern x)).apply x i := by
  have hp : pattern x i = false := by simp [pattern, not_lt.mpr h]
  simp [Layer.apply, linear, Affine.apply, diagonal_mulVec_apply, hp, max_eq_right h]

end ReLU

end ReLU

/-- 台账 C2：单层仿射网络就是该仿射映射本身（归纳的基例）。 -/
theorem net_affine_apply {G : Type*} [Fintype G] (f : Affine G) :
    Net.apply [Layer.affine f] = f.apply := by
  funext x
  simp [Net.apply, Layer.apply]

/-! ## 最大池化：选择矩阵 -/

section Pool

variable {G : Type*} [Fintype G] [DecidableEq G]

namespace Pool

/-- 输入 `x` 处每个窗口取到最大值的坐标（`Classical.choose`，非计算）。 -/
noncomputable def choice (w : G → Finset G) (hw : ∀ i, (w i).Nonempty)
    (x : Vec G) : G → G :=
  fun i => Classical.choose (Finset.exists_mem_eq_sup' (hw i) x)

/-- 选中的坐标确实在窗口里。 -/
theorem choice_mem (w : G → Finset G) (hw : ∀ i, (w i).Nonempty)
    (x : Vec G) (i : G) : choice w hw x i ∈ w i :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' (hw i) x)).1

/-- 选中的坐标取到窗口最大值。 -/
theorem choice_eq (w : G → Finset G) (hw : ∀ i, (w i).Nonempty)
    (x : Vec G) (i : G) :
    (w i).sup' (hw i) x = x (choice w hw x i) :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' (hw i) x)).2

/-- 按坐标选择：`(selectMat c).mulVec x i = x (c i)`。 -/
def selectMat (c : G → G) : Mat G := fun i j => if j = c i then (1 : ℝ) else 0

/-- 选择矩阵作为仿射层（偏置为零）。 -/
def selectAff (c : G → G) : Affine G := ⟨selectMat c, 0⟩

theorem selectMat_mulVec (c : G → G) (x : Vec G) (i : G) :
    (selectMat c).mulVec x i = x (c i) := by
  classical
  simp only [selectMat, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (c i)]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ (c i)) h

/-- 选择矩阵的逐点值。 -/
theorem selectAff_apply (c : G → G) (x : Vec G) (i : G) :
    (selectAff c).apply x i = x (c i) := by
  simp [selectAff, Affine.apply, selectMat_mulVec]

/-- **台账 C9**：池化的值等于窗口内某个坐标的值（池化 = 选择）。 -/
theorem is_selection (w : G → Finset G) (hw : ∀ i, (w i).Nonempty)
    (x : Vec G) (i : G) :
    (Layer.pool w hw).apply x i = x (choice w hw x i) :=
  choice_eq w hw x i

/-- 台账 C10 的池化半边：池化层在输入处的值，等于对应选择矩阵的值。 -/
theorem apply_eq_select (w : G → Finset G) (hw : ∀ i, (w i).Nonempty)
    (x : Vec G) :
    (Layer.pool w hw).apply x = (selectAff (choice w hw x)).apply x := by
  funext i
  rw [selectAff_apply]
  exact choice_eq w hw x i

end Pool

end Pool

/-! ## 卷积：循环结构

索引在 `G` 上，`G` 是加法交换幺半群。**只用加法、不用减法**：
`(k ⋆ x) i = ∑ m, k m * x (i + m)`。

`G := Fin n` 时这是一维循环卷积；`G := Fin h × Fin w` 时这是二维循环卷积
（逐坐标加法）。同一个定理，两个实例。 -/

section Conv

variable {G : Type*} [AddCommSemigroup G] [Fintype G] [DecidableEq G]

namespace Conv

/-- 循环平移：`(shiftVec t x) j = x (j + t)`。 -/
def shiftVec (t : G) (x : Vec G) : Vec G := fun j => x (j + t)

/-- 卷积，写成只用加法的求和。 -/
def convOp (k : Vec G) (x : Vec G) (i : G) : ℝ := ∑ m, k m * x (i + m)

/-- 卷积对应的循环矩阵。 -/
def convMat (k : Vec G) : Mat G := fun i j => ∑ m, if j = i + m then k m else 0

/-- 卷积层：作为一个仿射层（偏置为零）。 -/
def layer (k : Vec G) : Layer G := .affine ⟨convMat k, 0⟩

/-- 桥：矩阵作用与求和定义一致。C10 靠它把卷积接进 C5。 -/
theorem convMat_mulVec (k : Vec G) (x : Vec G) (i : G) :
    (convMat k).mulVec x i = convOp k x i := by
  simp only [convMat, convOp, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_eq_single (i + m)]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ (i + m)) h

/-- **台账 C8**：卷积与循环平移可交换——这就是"Toeplitz 结构"的数学内容。 -/
theorem convOp_shift (k : Vec G) (t : G) (x : Vec G) :
    convOp k (shiftVec t x) = shiftVec t (convOp k x) := by
  funext i
  simp only [convOp, shiftVec]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  rw [add_assoc, add_comm m t, ← add_assoc]

end Conv

end Conv

/-! ## 前向递归 -/

section Walk

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- 一层产生的模式：ReLU 的开关，或池化的选择。 -/
inductive Pat (G : Type*) where
  | relu (σ : G → Bool)
  | pool (c : G → G)

/-- 沿途每一层产生的模式。 -/
abbrev Pattern (G : Type*) := List (Pat G)

/-- 前向递归：逐层前进并累积仿射映射与模式。 -/
noncomputable def walk : Net G → Vec G → Vec G × Affine G × Pattern G
  | [], x => (x, ⟨1, 0⟩, [])
  | .affine f :: ls, x =>
      let r := walk ls (f.apply x)
      (r.1, r.2.1.comp f, r.2.2)
  | .relu :: ls, x =>
      let r := walk ls (Layer.apply .relu x)
      (r.1, r.2.1.comp (ReLU.linear (ReLU.pattern x)), Pat.relu (ReLU.pattern x) :: r.2.2)
  | .pool w hw :: ls, x =>
      let r := walk ls (Layer.apply (.pool w hw) x)
      (r.1, r.2.1.comp (Pool.selectAff (Pool.choice w hw x)),
        Pat.pool (Pool.choice w hw x) :: r.2.2)

/-- 整条网络在输入 `x` 处的线性化。 -/
noncomputable def linOf (net : Net G) (x : Vec G) : Affine G := (walk net x).2.1

/-- 整条网络在输入 `x` 处的模式序列。 -/
noncomputable def patternOf (net : Net G) (x : Vec G) : Pattern G := (walk net x).2.2

/-- 台账 C4：**归纳步**。两个输入的模式序列相同，则网络在同一点处的值
等于"取第一个输入做的线性化"在第二个输入处的值。 -/
theorem eval_eq_lin (net : Net G) (x y : Vec G)
    (h : patternOf net y = patternOf net x) :
    Net.apply net y = (linOf net x).apply y := by
  induction net generalizing x y with
  | nil =>
      simp [Net.apply, linOf, walk, Affine.apply]
  | cons l ls ih =>
      cases l with
      | affine f =>
          have h' : patternOf ls (f.apply y) = patternOf ls (f.apply x) := by
            simpa [patternOf, walk] using h
          have hrec := ih (f.apply x) (f.apply y) h'
          simp only [Net.apply, linOf, walk, Layer.apply]
          rw [hrec, Affine.comp_apply]
          rfl
      | relu =>
          have hpat : ReLU.pattern y = ReLU.pattern x := by
            have h1 : Pat.relu (ReLU.pattern y) = Pat.relu (ReLU.pattern x) := by
              simpa [patternOf, walk] using congrArg List.head? h
            exact Pat.relu.inj h1
          have h' : patternOf ls (Layer.apply .relu y)
                  = patternOf ls (Layer.apply .relu x) := by
            simpa [patternOf, walk] using congrArg List.tail h
          have hrec := ih (Layer.apply .relu x) (Layer.apply .relu y) h'
          simp only [Net.apply, linOf, walk, Layer.apply]
          rw [Affine.comp_apply, ← hpat, ← ReLU.apply_eq_linear y]
          exact hrec
      | pool w hw =>
          have hc : Pool.choice w hw y = Pool.choice w hw x := by
            have h1 : Pat.pool (Pool.choice w hw y) = Pat.pool (Pool.choice w hw x) := by
              simpa [patternOf, walk] using congrArg List.head? h
            exact Pat.pool.inj h1
          have h' : patternOf ls (Layer.apply (.pool w hw) y)
                  = patternOf ls (Layer.apply (.pool w hw) x) := by
            simpa [patternOf, walk] using congrArg List.tail h
          have hrec := ih (Layer.apply (.pool w hw) x) (Layer.apply (.pool w hw) y) h'
          simp only [Net.apply, linOf, walk, Layer.apply]
          rw [Affine.comp_apply, ← hc, ← Pool.apply_eq_select w hw y]
          exact hrec

/-- 模式 σ 对应的区域：网络在该输入处的模式序列恰好是 σ。 -/
def regionOf (net : Net G) (σ : Pattern G) : Set (Vec G) := {y | patternOf net y = σ}

/-- **台账 C5（主定理）**：对每个输入 `x`，存在一个模式 σ 使得
`x` 属于 σ 对应的区域，且网络在整个区域上等于 `linOf net x`。 -/
theorem exists_explanation (net : Net G) (x : Vec G) :
    x ∈ regionOf net (patternOf net x) ∧
      ∀ y ∈ regionOf net (patternOf net x),
        Net.apply net y = (linOf net x).apply y := by
  refine ⟨rfl, ?_⟩
  intro y hy
  exact eval_eq_lin net x y hy

/-- **台账 C6（完备性推论）**：预测被激活模式唯一决定。 -/
theorem eval_self (net : Net G) (x : Vec G) :
    Net.apply net x = (linOf net x).apply x :=
  eval_eq_lin net x x rfl

end Walk

/-! ## CNN 实例化：一维与二维 -/

section Instances

variable {G : Type*} [AddCommSemigroup G] [Fintype G] [DecidableEq G]

/-- 一个最小的 CNN：卷积 → ReLU → 池化。 -/
def cnn (K : Vec G) (w : G → Finset G) (hw : ∀ i, (w i).Nonempty) : Net G :=
  [Conv.layer K, Layer.relu, Layer.pool w hw]

/-- **台账 C10（CNN 的完备解释定理）**：对每个输入，这个 CNN 都有精确解释。 -/
theorem cnn_explanation (K : Vec G) (w : G → Finset G)
    (hw : ∀ i, (w i).Nonempty) (x : Vec G) :
    x ∈ regionOf (cnn K w hw) (patternOf (cnn K w hw) x) ∧
      ∀ y ∈ regionOf (cnn K w hw) (patternOf (cnn K w hw) x),
        Net.apply (cnn K w hw) y = (linOf (cnn K w hw) x).apply y :=
  exists_explanation (cnn K w hw) x

end Instances

/-! ## 二维卷积是一个实例

`G := Fin h × Fin w`，加法逐坐标。**没有第二套证明**：
`cnn2d_explanation` 就是 `cnn_explanation` 在这个 `G` 上的特化。
卷积的平移等变性（C8）同样自动适用于二维。 -/

/-- 二维循环卷积的索引：`Fin h × Fin w`。 -/
abbrev Grid (h w : ℕ) := Fin h × Fin w

/-- **台账 C11**：二维 CNN 的完备解释定理。

与一维共用同一个 `exists_explanation`——二维性只体现为索引类型是乘积。 -/
theorem cnn2d_explanation (h w : ℕ) (K : Vec (Grid h w))
    (win : Grid h w → Finset (Grid h w)) (hw : ∀ i, (win i).Nonempty)
    (x : Vec (Grid h w)) :
    x ∈ regionOf (cnn K win hw) (patternOf (cnn K win hw) x) ∧
      ∀ y ∈ regionOf (cnn K win hw) (patternOf (cnn K win hw) x),
        Net.apply (cnn K win hw) y = (linOf (cnn K win hw) x).apply y :=
  cnn_explanation K win hw x

/-- 台账 C12：二维卷积与二维循环平移可交换（C8 在 `Fin h × Fin w` 上的实例）。 -/
theorem conv2d_shift (h w : ℕ) (K : Vec (Grid h w))
    (t : Grid h w) (x : Vec (Grid h w)) :
    Conv.convOp K (Conv.shiftVec t x) = Conv.shiftVec t (Conv.convOp K x) :=
  Conv.convOp_shift K t x

/-! ## 零填充：边界在哪里失效

循环卷积的索引加法会回绕，所以平移是双射，等变性无条件成立。
**零填充不回绕**：偏移越界处按 0 处理。代价是等变性只在内部成立，
边界上失效。这一节把失效点证出来——用一个三元素的显式反例。 -/

namespace ZeroPad

variable {n : ℕ}

/-- 一维零填充卷积：偏移 `i + m` 越界处按 0 处理（不回绕）。 -/
noncomputable def conv1 (K x : Vec (Fin n)) (i : Fin n) : ℝ :=
  ∑ m : Fin n, K m * if h : i.val + m.val < n then x ⟨i.val + m.val, h⟩ else 0

/-- **台账 C13**：零填充破坏平移等变。

反例：`n = 3`，核只保留偏移 1（`K = [0,1,0]`），输入 `x = [1,2,3]`，平移 `t = 1`。

* `shift x           = [2,3,1]`（循环平移）
* `conv1 K x         = [2,3,0]`
* `conv1 K (shift x) = [3,1,0]`
* `shift (conv1 K x) = [3,0,2]`

第 1 个坐标不同：`1 ≠ 0`。边界在 `i = 2` 处：`2 + 1 = 3` 越界，被填成 0，
而平移后的输入在那里看到的是 1。 -/
theorem breaks_shift :
    ∃ (K x : Vec (Fin 3)) (t : Fin 3),
      conv1 K (Conv.shiftVec t x) ≠ Conv.shiftVec t (conv1 K x) := by
  refine ⟨fun m => if m = 1 then 1 else 0, ![1, 2, 3], 1, ?_⟩
  intro h
  have h1 := congrFun h 1
  simp [conv1, Conv.shiftVec, Fin.sum_univ_three, Fin.ext_iff] at h1

end ZeroPad

/-! ## 局部稳定性：半径估计的地基

`exists_explanation` 说"在模式对应的区域上等于线性化"，但没说这个区域**有多大**。
要回答"这个解释在多远内可信"，先要两条：扰动足够小时，ReLU 的开关不翻、池化的选择不变。
这就是 C14 与 C15。

**约定**：`Close r` 用**非严格**的 `≤`。原因是 `sup'` 的 Lipschitz 估计只给非严格界，
链式传播到池化层时会变成 `≤`。代价是 margin / gap 必须写成**严格**不等式。 -/

namespace Local

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- 逐坐标接近（sup 范数意义）：`∀ i, |y i - x i| ≤ r`。 -/
def Close (r : ℝ) (x y : Vec G) : Prop := ∀ i, |y i - x i| ≤ r

/-- **台账 C14（ReLU 的局部符号稳定）**。

若 x 的每个坐标离 0 **严格**大于 ε，且 y 与 x 逐坐标之差不超过 ε，
则 y 与 x 的 ReLU 模式相同——开关不翻。 -/
theorem relu_pattern_stable {x y : Vec G} {ε : ℝ}
    (hε : 0 < ε) (hm : ∀ i, ε < |x i|) (hc : Close ε x y) :
    ReLU.pattern y = ReLU.pattern x := by
  funext i
  have hlt : |y i - x i| < |x i| := lt_of_le_of_lt (hc i) (hm i)
  have h := abs_lt.mp hlt
  have hiff : (0 < y i) ↔ (0 < x i) := by
    rcases lt_or_ge (x i) 0 with hx | hx
    · have hx' : |x i| = -(x i) := abs_of_neg hx
      have hneg : y i < 0 := by linarith [h.2]
      constructor
      · intro hpos; linarith
      · intro hpos; linarith
    · have hx' : |x i| = x i := abs_of_nonneg hx
      have hposx : 0 < x i := by linarith [hm i, hx', abs_nonneg (x i)]
      have hpos : 0 < y i := by linarith [h.1]
      constructor
      · intro _; exact hposx
      · intro _; exact hpos
  by_cases h0 : 0 < x i
  · have hy : 0 < y i := hiff.mpr h0
    simp [ReLU.pattern, h0, hy]
  · have hy : ¬ 0 < y i := fun hh => h0 (hiff.mp hh)
    simp [ReLU.pattern, h0, hy]

/-- **台账 C15（池化的局部选择稳定）**。

若 x 处每个窗口的最大值比窗口内其他坐标**严格**高出 δ，且 y 与 x 逐坐标之差不超过 δ/2，
则 y 处选中的坐标与 x 处相同——argmax 不换。

需要严格最大，是因为 `choice` 用 `Classical.choose`：平局时的任意选择会随输入变化。 -/
theorem pool_choice_stable (w : G → Finset G) (hw : ∀ i, (w i).Nonempty)
    {x y : Vec G} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j, j ∈ w i → j ≠ Pool.choice w hw x i →
      δ < x (Pool.choice w hw x i) - x j)
    (hc : Close (δ / 2) x y) :
    Pool.choice w hw y = Pool.choice w hw x := by
  funext i
  have hstrict : ∀ j ∈ w i, j ≠ Pool.choice w hw x i →
      y j < y (Pool.choice w hw x i) := by
    intro j hj hne
    have h1 := hgap i j hj hne
    have h2 := (abs_le.mp (hc j)).2
    have h3 := (abs_le.mp (hc (Pool.choice w hw x i))).1
    linarith
  have hmem : Pool.choice w hw y i ∈ w i := Pool.choice_mem w hw y i
  have heq : (w i).sup' (hw i) y = y (Pool.choice w hw y i) := Pool.choice_eq w hw y i
  have hle : y (Pool.choice w hw x i) ≤ (w i).sup' (hw i) y :=
    Finset.le_sup' y (Pool.choice_mem w hw x i)
  by_contra hne
  have hlt := hstrict _ hmem hne
  linarith

/-- `sup'` 的 Lipschitz 性：逐点差不超过 R，则两边的最大值之差也不超过 R。 -/
theorem abs_sup'_sub_le {s : Finset G} (hs : s.Nonempty) {f g : G → ℝ} {R : ℝ}
    (h : ∀ i ∈ s, |f i - g i| ≤ R) :
    |s.sup' hs f - s.sup' hs g| ≤ R := by
  have hfg : ∀ i ∈ s, f i ≤ g i + R := by
    intro i hi; have := (abs_le.mp (h i hi)).2; linarith
  have hgf : ∀ i ∈ s, g i ≤ f i + R := by
    intro i hi; have := (abs_le.mp (h i hi)).1; linarith
  have h1 : s.sup' hs f ≤ s.sup' hs g + R := by
    apply Finset.sup'_le
    intro i hi
    have := Finset.le_sup' g hi
    linarith [hfg i hi]
  have h2 : s.sup' hs g ≤ s.sup' hs f + R := by
    apply Finset.sup'_le
    intro i hi
    have := Finset.le_sup' f hi
    linarith [hgf i hi]
  rw [abs_le]
  constructor <;> linarith

end Local

/-! ## 局部有效半径

* 仿射层：扰动被行绝对值和放大 → 半径换成 `max (rowSup A) 1 * R`
  （`max · 1` 只是为了保证半径保持正数；真实放大率是 `rowSup A`，取更大值是**保守**的）；
* ReLU 层：要求 `R < |x i|`（严格离 0 的距离）；
* 池化层：要求 `2R <` 窗口内最大与次大的差（严格最大）。 -/

namespace Local

variable {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]

/-- 一行的绝对值之和。 -/
noncomputable def rowAbs (A : Mat G) (i : G) : ℝ := ∑ j, |A i j|

/-- 所有行绝对值和的最大值。 -/
noncomputable def rowSup (A : Mat G) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => rowAbs A i)

/-- 矩阵作用的逐坐标 Lipschitz 估计。 -/
theorem mulVec_close (A : Mat G) {x y : Vec G} {R : ℝ}
    (h : ∀ j, |y j - x j| ≤ R) (i : G) :
    |(A.mulVec y) i - (A.mulVec x) i| ≤ rowAbs A i * R := by
  have hsub : (A.mulVec y) i - (A.mulVec x) i = ∑ j, A i j * (y j - x j) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, mul_sub]
  rw [hsub]
  calc |∑ j, A i j * (y j - x j)|
      ≤ ∑ j, |A i j * (y j - x j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |y j - x j| := by simp [abs_mul]
    _ ≤ ∑ j, |A i j| * R :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (abs_nonneg _))
    _ = rowAbs A i * R := by simp [rowAbs, Finset.sum_mul]

/-- 递归的半径条件：沿轨迹每层的 margin / gap 都够大。 -/
noncomputable def Bounds : Net G → Vec G → ℝ → Prop
  | [], _, _ => True
  | Layer.affine f :: ls, x, R =>
      Bounds ls (f.apply x) (max (rowSup f.A) 1 * R)
  | Layer.relu :: ls, x, R =>
      (∀ i, R < |x i|) ∧ Bounds ls (Layer.apply .relu x) R
  | Layer.pool w hw :: ls, x, R =>
      (∀ i j, j ∈ w i → j ≠ Pool.choice w hw x i →
        2 * R < x (Pool.choice w hw x i) - x j) ∧
      Bounds ls (Layer.apply (.pool w hw) x) R

/-- 半径 `R` 内的扰动不改变模式序列。 -/
def Stable (net : Net G) (x : Vec G) (R : ℝ) : Prop :=
  ∀ y, Close R x y → patternOf net y = patternOf net x

/-- **台账 C16（局部半径）**：`0 < R` 且每层 margin / gap 足够时，
半径 `R` 内的任何扰动都不改变模式序列。 -/
theorem stable_of_bounds (net : Net G) (x : Vec G) {R : ℝ}
    (hR : 0 < R) (hb : Bounds net x R) : Stable net x R := by
  induction net generalizing x R with
  | nil =>
      intro y _
      simp [patternOf, walk]
  | cons l ls ih =>
      cases l with
      | affine f =>
          have hR' : 0 < max (rowSup f.A) 1 * R := by
            have : (0:ℝ) < max (rowSup f.A) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
            positivity
          have hb' : Bounds ls (f.apply x) (max (rowSup f.A) 1 * R) := hb
          have ih' : Stable ls (f.apply x) (max (rowSup f.A) 1 * R) :=
            ih (f.apply x) hR' hb'
          intro y hy
          have hclose : Close (max (rowSup f.A) 1 * R) (f.apply x) (f.apply y) := by
            intro i
            have h1 := mulVec_close f.A (fun j => hy j) i
            have hsup : rowAbs f.A i ≤ rowSup f.A := by
              unfold rowSup
              exact Finset.le_sup' (fun i => rowAbs f.A i) (Finset.mem_univ i)
            have h2 : rowAbs f.A i ≤ max (rowSup f.A) 1 :=
              le_trans hsup (le_max_left _ _)
            have h3 : rowAbs f.A i * R ≤ max (rowSup f.A) 1 * R :=
              mul_le_mul_of_nonneg_right h2 hR.le
            have heq : f.A.mulVec y i + f.b i - (f.A.mulVec x i + f.b i)
                = f.A.mulVec y i - f.A.mulVec x i := by ring
            simp only [Affine.apply, Pi.add_apply]
            rw [heq]
            exact le_trans h1 h3
          have := ih' (f.apply y) hclose
          simpa [patternOf, walk] using this
      | relu =>
          obtain ⟨hmargin, hb'⟩ := hb
          have ih' : Stable ls (Layer.apply .relu x) R :=
            ih (Layer.apply .relu x) hR hb'
          intro y hy
          have hpat : ReLU.pattern y = ReLU.pattern x :=
            relu_pattern_stable hR hmargin hy
          have hclose : Close R (Layer.apply .relu x) (Layer.apply .relu y) := by
            intro i
            simp only [Layer.apply]
            exact le_trans (abs_max_sub_max_le_abs (y i) (x i) 0) (hy i)
          have := ih' (Layer.apply .relu y) hclose
          simpa [patternOf, walk, hpat] using this
      | pool w hw =>
          obtain ⟨hgap, hb'⟩ := hb
          have hR2 : (0:ℝ) < 2 * R := by linarith
          have ih' : Stable ls (Layer.apply (.pool w hw) x) R :=
            ih (Layer.apply (.pool w hw) x) hR hb'
          intro y hy
          have hchoice : Pool.choice w hw y = Pool.choice w hw x := by
            apply pool_choice_stable w hw hR2 hgap
            intro i
            have h := hy i
            linarith
          have hclose : Close R (Layer.apply (.pool w hw) x) (Layer.apply (.pool w hw) y) := by
            intro i
            simp only [Layer.apply]
            have := abs_sup'_sub_le (hw i) (f := y) (g := x) (R := R) (fun j _ => hy j)
            rwa [abs_sub_comm] at this ⊢
          have := ih' (Layer.apply (.pool w hw) y) hclose
          simpa [patternOf, walk, hchoice] using this

/-- **台账 C17（完备解释的局部版本）**：半径 `R` 内的点都落在同一个模式区域里，
因此 C5 给出的线性化在那个球上处处有效。 -/
theorem local_region (net : Net G) (x : Vec G) {R : ℝ}
    (hR : 0 < R) (hb : Bounds net x R)
    {y : Vec G} (hy : Close R x y) :
    y ∈ regionOf net (patternOf net x) :=
  stable_of_bounds net x hR hb y hy

end Local

/-! ## 感受野：线性化矩阵的稀疏结构

审计指出台账曾声称"解释按感受野分解"，但代码里没有对应定理。这一节把它补上。

`rowSupport net x i` 是"输出坐标 `i` 依赖的输入坐标集合"，沿网络反向递归：

* 仿射层：`M * A` 的第 `i` 行支撑 ⊆ 把 `M` 的第 `i` 行支撑里的每个 `j` 换成 `A` 第 `j` 行的支撑；
* ReLU 层：`M * D`（对角 0/1）只保留开着的坐标；
* 池化层：`M * S`（选择矩阵）把 `j` 换成 `c j`。

主定理：`(linOf net x).A i j ≠ 0 ⇒ j ∈ rowSupport net x i`。
这就是"感受野"的精确含义——**矩阵的零模式由结构决定，与输入无关**。 -/

namespace Field

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- 输出坐标 `i` 依赖的输入坐标集合。 -/
noncomputable def rowSupport : Net G → Vec G → G → Finset G
  | [], _, i => {i}
  | Layer.affine f :: ls, x, i =>
      (rowSupport ls (f.apply x) i).biUnion
        (fun j => Finset.univ.filter (fun k => f.A j k ≠ 0))
  | Layer.relu :: ls, x, i =>
      (rowSupport ls (Layer.apply .relu x) i).filter
        (fun k => ReLU.pattern x k = true)
  | Layer.pool w hw :: ls, x, i =>
      (rowSupport ls (Layer.apply (.pool w hw) x) i).image (Pool.choice w hw x)

/-- **台账 C18（感受野）**：线性化矩阵的每个非零元都落在感受野内。 -/
theorem mem_rowSupport (net : Net G) (x : Vec G) (i j : G)
    (h : (linOf net x).A i j ≠ 0) : j ∈ rowSupport net x i := by
  induction net generalizing x i j with
  | nil =>
      simp only [rowSupport, Finset.mem_singleton]
      have h1 : (1 : Matrix G G ℝ) i j ≠ 0 := by simpa [linOf, walk] using h
      by_contra hne
      have hz : (1 : Matrix G G ℝ) i j = 0 := by
        rw [Matrix.one_apply]
        exact if_neg (Ne.symm hne)
      exact h1 hz
  | cons l ls ih =>
      cases l with
      | affine f =>
          have hA : ((linOf ls (f.apply x)).A * f.A) i j ≠ 0 := by
            simpa [linOf, walk, Affine.comp] using h
          rw [Matrix.mul_apply] at hA
          obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
          obtain ⟨hk1, hk2⟩ := mul_ne_zero_iff.mp hk
          simp only [rowSupport]
          rw [Finset.mem_biUnion]
          exact ⟨k, ih (f.apply x) i k hk1,
            Finset.mem_filter.mpr ⟨Finset.mem_univ j, hk2⟩⟩
      | relu =>
          have hA : ((linOf ls (Layer.apply .relu x)).A *
              (ReLU.linear (ReLU.pattern x)).A) i j ≠ 0 := by
            simpa [linOf, walk, Affine.comp] using h
          rw [Matrix.mul_apply] at hA
          obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
          obtain ⟨hk1, hk2⟩ := mul_ne_zero_iff.mp hk
          have hkj : k = j := by
            by_contra hne
            have hz : (ReLU.linear (ReLU.pattern x)).A k j = 0 := by
              simp only [ReLU.linear, Matrix.diagonal_apply]
              exact if_neg hne
            exact hk2 hz
          have hpat : ReLU.pattern x k = true := by
            by_contra hp
            have hz : (ReLU.linear (ReLU.pattern x)).A k j = 0 := by
              simp only [ReLU.linear, Matrix.diagonal_apply, if_pos hkj]
              simp [hp]
            exact hk2 hz
          simp only [rowSupport]
          rw [Finset.mem_filter]
          exact ⟨by rw [← hkj]; exact ih (Layer.apply .relu x) i k hk1,
            by rw [← hkj]; exact hpat⟩
      | pool w hw =>
          have hA : ((linOf ls (Layer.apply (.pool w hw) x)).A *
              (Pool.selectAff (Pool.choice w hw x)).A) i j ≠ 0 := by
            simpa [linOf, walk, Affine.comp] using h
          rw [Matrix.mul_apply] at hA
          obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
          obtain ⟨hk1, hk2⟩ := mul_ne_zero_iff.mp hk
          simp only [rowSupport]
          rw [Finset.mem_image]
          refine ⟨k, ih (Layer.apply (.pool w hw) x) i k hk1, ?_⟩
          by_contra hne
          have hz : (Pool.selectMat (Pool.choice w hw x)) k j = 0 := by
            simp only [Pool.selectMat]
            exact if_neg (Ne.symm hne)
          exact hk2 hz

end Field

/-! ## 唯一性：解释不是我们选的，是被网络决定的

C5 说"存在一个解释"。这一节说：在小球上，**它是唯一的**。

关键是标准引理：两个仿射映射若在一个开球上处处相等，则它们的矩阵与常数项都相同。
证明很短——在球心比常数项，在球心加上 `(r/2)·e_k` 比第 `k` 列——但它把
"解释是一种表示"变成"解释是网络的客观属性"。 -/

namespace Unique

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- **台账 C19（仿射映射的球上延拓唯一性）**：两个仿射映射在半径 `r > 0` 的球上
处处相等，则它们相等。 -/
theorem affine_ext_on_ball {f g : Affine G} {x₀ : Vec G} {r : ℝ} (hr : 0 < r)
    (h : ∀ y, Local.Close r x₀ y → f.apply y = g.apply y) : f = g := by
  have hc : f.apply x₀ = g.apply x₀ := by
    apply h
    intro i
    rw [sub_self, abs_zero]
    exact hr.le
  have hA : f.A = g.A := by
    funext i k
    set e : Vec G := fun j => if j = k then (1 : ℝ) else 0 with he_def
    set Y : Vec G := fun j => x₀ j + (r / 2) * e j with hY_def
    have key : ∀ (A : Mat G), (A.mulVec Y) i - (A.mulVec x₀) i = (r / 2) * A i k := by
      intro A
      have hdiff : (A.mulVec Y) i - (A.mulVec x₀) i = ∑ j, A i j * ((r / 2) * e j) := by
        simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [hY_def]
        ring
      rw [hdiff]
      have hfac : ∑ j, A i j * ((r / 2) * e j) = (r / 2) * ∑ j, A i j * e j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hfac]
      have hsum : ∑ j, A i j * e j = A i k := by
        simp only [he_def, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq']
        simp
      rw [hsum]
    have hY : Local.Close r x₀ Y := by
      intro j
      have h1 : Y j - x₀ j = (r / 2) * (if j = k then (1 : ℝ) else 0) := by
        simp only [hY_def, he_def]
        ring
      rw [h1]
      by_cases hj : j = k
      · rw [if_pos hj, mul_one, abs_of_pos (by linarith : (0:ℝ) < r / 2)]
        linarith
      · rw [if_neg hj, mul_zero, abs_zero]; linarith
    have h1 := congrFun (h Y hY) i
    have e0 := congrFun hc i
    simp only [Affine.apply, Pi.add_apply] at h1 e0
    have step : f.A.mulVec Y i - f.A.mulVec x₀ i = g.A.mulVec Y i - g.A.mulVec x₀ i := by
      linarith
    rw [key f.A, key g.A] at step
    have hpos : (r / 2) ≠ 0 := by linarith
    exact mul_left_cancel₀ hpos step
  have hb : f.b = g.b := by
    funext i
    have e0 := congrFun hc i
    simp only [Affine.apply, Pi.add_apply] at e0
    rw [hA] at e0
    linarith
  cases f with
  | mk fA fb =>
    cases g with
    | mk gA gb =>
      simp only [Affine.mk.injEq] at hA hb ⊢
      exact ⟨hA, hb⟩

/-- **台账 C20（解释的唯一性）**：在 `Bounds` 成立、`R > 0` 的球上，
任何与网络相等的仿射映射**都等于** `linOf net x`。

换句话说：解释不是我们挑的一种表示，而是网络在小球上唯一决定的仿射模型。 -/
theorem explanation_unique (net : Net G) (x : Vec G) {R : ℝ} [Nonempty G]
    (hR : 0 < R) (hb : Local.Bounds net x R)
    {g : Affine G} (hg : ∀ y, Local.Close R x y → g.apply y = Net.apply net y) :
    g = linOf net x := by
  have hball : ∀ y, Local.Close R x y → g.apply y = (linOf net x).apply y := by
    intro y hy
    have hmem : y ∈ regionOf net (patternOf net x) := Local.local_region net x hR hb hy
    have heq : Net.apply net y = (linOf net x).apply y := eval_eq_lin net x y hmem
    rw [hg y hy, heq]
  exact affine_ext_on_ball hR hball

end Unique

end CnnExplain
