import Mathlib

/-!
# __LIB__：骨架

约定（对应 WORKFLOW.md 的 P5–P6）：

* `docs/SPEC.md` 的定义台账，每一条在这里写成一个 `def`，系数逐字一致；
* `docs/LEMMAS.md` 的每条引理，写成一个 `theorem`/`lemma`，名字填进 `docs/CLAIMS.md`；
* 不允许 `sorry` / `admit` / 自定义 `axiom`；
* 每条主要定理都要在 `Audit.lean` 里 `#print axioms` 一次。

下面两个声明只是演示命名与写法，正式工作开始时可以删掉。
-/

namespace __LIB__

/-- 示例定义（替换成 SPEC 台账里的第一个对象）。 -/
def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k

/-- 示例引理：台账里「Lean 声明」一列写 `IsEven.add`。 -/
theorem IsEven.add (m n : ℕ) (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  exact ⟨a + b, by ring⟩

end __LIB__
