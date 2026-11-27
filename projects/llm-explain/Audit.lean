import LlmExplain

/-!
# 公理审计

不属于库的构建目标，单独运行：

    lake env lean Audit.lean

允许出现的公理：`propext`、`Classical.choice`、`Quot.sound`。
不允许：`sorryAx`，以及任何未登记在 `docs/CLAIMS.md` 的自定义公理。

**每新增一条状态为 `PROVED` 的命题，必须在这里加一行 `#print axioms`。**
`mathlean check` 会检查 `docs/CLAIMS.md` 里每个 `PROVED` 名字都能在这里找到。
-/

#print axioms LlmExplain.exp_sum_pos
#print axioms LlmExplain.softmax_pos
#print axioms LlmExplain.softmax_sum
#print axioms LlmExplain.attn_range
#print axioms LlmExplain.softmax_shift
#print axioms LlmExplain.softmax_mono
#print axioms LlmExplain.Gap.softmax_ge_of_gap
#print axioms LlmExplain.Gap.hard_attn_error
#print axioms LlmExplain.rms_smul
#print axioms LlmExplain.block_range
#print axioms LlmExplain.block_close_to_hard
#print axioms LlmExplain.softmax_monotone
#print axioms LlmExplain.softmax_variance_nonneg
#print axioms LlmExplain.attn_value_lipschitz
#print axioms LlmExplain.block_lipschitz
#print axioms LlmExplain.shift_inv_forces_multiplicative
#print axioms LlmExplain.exp_weight_shift_invariant
#print axioms LlmExplain.linLayer_comp
#print axioms LlmExplain.residual_cross_term
#print axioms LlmExplain.attention_contracts
#print axioms LlmExplain.attn_injective
#print axioms LlmExplain.softmax_eq_iff_shift
#print axioms LlmExplain.card_le_of_affinelyIndependent
#print axioms LlmExplain.ker_finrank_ge
#print axioms LlmExplain.fiber_contains
#print axioms LlmExplain.exists_second_explanation
