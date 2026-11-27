import CnnExplain

/-!
# 公理审计

不属于库的构建目标，单独运行：

    lake env lean Audit.lean

允许出现的公理：`propext`、`Classical.choice`、`Quot.sound`。
不允许：`sorryAx`，以及任何未登记在 `docs/CLAIMS.md` 的自定义公理。

**每新增一条状态为 `PROVED` 的命题，必须在这里加一行 `#print axioms`。**
`mathlean check` 会检查 `docs/CLAIMS.md` 里每个 `PROVED` 名字都能在这里找到。
-/

#print axioms CnnExplain.Affine.comp_apply
#print axioms CnnExplain.net_affine_apply
#print axioms CnnExplain.ReLU.apply_eq_linear
#print axioms CnnExplain.ReLU.boundary_agrees
#print axioms CnnExplain.eval_eq_lin
#print axioms CnnExplain.exists_explanation
#print axioms CnnExplain.eval_self
#print axioms CnnExplain.Conv.convOp_shift
#print axioms CnnExplain.Pool.is_selection
#print axioms CnnExplain.cnn_explanation
#print axioms CnnExplain.cnn2d_explanation
#print axioms CnnExplain.conv2d_shift
#print axioms CnnExplain.ZeroPad.breaks_shift
#print axioms CnnExplain.Local.relu_pattern_stable
#print axioms CnnExplain.Local.pool_choice_stable
#print axioms CnnExplain.Local.stable_of_bounds
#print axioms CnnExplain.Local.local_region
#print axioms CnnExplain.Field.mem_rowSupport
#print axioms CnnExplain.Unique.affine_ext_on_ball
#print axioms CnnExplain.Unique.explanation_unique
