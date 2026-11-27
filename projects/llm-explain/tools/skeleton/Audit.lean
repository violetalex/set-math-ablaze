import __LIB__

/-!
# 公理审计

不属于库的构建目标，单独运行：

    lake env lean Audit.lean

允许出现的公理：`propext`、`Classical.choice`、`Quot.sound`。
不允许：`sorryAx`，以及任何未登记在 `docs/CLAIMS.md` 的自定义公理。

**每新增一条状态为 `PROVED` 的命题，必须在这里加一行 `#print axioms`。**
`mathlean check` 会检查 `docs/CLAIMS.md` 里每个 `PROVED` 名字都能在这里找到。
-/

#print axioms __LIB__.IsEven.add
