import Liouville

/-!
# 公理审计

不属于库的构建目标，单独运行：

    lake env lean Audit.lean

允许出现的公理：`propext`、`Classical.choice`、`Quot.sound`。

**每新增一条状态为 `PROVED` 的命题，必须在这里加一行 `#print axioms`。**
`mathlean check` 会检查 `docs/CLAIMS.md` 里每个 `PROVED` 名字都能在这里找到。

只审计顶层陈述（台账里的名字）：公理依赖是传递的，
`#print axioms Liouville.PhiExt_bound` 已经把整条证明链路上的引理都盖住了。
-/

#print axioms Liouville.PhiExt_bound
#print axioms Liouville.PhiExt_bound_tendsto
