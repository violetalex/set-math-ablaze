<!-- mathlean:template 脚手架占位：被真实阶段产物覆盖后本行消失 -->
# 命题台账

> 唯一真相。论文里每一句"我们证明了……"都必须能追到这里的某一行。
> 由 `mathlean check` 的 `ledger` 门自动检查（工程里是 `bash scripts/check.sh`）。

## 状态取值

| 状态 | 含义 | 额外要求 |
|---|---|---|
| `PROVED` | Lean 4 机器验证通过 | 「Lean 声明」列是真实声明名，且 `Audit.lean` 里有 `#print axioms` |
| `PROVED-INFORMAL` | 只有人类证明 | 备注写"未形式化"及原因 |
| `CONDITIONAL` | 在若干假设下成立 | 备注必须写「假设：……」 |
| `OPEN` | 没有证明，也没有反例 | 备注写卡在哪里 |
| `REFUTED` | 有反例 | 备注必须写「反例：……」 |
| `INFORMAL-ONLY` | 依赖 Mathlib 缺失的工具 | 备注写缺什么 |

## 台账

<!-- 六列，缺一列检查脚本会跳过该行；ID 用 C1、C2… -->

| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |
|---|---|---|---|---|---|
| _ | OPEN | （第一条命题写在这里） | — | — | （占位行，检查时忽略） |

## 写法示例

```
| C1 | PROVED | 若 b^ρ ≥ 0 则 Γ ≡ 0 | IsEven.add | — | 论文定理 1.1 |
| C2 | CONDITIONAL | 逃逸平台处 Γ ≡ 0 | — | C1 | 假设：ρ ≳ (−t)^{1/4} 且 |Γ| ≥ L/2 |
| C4 | REFUTED | V = −4νρ/(1+ρ²) 是反例 | — | — | 反例：加权无散条件失效 |
```

- 「Lean 声明」填源码里 `theorem`/`lemma` 后面的名字（`IsEven.add` 或全名 `Lib.IsEven.add` 均可）。
- 填了 `PROVED` 却没在 `Audit.lean` 里 `#print axioms`，检查脚本会报错——这正是要防的。

## 与论文的对应

| 论文位置 | 台账 ID |
|---|---|
| （定理 1.1） | C1 |

## 变更记录

- YYYY-MM-DD：C2 由 PROVED 降级为 CONDITIONAL，原因 ……
- YYYY-MM-DD：C4 撤回原证明，改为反例 ……
