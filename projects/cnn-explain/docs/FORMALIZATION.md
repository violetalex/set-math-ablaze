# P5 形式化映射：哪些能直接借 Mathlib，哪些要自建

> 口径：`easy` = 新定义 + 几十行；`medium` = 需要归纳或构造；`hard` = 需要新建一层理论；
> `not-feasible` = Mathlib 缺关键工具且短期内补不上。
> **所有"已有"一栏的名字都用 `#check` 验证过**（`/tmp/cnncheck/Check.lean`，EXIT=0）。

## 1. 已确认可用的 Mathlib 工具

| 用途 | 名字 |
|---|---|
| 矩阵作用于向量是线性的 | `Matrix.mulVec_add`, `Matrix.add_mulVec` |
| 矩阵乘法与 `mulVec` 相容（复合的代数） | `Matrix.mulVec_mulVec` |
| 单位/零矩阵 | `Matrix.one_mulVec`, `Matrix.zero_mulVec` |
| ReLU 两个分支 | `max_eq_left`, `max_eq_right`, `le_max_left`, `max_le` |
| 有限和分配律 | `Finset.sum_add_distrib` |
| 集合交集上的谓词 | `Set.mem_iInter` |

**没有被验证到的**（不要写进论文）：`Matrix.mulVec_sub`、向量的有序性引理。
需要时先 `#check`。

## 2. 逐条评估

| 台账 | 要建什么 | 已有 | 缺什么 | 成本 |
|---|---|---|---|---|
| C1 | `Affine n := Mat n × Vec n` 及 `comp` | 上面 5 条矩阵引理 | 只是拼装 | **easy** |
| C2 | 单层仿射的 `linOf` 恒等 | `Matrix.one_mulVec` | — | **easy** |
| C3 | 单层 ReLU 的两分支 | `max_eq_left/right` | — | **easy** |
| C4 | 归纳步：`Net` 是 `List (Layer n)`，对列表归纳 | 无现成 | 需要 `Pattern`、`region` 的定义，以及"交集仍在区域内"的簿记 | **medium** |
| C5 | 主定理：构造 σ 并证 `x ∈ region σ` | — | 由 C4 直接得到 | **easy（依赖 C4）** |
| C6 | 推论 | — | 一行 | **easy** |
| C7 | 边界相容（`max 0 0 = 0`） | `max_eq_right` 等 | — | **easy** |
| C8 | `conv K` 写成 Toeplitz 型矩阵 | `Matrix` | 索引簿记（`Fin` 上的加法要处理越界） | **medium** |
| C9 | 最大池化 = 取 argmax 的选择矩阵 | `Finset.sup'` | 并列时的选取必须固定，否则不是函数 | **medium** |
| C10 | CNN 实例化 C5 | — | 由 C5/C8/C9 | **easy** |

**没有任何一条是 `not-feasible`。** 这是选"精确但不紧凑"这个定义的直接回报：
它不需要新的分析工具，只需要有限维线性代数 + 列表归纳。

对照：论文 A 的 31 条里有 9 条 `not-feasible`（缺 Feynman–Kac / 抛物极值原理）。
**同一个工作流，缺口分布完全不同——这本身就是 P5 该给出的信息。**

## 3. 风险排序

1. **C4 的归纳簿记**是真正的瓶颈。`region` 是逐层前激活值的符号条件，
   而第 l 层的前激活值本身依赖于前 l−1 层的模式。定义顺序一旦写错，
   后面全部卡住。建议：先把 `region` 定义成"对每一层，用**已经线性化的**前驱算出的
   前激活值满足符号条件"，这样它是递归定义的、不是同时定义的。
2. **`Fin n` 上的索引算术**（C8）。卷积要处理 `i + k` 越界，标准做法是把填充写成
   显式的 `if` 或扩维，不要试图用 `Fin` 的模运算。
3. **C9 的并列**。最大池化在并列时取第一个还是任意一个，必须写死；否则
   `pool` 不是函数，C5 的前提就不成立。

## 4. 建议的推进顺序

```
C1 → C2 → C3 → C7 → C4 → C5 → C6        （第一阶段，约 2–4 周）
C8 → C9 → C10                           （第二阶段，约 3–4 周）
```

**先把 C7 放在 C4 之前**：它是 C3 的直接推论，但能让符号约定（`z=0` 归关分支）
在写归纳之前就被钉死。经验上，边界约定是这类形式化最容易返工的地方。

## 5. 不在本文件判断的

成本分级是对 **Lean/Mathlib 落地工作量**的估计，不是对命题真伪的判断。
C5 的真伪由数学决定，不由本文件决定。
