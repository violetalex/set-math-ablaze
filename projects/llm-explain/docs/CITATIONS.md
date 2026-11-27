# 文献核实记录（P1）

> 目的不是收集引用，而是回答一个问题：**本工程这 28 条里，有没有哪条是新的。**
> 规则：每条必须带可检索标识符；查不到就写"未核实"。

## 方法

`https://export.arxiv.org/api/query` 按摘要检索（dblp 有反爬墙、Semantic Scholar 限流、
Crossref 的 `query.bibliographic` 对泛标题匹配极差——这三个坑在 `mathlean` 仓库的
`docs/CITATIONS.md` 里已记录）。检索式见下方各条。

## 结论：**前 22 条没有一条是新的；C23–C28 未找到对应**（见第二轮）

| 本工程 | 文献对应 | 标识符 |
|---|---|---|
| C22 注意力收缩 / rank collapse | Dong, Cordonnier, Loukas, *Attention is Not All You Need: Pure Attention Loses Rank Doubly Exponentially with Depth* | `arXiv:2103.03404` |
| C22 的后续（收缩机制的谱分析） | *Mind the Gap: a Spectral Analysis of Rank Collapse and Signal Propagation in Attention Layers* | `arXiv:2410.07799` |
| C22 的后续（残差阻止收缩） | *Lambda-Skip Connections: the architectural component that prevents Rank Collapse* | `arXiv:2410.10609` |
| softmax 的 `1/2` Lipschitz 常数 | *Softmax is 1/2-Lipschitz: A tight bound across all ℓ_p norms* | `arXiv:2510.23012` |
| C8 硬注意力逼近 | *Simulating Hard Attention Using Soft Attention* | `arXiv:2412.09925` |
| C1–C3、C12 的 softmax 性质 | *On the Properties of the Softmax Function with Application in Game Theory and Reinforcement Learning* | `arXiv:1704.00805` |
| C20 线性注意力复合 | 线性注意力等价性文献（多篇），属 folklore | 检索到多篇，未逐一核 |

**检索式**（可复现）：
- `abs:"rank collapse" AND abs:"attention"`
- `abs:"token uniformity"`
- `abs:"softmax" AND abs:"Lipschitz"`
- `abs:"hard attention" AND abs:"softmax"`

## 唯一可能的新意：形式化本身

检索 `abs:"Lean 4" AND abs:"transformer"`、`abs:"Lean" AND abs:"attention" AND abs:"formalization"`、
`abs:"proof assistant" AND abs:"neural network"`，命中的是：

- *Formal Analysis of the Sigmoid Function and Formal Proof of the Universal Approximation
  Theorem*（`arXiv:2512.03635`）——神经网络理论的形式化，但不是 Lean、不是注意力；
- *Taming Differentiable Logics with Coq Formalisation*（`arXiv:2403.13700`）——Coq；
- 若干 Lean 数学形式化，与 transformer 无关。

**没有发现 Lean 4 / Mathlib 里对注意力结构性质（收缩、gap 界、单调性）的形式化。**

**这只能作为"未发现"，不能作为"不存在"**：单次 API 检索不构成完备性证明。论文若
要主张"首个"，必须写成"to our knowledge"，并接受被指出反例的风险。

## 第二轮：可逆性结果（C23–C25）

检索式与结果：

| 检索式 | 命中 |
|---|---|
| `abs:"attention" AND abs:"identifiab"` | **0** |
| `abs:"attention" AND abs:"invertib"` | **0** |
| `abs:"affinely independent" AND abs:"attention"` | **0** |
| `abs:"attention weights" AND abs:"recover"` | 5 篇，见下 |
| `abs:"attention" AND abs:"output" AND abs:"weights" AND abs:"unique"` | 4 篇，均非本问题 |

**唯一相邻的工作**：Deng, Song, Xie, Yang, *Unmasking Transformers: A Theoretical
Approach to Data Recovery via Attention Weights*, `arXiv:2310.12462`（2023-10）。

它问的是：**给定注意力权重与输出，能否恢复输入数据 `X`**——即 `(W, B) → X`。

本工程问的是：**给定值与输出，能否恢复权重 `p`**——即 `(v, out) → p`。

**方向相反**。两者不重叠：他们是"从注意力反推数据"，我们是"从数据与输出反推注意力"。

### 诚实的判断

- 数学内容是**标准线性代数**：`n` 个点仿射无关要求 `n − 1 ≤ d`，任何线性代数课都会讲。
  一位专家会说"这是显然的"。所以它的价值**不在深度，在问法**——把注意力当反问题看，
  得出"长序列下注意力图不可恢复"这个结论，并把它写成充要条件。
- "检索没命中"**不等于**"文献里没有"。摘要检索会漏掉只在正文里陈述的结果。
  论文只能写 "to our knowledge"，不能写"首个"。
- 一个必须承认的风险：这可能是若干论文里的**脚注或显然推论**，只是没人当主结果写。

## 第三轮：论文参考文献

论文 `paper/main.tex` 引了 15 条。逐条状态：

| 条目 | 标识符 | 来源 |
|---|---|---|
| Luce 1959 | doi:10.1037/14396-000（**指 2005 Dover 重印本**，ISBN 978-0-486-44136-8） | Crossref 解析 |
| McFadden 1974 | 无章节 DOI；书目由 Crossref 记录 doi:10.1017/S0770451800103604 佐证 | Crossref |
| Dong et al. 2021 | arXiv:2103.03404 | 第一轮 |
| Mind the Gap 2024 | arXiv:2410.07799 | 第一轮 |
| Lambda-Skip 2024 | arXiv:2410.10609 | 第一轮 |
| Softmax is 1/2-Lipschitz 2025 | arXiv:2510.23012 | 第一轮 |
| Simulating Hard Attention 2024 | arXiv:2412.09925 | 第一轮 |
| Unmasking Transformers 2023 | arXiv:2310.12462 | 第二轮 |
| Montúfar et al. 2014 | arXiv:1402.1869 | 另一工程的 P1（同法核实） |
| Telgarsky 2016 | arXiv:1602.04485 | 同上 |
| Arora et al. 2018 | arXiv:1611.01491 | 同上（arXiv `journal_ref` 误写 "ICLR 2028"，PDF 页眉为 ICLR 2018） |
| Ribeiro et al. 2016 (LIME) | arXiv:1602.04938 | 同上 |
| Lundberg & Lee 2017 (SHAP) | arXiv:1705.07874 | 同上 |
| Selvaraju et al. 2017 (Grad-CAM) | arXiv:1610.02391；doi:10.1109/ICCV.2017.74 | 同上 |
| Sundararajan et al. 2017 (IG) | arXiv:1703.01365 | 同上 |

**Lucе 与 McFadden 的两处书目限定已写进正文**，不是藏在文献表里：
DOI 指向重印本、McFadden 无章节 DOI。若审稿人要求 1959 原版的书目，需要另找 ISBN。

## 未核实项（不得进入正文）

- ~~Luce (1959)、McFadden (1974)~~——**已核实，见第三轮**：Luce 的 DOI 指 2005 重印本；
  McFadden 无章节 DOI，书目由 Crossref 记录佐证。论文已引，并写出两处限定。
- C19 的 Cauchy 分类：经典函数方程理论，**仍未核实具体出处，不得进入正文**。

## 对论文的含义

这个项目的贡献**不能**写成"我们证明了关于 transformer 的新定理"。正确的写法是：

> 我们给出一组关于 softmax 注意力的结构事实的**机器验证**，其中最重要的收缩性质
> 是已知结果（Dong et al.）的显式常数版本；所有数学内容均可在文献中找到对应，
> 本工作的增量在于形式化与一个统一的、可复现的证据台账。

在这个前提下，`docs/SPEC.md` §7 的"不可写的"清单要再加一条：
**不可写"这些是新定理"。**
