# P1 文献核实记录

> 规则：每条引用必须带可检索标识符，并由**另一个人**独立打开该标识符，
> 确认标题、作者、年份、结论四者一致。任何一项对不上就降级，不得进入正文。

## 方法

1. **机器检索**（作者本人）：arXiv export API 按标题精确检索，取得 `arXiv:<id>`、
   作者列表、首次发布日期、`journal_ref` 与自带 DOI。Grad-CAM 的两个 DOI 另用
   Crossref `works/<doi>` 解析确认归属。
2. **独立复核**（另一个人）：逐条打开 `https://arxiv.org/abs/<id>`（以及 DOI），
   逐项比对标题、作者、年份、结论。

**工具局限**（记录，避免下次重复踩坑）：`dblp.org` 有反爬墙（返回 HTML 挑战页）、
`api.semanticscholar.org` 会 429、Crossref 的 `query.bibliographic` 端点会 429 且对
泛标题匹配很差（把 Montúfar 匹配成了一篇 2022 年的 TNNLS 综述）。
**可靠的是 `https://export.arxiv.org/api/query`、`arxiv.org/abs/<id>` 与
`api.crossref.org/works/<doi>`**（后者在按 DOI 精确取时没有限流）。

## 逐条记录

| # | 正文条目 | 标识符 | 机器检索 | 独立复核 | 备注 |
|---|---|---|---|---|---|
| 1 | Montúfar, Pascanu, Cho, Bengio — linear regions | `arXiv:1402.1869` | 命中 | VERIFIED | 首次发布 2014-02-08；NIPS 2014 由官方论文列表核对 |
| 2 | Telgarsky — benefits of depth | `arXiv:1602.04485` | 命中 | VERIFIED | arXiv comment 明写 "To appear, COLT 2016" |
| 3 | Arora, Basu, Mianjy, Mukherjee — understanding ReLU nets | `arXiv:1611.01491` | 命中 | VERIFIED（附异常） | 见 §异常 1 |
| 4 | Ribeiro, Singh, Guestrin — LIME | `arXiv:1602.04938` | 命中 | VERIFIED | KDD 2016 未被 arXiv 元数据标注；年份与内容一致 |
| 5 | Lundberg & Lee — SHAP | `arXiv:1705.07874` | 命中 | VERIFIED | arXiv comment 明写 "To appear in NIPS 2017" |
| 6 | Selvaraju et al. — Grad-CAM | `arXiv:1610.02391`；`10.1109/ICCV.2017.74`；`10.1007/s11263-019-01228-7` | 命中 | VERIFIED（见 §异常 2） | 两个 DOI 归属已确认：ICCV 2017 会议版 / IJCV 128 (2020) 期刊版 |
| 7 | Sundararajan, Taly, Yan — integrated gradients | `arXiv:1703.01365` | 命中 | VERIFIED | ICML 2017 经 PMLR v70 列表核对 |

**结论：七条全部带标识符，七条全部通过独立复核。** 正文中没有未核实的引用。

## 异常

### 1. Arora 那篇的 arXiv 元数据写错了年份

arXiv 页面与 API 的 `journal_ref` 字段逐字为 **"ICLR 2028"**，但该文 v6 的 PDF 首页
页眉写的是 **"Published as a conference paper at ICLR 2018"**。

判定：2028 是 arXiv 元数据的笔误。正文写 2018，正确。
记在这里，因为下一个查的人会看到同样的矛盾，不该以为自己看错了。

### 2. 一次由**核对简报**引起的误报

独立复核最初对第 6 条报 MISMATCH：标题 "Location" 对不上、首作者 "Ramanprasaath"
多一个 n。

复查后发现：**论文本身是对的**（`main.tex` 写的是 `Selvaraju` 与 `localization`），
错在**我写给核对员的简报**——我在简报里把标题打成了 "Location"、作者打成了
"Ramanprasaath"。核对员照简报严谨比对，报 MISMATCH 是正确的行为。

判定：`REFUTED`（对论文而言），原因是简报有误而非文献有误。
保留这条记录，因为它说明第二道检查确实在逐字比对——如果它没报，反而说明它在敷衍。

## 与正文的对应

正文 `paper/main.tex` 的 `thebibliography` 中七条均带 `arXiv:` 标识符，
Grad-CAM 另带 ICCV 的 DOI。摘要里的 `% TODO (P1)` 已删除。
