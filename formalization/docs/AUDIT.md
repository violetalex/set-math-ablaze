# 审计记录：`prop:bound` 积分步

> 对象：`Liouville/Bound.lean`（台账 `A34` / `A35`）。
> 判定用语：`CONFIRMED`（能复现的具体错误）、`PLAUSIBLE`（有具体疑点但未坐实）、
> `REFUTED`（审计方自己错了）。只有 `CONFIRMED` 触发修改。

## 1. 实现过程中自查发现

| # | 发现 | 判定 | 处理 |
|---|---|---|---|
| F1 | 骨架 `Scratch/Probe1.lean` 把 $R$ 写成 $1+\rho+\sqrt{-t}$，丢掉 $\zeta$ | **CONFIRMED（范围）** | 改回 `eq:R` 原式 $1+\sqrt{\rho^2+\zeta^2}+\sqrt{-t}$。**方向说明（初版写反了）**：$R$ 变小使上界 $C_1\rho/R$ 变大，即假设**变弱**、命题变强——不是"假设变强"。两个版本都真，但只有原式是逐字对应 |
| F2 | `Phi_bound_tendsto` 的阈值 $T$ 可以是正数，与论文的 $t\le0$ 量词不符 | **CONFIRMED** | 阈值改成 $\min(T,0)$ |
| F3 | 论文写 $\lVert\Phi(t)\rVert_\infty\to0$，本文件给逐点一致版 | **CONFIRMED（范围）** | 记入 SPEC §3；差的是 `sSup` 的 `BddAbove` 簿记，不是分析 |
| F4 | 初版称 `hbound` "比 (H2) 强" | **REFUTED（初版写反了）** | `hbound` 只约束 $\omega^\zeta$，不约束 $\omega^\rho,\omega^\theta$，故**弱于** (H2)。它把论文的一步推导变成了假设，缺的是推导本身（SPEC §5） |

## 2. 独立对抗审计（三路，未参与实现）

方法见 `docs/FIDELITY.md`：三路审计员分别从**保真**、**证明正确性**、**陈述强度**入手，
只拿论文原文、SPEC 和 Lean 源码，任务是证伪。

| # | 发现 | 判定 | 处理 |
|---|---|---|---|
| F5 | **（major）** 论文 (eq:Phi) 把 $\Phi$ 定义为光滑提升 $g(\lvert y\rvert^2,y_5,t)$，$\Phi(0,\zeta,t)=g(0,\zeta,t)$ 一般非零；Lean 的 `Γ/ρ²` 在 $\rho=0$ 走 $x/0=0$，断言退化为平凡真。即 A34 在轴上比 `prop:bound` 严格更弱 | **CONFIRMED** | 新增 `PhiExt`：$\rho>0$ 取 $\Gamma/\rho^2$，$\rho=0$ 取连续延拓值 $\Phi_0$；新增假设 (axis-L) 即 $\Gamma/\rho^2\to\Phi_0$。台账 A34/A35 改指 `PhiExt_bound` / `PhiExt_bound_tendsto`，量词恢复为 $\rho\ge0$ |
| F6 | **（minor）** SPEC §4.1 用 $\Gamma=\rho^2/(2(1+\sqrt{-t}))$ 作"常数锐"的见证，但它**不满足** `hbound`：$\partial_\rho\Gamma=\rho/(1+\sqrt{-t})\ge\rho/R$，方向相反 | **CONFIRMED** | 换成正确的极值族 $\Gamma=\int_0^\rho r\,dr/R$（$\partial_\rho\Gamma=\rho/R$ 取等）。$1/2$ 是上确界且锐，但永不取等号。SPEC §4.1 已改 |
| F7 | `docs/CLAIMS.md` 与 `docs/AUDIT.md` 引用了不存在的 `docs/FIDELITY.md` | **CONFIRMED** | 该文件已由审计流程生成 |
| F8 | `abs_Phi_le` 里的 `hΓ0` 在该引理内冗余（$\rho=0$ 分支由 `x/0=0` 自动成立） | **CONFIRMED（无害）** | 未改。`hΓ0` 在 `abs_Gamma_le` 里不可省（去掉后目标卡在 $\lvert\Gamma\rvert=\lvert\Gamma-\Gamma(0)\rvert$）；整条链依赖它 |

审计员另外**驳回**的怀疑（`REFUTED`，不构成缺陷）：$R$ 是偷换变量；量词 $\forall\exists$ 被换序；
常数被改或 $\le$ 被换成 $<$；额外假设把命题证弱；A34 空洞（有非零实例）；A35 与 sup 版之间有实质分析缺口。

## 3. 修改后的复验

F5/F6 修改完成后重跑：

```
✔ build    ✔ sorry    ✔ axioms    ✔ ledger    ✔ docs      OK
A34 -> Liouville.PhiExt_bound，A35 -> Liouville.PhiExt_bound_tendsto
# print axioms 均为 [propext, Classical.choice, Quot.sound]
```

## 4. 未决事项

- 由 (H1)–(H3) 推出 (H2′) 的那一步（ℝ³ 旋度、柱坐标链式法则）**没有任何机器验证**。
  论文本身在这里只有一行引用（`eq:identities`），但它决定 A34 能否合成为 A9。
- A35 的 `sSup` 形式（$\lVert\Phi(t)\rVert_\infty\to0$）未做，属已声明的范围限制。
