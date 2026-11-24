# 论文 A 命题台账

> 对象：`paperA/mainA.tex`，*A conditional Liouville theorem for ancient axisymmetric
> Navier–Stokes flow with swirl at the critical endpoint*（Fan Li）。
> 规则：论文里每一句「我们证明了……」都必须能追到本表的一行。
> 检查：`mathlean ledger --file CLAIMS.md --tex paperA/mainA.tex`
>
> 本表绝大部分不涉及 Lean。机器验证的是 A34 与 A35（A9 的积分步与其推论，见下），其余 `PROVED` 留待形式化后使用。
>
> 前提：凡涉及 $u$ 的行都设在 `hyp:main` 的 (H1)–(H4)（$\gamma=0$）与 `eq:axis`
> 的轴正则之下；A13–A16 是抽象线性类或一般 $\mathbb R^5$ 上的陈述，不受此限。

## 状态取值

| 状态 | 含义 |
| --- | --- | --- |
| `PROVED-INFORMAL` | 本文给出了完整的人类证明 |
| `CONDITIONAL` | 证明完整，但结论依赖某个**未被证明成立**的假设（备注写明） |
| `OPEN` | 既无证明也无反例 |
| `REFUTED` | 有反例 |
| `CITED` | 引自他人，本文未证 |
| `PROVED` | Lean 4 + Mathlib 机器验证（目前只有 A34、A35，见 `~/liouville-lean`） |

## 台账

| ID | 状态 | 命题 | Lean 声明 | 依赖 | 理解 | 备注 |
| --- | --- | --- | --- | --- | --- | --- |
| A1 | CITED | 无旋古代有界弱解 $u=(u^\rho,0,u^\zeta)$ 必为 $(0,0,b(t))$，且 $b$ 为常数 | — | — | — | 引用：KNSS Theorem 5.2 与 Remark 6.1（`thm:KNSS`） |
| A2 | CONDITIONAL | 若 $b^\rho\ge0$，则 $\Gamma\equiv0$，从而 $u=(0,0,c)$ | — | A8, A9 | — | 假设：$b^\rho\ge0$（`eq:Hsign`）；本文 §1.3 明言不由 (H1)–(H4) 推出。含 `thm:main` 与 `thm:main2` |
| A3 | CONDITIONAL | 权重型极值原理：$w=\Gamma/h$ 在内部临界点满足 $\partial_tw=\nu\Delta_\mu w+\frac wh(\nu\Delta_\mu h-b\cdot\nabla h)$；若该系数 $\le0$，$\lvert w\rvert$ 在内部极值处不增；若再设 $\sup\lvert w\rvert$ 在几乎所有 $t$ 被达到且反向衰减，则 $\Gamma\equiv0$ | — | — | — | 假设：$\sup\lvert w\rvert$ 有限且在几乎所有 $t$ 被达到（`rem:attain`）。本文实际只用到 $h=\rho^2$ 与 $h=\rho^2e^f$ 两支，二者在 A2/A4 中不依赖该假设。含 `thm:weights`、`thm:weights2` |
| A4 | CONDITIONAL | 若存在 $f\in C^2(\mathbb R^5)$ 满足 $f\ge-C$、$\lvert\nabla_5f\rvert\le C$ 与 $(\star)$，则 $\Gamma\equiv0$ | — | A8 | — | 假设：存在这样的 $f$（即 $(\star)$）；必要性未声称。含 `thm:star`、`thm:star2` |
| A5 | CONDITIONAL | 若 $(\star)$ 成立且存在静止伴随方程的正解 $m>0$，则 $\nu\int\lvert\nabla_5f\rvert^2m\le\int V_0m$；$V_0$ 的 $m$-均值严格为负时 $(\star)$ 不可能 | — | A4, A28 | — | 假设：分部积分的边界项可合法丢弃（紧支撑/周期/Neumann）`prop:NC` |
| A6 | PROVED-INFORMAL | 抽象线性类（$b=(0,0,\beta)$ 常数、$V_0<0$ 常数视为独立数据）存在有界非平凡古代解；该模式与 (H1)–(H3) 不相容 | — | — | — | `prop:mode`，本文 §1.3 明言是"模式"而非 NS 反例 |
| A7 | PROVED-INFORMAL | 在 (H1)–(H3) 与轴正则下 $W:=-2\psi/\rho^2$ 满足 $\lvert W\rvert\le C_0$ 且 $V_0=2b^\rho/\rho=\partial_\zeta W$，故 $V_0$ 在 $\zeta$ 方向零 Cesàro 均值 | — | — | — | `prop:W` |
| A8 | PROVED-INFORMAL | 提升恒等式 $\Delta_\mu(\rho^2A)=\rho^2\Delta_5A$；$\Phi=\Gamma/\rho^2$ 满足 $\partial_t\Phi+\operatorname{Div}_5(b\Phi)=\nu\Delta_5\Phi$ | — | — | — | `prop:lift` |
| A9 | PROVED-INFORMAL | 反向一致界 $\lvert\Phi(t)\rvert\le C_1/(2(1+\sqrt{-t}))$ | — | — | — | `prop:bound` |
| A34 | PROVED | `prop:bound` 的**积分步**：设 $\Gamma(0,\zeta,t)=0$ 且 $\Gamma(\rho,\zeta,t)/\rho^2\to\Phi_0(\zeta,t)$（$\rho\to0^+$，即轴正则），$\lvert\partial_\rho\Gamma\rvert\le C_1\rho/R$；则 $\lvert\Phi(\rho,\zeta,t)\rvert\le C_1/(2(1+\sqrt{-t}))$ 对一切 $\rho\ge0,\zeta,t\le0$，其中 $\Phi=\Gamma/\rho^2$（$\rho>0$）、$\Phi=\Phi_0$（$\rho=0$） | `Liouville.PhiExt_bound` | — | yes | **Lean 4 + Mathlib 机器验证**（`~/liouville-lean`，公理 $\subseteq$ {propext, Classical.choice, Quot.sound}，无 sorry）。仅覆盖 A9 的最后一步：由 (H1)–(H3) 推出 $\lvert\partial_\rho\Gamma\rvert\le C_1\rho/R$ 需要 ℝ³ 旋度与柱坐标链式法则，**未**形式化，故 A9 本身仍是 `PROVED-INFORMAL`。详见 `~/liouville-lean/docs/FIDELITY.md` |
| A35 | PROVED | 由 A34：$\forall\varepsilon>0\ \exists T\ \forall t\le T\ \forall\rho\ge0\ \forall\zeta$, $\lvert\Phi\rvert\le\varepsilon$（反向衰减的逐点一致形式） | `Liouville.PhiExt_bound_tendsto` | A34 | yes | 论文 A9 写的是 $\lVert\Phi(t)\rVert_\infty\to0$；这里少一层 $\sup$ 的 `sSup` 簿记（需 `BddAbove` 与夹逼），缺的是簿记不是分析，故 A9 的这一半也保持 `PROVED-INFORMAL` |
| A10 | PROVED-INFORMAL | 对 $h=\rho^a$：阈值 $b^\rho\ge\nu(a-2)/\rho$；反向一致衰减 $\Rightarrow a\ge2$；阈值弱于 $b^\rho\ge0$ $\Rightarrow a\le2$。故 $a=2$ 是唯一相容的径向幂权 | — | A3 | — | `cor:tradeoff`。注意这是**权重方法的代数事实**，不是"任何方法都不能弱化" |
| A11 | PROVED-INFORMAL | 时间依赖的加性权 $h=\rho^2e^{f(t,x)}$ 在临界点给出 $\partial_tw=\nu\Delta_\mu w+Gw$，$G$ 含额外的 $-\partial_tf$，不给新信息 | — | A3 | — | `prop:timedep` |
| A12 | CONDITIONAL | 若存在 $n>0$ 满足 $\nu\Delta_5n=\operatorname{Div}_5(bn)$ 且 $n\ge c>0$、$\lvert\nabla_5\log n\rvert\le C$，则 $\Gamma\equiv0$ | — | A4 | — | 假设：存在这样的对偶密度 $n$；逆命题未声称 `prop:dual` |
| A13 | PROVED-INFORMAL | 球平均必要条件 $\int_{B_R}(V_0+\lvert b\rvert^2/4\nu)\ge-\nu C\lvert\partial B_R\rvert$ | — | A4 | — | `prop:ballavg`，不需要静止密度，在 $\mathbb R^5$ 上可用 |
| A14 | PROVED-INFORMAL | 若 $b$、$V_0$ 为常数且 $V_0<-\lvert b\rvert^2/(4\nu)$，则 $(\star)$ 不成立 | — | A13 | — | `cor:const` |
| A15 | PROVED-INFORMAL | 径向对偶密度只能是 $n=B+C\rho^{-2}$ 且 $Bb^\rho\equiv0$；可容许的 $n$ 必为常数，仅当 $V_0\equiv0$ 存在 | — | A12 | — | `prop:radial` |
| A16 | PROVED-INFORMAL | 一维 $b=-b_0\tanh x$、$V_0=b'$ 时不存在满足 $(\star)$ 的 $f$ | — | — | — | `prop:1d`（一维类中的否定结果） |
| A17 | PROVED-INFORMAL | 轴对称类中无一维约化：$b$ 只依赖 $\rho$ 或只依赖 $\zeta$ 都迫使 $b^\rho=0$、$V_0=0$ | — | — | — | `lem:no1d` |
| A18 | PROVED-INFORMAL | 存在满足 (H1)–(H4) 且 $(\star)$ 可解的显式运动学场（含 $V_0$ 变号的例子） | — | — | — | `prop:examples` |
| A19 | PROVED-INFORMAL | 有界加权无散场的对称 $\zeta$-均值估计 $\lvert\frac1{2Z}\int_{-Z}^{Z}V^\rho\rvert\le\frac{\lVert V\rVert_\infty\rho}{2Z}$ | — | — | — | `lem:zeromean` |
| A20 | PROVED-INFORMAL | 平台定位：$L=\lim_{t\to-\infty}\lVert\Gamma(t)\rVert_\infty>0$ 时存在 $t_n\to-\infty$ 与 $\rho_n\gtrsim(L/C_1)^{1/2}(-t_n)^{1/4}$ 使 $\lvert\Gamma\rvert\ge L/2$ | — | A9 | — | `prop:plateau` |
| A21 | PROVED-INFORMAL | 逐点论证无法判定平台：显式运动学场 $\Gamma=L(1-e^{-(\rho/r_*)^2})e^{-(\zeta/r_*)^2}$，$r_*=s^{1/4}$ | — | A20 | — | `prop:witness`（不是 NS 解） |
| A22 | PROVED-INFORMAL | 对每个 $\alpha>1/4$ 存在满足 (H1)–(H4)、$\lvert\Gamma\rvert=L$ 出现在 $\rho\sim(-t)^\alpha$ 上的场 | — | A21 | — | `prop:plateauscales`（不是 NS 解） |
| A23 | PROVED-INFORMAL | 精确平均方程 $\partial_\tau\langle G\rangle+\frac1\rho\partial_\rho(\rho C)=\nu\Delta_\mu\langle G\rangle$，$C=\langle b^\rho G\rangle$，且 $\lvert C\rvert\le\frac{C_0C_1}{2}\frac{\rho^2}{1+\sqrt s}$ | — | A19 | — | `prop:average` |
| A24 | PROVED-INFORMAL | 均匀轴向类刚性：$b=(0,0,c)$ 常数时 $\Gamma\equiv0$（用 (H2) 与有界古代热核 Liouville） | — | A9 | — | `rem:axialrigid` |
| A25 | PROVED-INFORMAL | 两尺度类内，均匀校正子界 $\Leftrightarrow$ 领先轴向输运消失 $c\partial_\zeta G_0=0$；且 $C\equiv0\Rightarrow\langle G\rangle\equiv0$ | — | A20, A21 | — | `rem:corrector`、`rem:whyavg` |
| A26 | OPEN | 压强紧性：从 (H4) 推出 $s^{-1/4}\lVert\nabla_yP\rVert_{L^\infty(K)}\to0$ | — | — | — | 备注：`rem:pressure`，本文未写；故"$c$ 常数"是任何 blow-down 陈述的假设 |
| A27 | OPEN | $\gamma=0$ 端点的一般情形：证明 $L=0$ | — | A2, A4, A12 | — | 备注：`openproblem` 环境；本文不声称解决 |
| A28 | CONDITIONAL | Fisher 恒等式：在 $\mathbb R^5$ 上需额外的通量假设（$bm$ 与 $m\nabla\log m$ 过 $\lvert x\rvert=R$ 的通量为零，且 $\int\lvert\nabla m\rvert^2/m<\infty$），此时 $\int V_0m=\nu\int\lvert\nabla_5m\rvert^2/m\ge0$ | — | — | — | 假设：上述通量与可积性；`rem:fisher`。故 `prop:NC` 是模型判据，不是 NS 类定理 |
| A29 | CONDITIONAL | 涡量规范：$\Delta_5W=2\Omega$、$b\cdot\nabla_5W=-WV_0$，$f=\log\lvert W\rvert$ 满足精确恒等式；若 $W$ 定常、$\lvert W\rvert\ge c$、$\Omega/W\le0$，则 $(\star)$ 成立 | — | A4 | — | 假设：$\Omega/W\le0$ 与 $W$ 定常，均未在 (H1)–(H3) 下证明；`rem:gauge` |
| A30 | CONDITIONAL | $\zeta$-通量：若单侧极限 $c_\pm$ 存在且与 $\rho$ 无关，则 $\int b^\rho\,d\zeta=\rho(c_--c_+)$；$b^\rho\ge0$ 且 $c_+=c_-$ 时 $b^\rho\equiv0$ | — | A7 | — | 假设：one-constant 陈述不随 (H1)–(H4) 成立（本文注明 OPEN）；`rem:flux` |
| A31 | CONDITIONAL | 剩余条件即基态非衰减：$L^*=\nu\Delta_5+b\cdot\nabla_5$ 满足 $L^*1=0$，其 Dirichlet 主特征值 $\le0$；若存在满足 $n\ge c$、$\lvert\nabla\log n\rvert\le C$ 的正解则 $(\star)$ 成立 | — | A12 | — | 假设：存在有下界且梯度受控的正解；"超解 $\to$ 有下界解"这一步 Pinsky–Murata–Pinchover 理论不提供；`rem:groundstate` |
| A32 | CITED | 有界可测漂移的鞅问题适定，故 Feynman–Kac 步不需要 $b$ 的 Lipschitz 或正则性 | — | — | — | 引用：Stroock–Varadhan 鞅问题理论；`rem:noreg` |
| A33 | CITED | 漂移在 $L_\infty(BMO^{-1})$ 时无势方程的古代有界解必为常数 | — | — | — | 引用：SSSZ；本文**未**验证极向漂移属于该类（常向量都不在 $BMO^{-1}$），故不可用于 A2 之外的情形；`rem:sssz` |

## 摘要断言对照

逐句核对 `\begin{abstract}` 的断言（§1 引言同理）。

| 摘要原句 | 台账 | 判定 |
| --- | --- | --- | --- |
| Modulo the swirl-free Liouville theorem, the endpoint is equivalent to $\Gamma\equiv0$ | A1 + §1.1 论证 | 一致：引用明确，等价性有证明 |
| We prove that $\Gamma\equiv0$ whenever the radial velocity is non-negative, $b^\rho\ge0$ | A2 | 一致：条件写在同一句里 |
| The proof is an exact maximum principle for $\Phi=\Gamma/\rho^2$ on $\mathbb R^5$ | A8, A9 | 一致 |
| the obstruction is the sign of $V_0=\operatorname{Div}_5b=2b^\rho/\rho$ | A7 | 一致 |
| the hypothesis is sharp inside the class of radial weights: among $\rho^a$ only $a=2$ retains the backward uniform decay | A10（+A3） | 一致，且**范围限定正确**（说的是径向幂权与"该论证所需"） |
| We reduce the remaining case to a scale-free sufficient condition $(\star)$ | A4 | 一致：用 "reduce ... to"，未声称必要性 |
| prove an averaged necessary condition | A13 | 一致：该条确实无条件成立 |
| and a dual sufficient condition for it | A12 | 一致：sufficient 明确 |
| an explicit counterexample showing that the linear five-dimensional theory alone cannot decide the sign | A6 | 一致：反例在**抽象线性类**内，未冒充 NS 反例 |
| The two-dimensional bounded-class lemma ... is treated in a companion paper | 指向论文 B | 一致：归属正确 |
| No unconditional $\gamma=0$ theorem is claimed | A27 | 一致 |

**结论：摘要与引言未发现超出台账的断言。**

三处需要注意但**不构成错误**的措辞：

1. A3（`thm:weights`）的到达性假设在定理陈述里是条件句，摘要的 "sharp" 只用到 A10 的代数计算，
   不依赖它——`rem:attain` 已说明。风险在于只看定理陈述的读者可能误以为无条件。
2. A10 证明的是"径向幂权中只有 $a=2$ 与反向衰减相容"，不是"任何论证都不能弱化 $b^\rho\ge0$"。
   摘要与引言都用了 "inside/within the radial-power family"，范围正确。
3. A28 与 A5 的分工：A5（"$V_0$ 的 $m$-均值严格为负时 $(\star)$ 不可能"）在 NS 类中**永远不会触发**，
   因为 A28 说明该均值非负。正文已两处点明——`prop:NC` 陈述末尾括注
   "For the drift of the Navier–Stokes class ... that alternative is never taken"，
   以及 `rem:fisher` 整段。§1.3 的 "They do not by themselves prove that $(\star)$ fails in the
   Navier–Stokes class" 也已限定范围。**无需修改**；记在这里是为了防止以后引用 A5 时断章取义。

## 变更记录

- 2026-11-14：新增 A34、A35（`PROVED`，机器验证）。它们是 A9（`prop:bound`）的积分步与推论；
  A9 本身状态不变。形式化工程：`~/liouville-lean`，验收 `scripts/check.sh` 五道门全绿。

- 2026-11-13：建表，覆盖 `mainA.tex` 全部 theorem/proposition/lemma/corollary 与实质性 remark
  （共 31 条，其中 CONDITIONAL 9 条、OPEN 2 条、CITED 1 条、PROVED-INFORMAL 19 条）。
- 2026-11-13：摘要与引言逐句核对，未发现超出台账的断言；提出 1 条措辞建议（见上第 3 点）。
- 2026-11-13：加 `--tex` 覆盖检查，补齐 3 个漏项：`hyp:main`（写进前言前提）、
  `rem:noreg`→A32、`rem:sssz`→A33（两条都是引用他人的工具性事实，标 CITED）。
  现存 12 个无 `\label` 的 remark/openproblem 已复核，全部是已入表结论的复述或说明：
  L425 最大原理形式（A8/A9）、L436 符号用在哪一步（A2）、L460 抽象类尖锐性（A6）、
  L572 $h$-变换形式（A4）、L600 $(\star)$ 的精确含义（A4）、L676 对偶方程之别（A12）、
  L945 一维恒等式（A16）、L1001 运动学场的性质（A18）、L1090 Cesàro 对照（A19）、
  L1174 下界尖锐（A20）、L1288 平均方程为何不闭合（A23）、L1353 openproblem（A27）。
