# SPEC：`prop:bound` 的积分步（论文 A）

> 对象：`paperA/mainA.tex`，`\label{prop:bound}`（第 354 行）。
> 本工程只锁定这一条，不锁定整篇论文。
> 台账行：`A34`（`Liouville.PhiExt_bound`）、`A35`（`Liouville.PhiExt_bound_tendsto`），
> 见 `~/liouville_w12/CLAIMS.md`。

## 1. 对象与定义台账

| 符号 | 定义 | 定义域 | 正则性 | Lean |
|---|---|---|---|---|
| $\Gamma$ | $\rho u^\theta$（swirl） | $\rho\ge0,\ \zeta\in\mathbb R,\ t\le0$ | 只要求 $\rho\mapsto\Gamma(\rho,\zeta,t)$ 在 $[0,\infty)$ 上可微、$\partial_\rho\Gamma$ 在每个 $[0,\rho]$ 上区间可积 | `Γ : ℝ → ℝ → ℝ → ℝ`，下标顺序 $(\rho,\zeta,t)$ |
| $R$ | $1+\lvert x\rvert+\sqrt{-t}$（`eq:R`），轴对称下 $\lvert x\rvert=\sqrt{\rho^2+\zeta^2}$ | $\mathbb R^3\times(-\infty,0]$ | 连续 | `Liouville.R` |
| $\Phi$ | $\Gamma/\rho^2$（`eq:Phi`），**在 $\rho=0$ 取连续延拓值 $\Phi_0(\zeta,t)=g(0,\zeta,t)$** | $\rho\ge0$ | 见 (axis-L) | `Liouville.PhiExt` |
| $\Phi_0$ | $\lim_{\rho\to0^+}\Gamma(\rho,\zeta,t)/\rho^2$ | $\zeta\in\mathbb R,t\le0$ | 存在（由 (axis-L)） | `Φ₀ : ℝ → ℝ → ℝ` |
| $\omega^\zeta$ | $\Gamma_\rho/\rho$（`eq:identities`） | $\rho>0$ | — | `Liouville.omegaZeta` |
| $\Delta_\mu$ | $\partial_\rho^2-\rho^{-1}\partial_\rho+\partial_\zeta^2$（`eq:Dmu`） | — | **本文件不用到** | 未定义 |

**$\Phi$ 在轴上的值必须单独处理。** 论文的定义 (eq:Phi) 是
$\Phi:=\Gamma/\rho^2=g(\lvert y\rvert^2,y_5,t)$，$g$ 光滑——所以 $\Phi(0,\zeta,t)=g(0,\zeta,t)$，
**一般非零**。而 Lean 的实数除法有 $x/0=0$，若直接写 $\Gamma/\rho^2$，则 `Phi Γ 0 ζ t = 0`，
断言在轴上退化成平凡真 $0\le C$。这不是论文的命题。因此这里引入 `PhiExt`：
$\rho>0$ 取 $\Gamma/\rho^2$，$\rho=0$ 取 $\Phi_0$。

**$R$ 的写法同样是刻意的。** $R=1+\sqrt{\rho^2+\zeta^2}+\sqrt{-t}$，即 (eq:R) 原样，不退化成
$1+\rho+\sqrt{-t}$。（注：退化成后者会让 $R$ 变小、假设 $\lvert\partial_\rho\Gamma\rvert\le C_1\rho/R$
**变弱**，即证一个更强的命题；那样仍然蕴含论文的结果，但就不是"逐字对应"了。）

## 2. 假设

| ID | 陈述 | 来源 | 能弱化到什么程度 |
|---|---|---|---|
| (H2′)：`hbound` | $\lvert\partial_\rho\Gamma(\rho,\zeta,t)\rvert\le C_1\rho/R(\rho,\zeta,t)$，对 $\rho\ge0$、所有 $\zeta,t$ | 论文由 `eq:identities`（$\partial_\rho\Gamma=\rho\omega^\zeta$）与 (H2)（$\lvert\omega\rvert\le C_1/R$）得到 | 不能再弱：它是证明唯一的输入。注意它只约束 $\omega^\zeta$，**比 (H2) 弱**，不需要 (H1)、(H3) |
| (axis)：`hΓ0` | $\Gamma(0,\zeta,t)=0$ | `eq:axis`（$\Gamma=\rho^2g(\rho^2,\zeta,t)$） | 弱化为单点取值 |
| (axis-L)：`hΦ₀` | $\Gamma(\rho,\zeta,t)/\rho^2\to\Phi_0(\zeta,t)$（$\rho\to0^+$），对每个 $(\zeta,t)$ | `eq:axis` 里 $g$ 光滑的全部内容 | 这就是本文件用到的轴正则；没有它，$\Phi$ 在轴上没有定义 |
| 可微：`hdiff` | $\rho\mapsto\Gamma(\rho,\zeta,t)$ 在 $[0,\infty)$ 上逐点可微 | $u$ 光滑 | 只用在 $[0,\rho]$ 上 |
| 可积：`hint` | $\partial_\rho\Gamma$ 在每个 $[0,\rho]$ 上区间可积 | $u$ 光滑 | 由连续可得 |
| `hC₁` | $0\le C_1$ | 界常数 | 逻辑上冗余（$C_1<0$ 时假设在 $\rho>0$ 无解，命题空洞真），保留以免讨论退化情形 |

**没有进入假设的东西**：(H1)、(H3)、(H4)、$\gamma=0$、$u$ 满足 Navier–Stokes、
$b$ 的对偶方程。它们对这一步都不起作用——论文自己的证明也没有用到。

## 3. 结论（量词写全）

$$C_1\ge0,\ \Gamma(0,\zeta,t)=0,\ \lim_{\rho\to0^+}\Gamma/\rho^2=\Phi_0(\zeta,t),
\ \lvert\partial_\rho\Gamma\rvert\le C_1\rho/R$$
$$\Longrightarrow\quad \forall\rho\ge0\ \forall\zeta\in\mathbb R\ \forall t\le0:\quad
\lvert\Phi(\rho,\zeta,t)\rvert\le\frac{C_1}{2\,(1+\sqrt{-t})},$$

其中 $\Phi=\Gamma/\rho^2$（$\rho>0$）、$\Phi=\Phi_0$（$\rho=0$）。

推论（`PhiExt_bound_tendsto`）：

$$\forall\varepsilon>0\ \exists T\ \forall t\le T\ \forall\rho\ge0\ \forall\zeta:\quad
\lvert\Phi(\rho,\zeta,t)\rvert\le\varepsilon .$$

注意推论是**逐点一致**形式，不是 $\lVert\Phi(t)\rVert_\infty\to0$：后者还要一层
$\sup_{(0,\infty)\times\mathbb R}$ 的 `sSup` 簿记（需 `BddAbove` 与夹逼，约 15–30 行）。缺的是簿记，不是分析。

## 4. 可伪性

1. **常数锐性**：取 $\Gamma(\rho,\zeta,t)=\int_0^\rho \frac{r\,dr}{1+\sqrt{r^2+\zeta^2}+\sqrt{-t}}$。
   则 $\partial_\rho\Gamma=\rho/R$ 恰好取到 `hbound` 的等号（$C_1=1$），且
   $\Gamma(0)=0$、$\Gamma/\rho^2\to0$。此时
   $\lvert\Phi\rvert\le\int_0^\rho\frac{r\,dr}{1+\sqrt{-t}}\big/\rho^2=\frac{1}{2(1+\sqrt{-t})}$，
   而 $\zeta=0$、$\rho\to0$ 时比值 $\to1$。所以 $1/2$ 是**上确界且锐**，但**永不取等号**
   （$\zeta=0$ 时 $R=1+\rho+\sqrt{-t}>1+\sqrt{-t}$）。
   ~~原先写的见证 $\Gamma=\rho^2/(2(1+\sqrt{-t}))$ 是错的~~：它的 $\partial_\rho\Gamma=\rho/(1+\sqrt{-t})$，
   而 $R\ge 1+\sqrt{-t}$ 使 $\rho/R\le\rho/(1+\sqrt{-t})$，方向正好相反，**不满足** `hbound`。
   这是独立审计发现的问题（见 `docs/FIDELITY.md` C2）。
2. **尺度检验**：$\Gamma\mapsto\lambda\Gamma$、$C_1\mapsto\lambda C_1$ 保持结论（齐次）。
   若把 $\int_0^\rho C_1r\,dr$ 错算成 $\rho$ 的一次方，这一族立刻暴露。
3. **轴上检验**：去掉 (axis-L) 后，`PhiExt` 在 $\rho=0$ 无定义，定理必须失败。
   这一条用来确认轴上不是靠 $x/0=0$ 蒙混过关的。
4. **$R$ 的方向检验**：把 $R$ 换成 $1+\rho+\sqrt{-t}$ 不改变结论（假设变弱）；
   换成 $1-\rho+\sqrt{-t}$ 必须失败（假设变强到不可满足）。

## 5. 范围外（明确不做）

- **从 (H1)–(H3) 推出 (H2′)**：需要 $\omega=\nabla\times u$、柱坐标下的旋度公式
  $\omega^\zeta=\partial_\rho(\rho u^\theta)/\rho$、以及 $\lvert\omega^\zeta\rvert\le\lvert\omega\rvert$。
  这是 ℝ³ 向量微积分框架，本次不做。**因此台账 A34/A35 只覆盖 `prop:bound` 的积分步，
  整条 `prop:bound`（A9）仍是 `PROVED-INFORMAL`。**
- **$\lVert\Phi(t)\rVert_\infty\to0$**：只做到逐点一致版（见 §3）。
- **整篇论文**：其余 33 行台账的 Lean 现状见 `docs/P5-RANKING.md`；
  主结论 `thm:main` 卡在 Mathlib 完全没有的 Feynman–Kac / 抛物极值原理一层。
