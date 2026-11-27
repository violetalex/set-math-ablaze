# Abstract (draft, ~190 words)

Attention heads are usually studied by asking what they compute. We ask the
inverse question: **what can be recovered from what they output?**

For a single softmax attention head, the layer output determines the attention
weights if and only if the value vectors are affinely independent. Since `n`
affinely independent points require `n ≤ d + 1`, any context longer than the
model width plus one admits two different attention maps producing an identical
layer output. (Short contexts are not covered: there affinity is possible and
the question becomes whether the trained values happen to be independent.) So attention
weights are not recoverable, even in principle, from a layer's output; a
heat map is one of many explanations of the same numbers.

The argument rests on structural facts we also verify: softmax is a probability
distribution, attention outputs are convex combinations of the values, weights
depend only on score differences, and a strictly positive minimum weight
contracts the token spread by an explicit factor — the mechanism behind rank
collapse.

All results are machine-checked in Lean 4 with Mathlib (23 ledger entries, no
`sorry`, axiom set `⊆ {propext, Classical.choice, Quot.sound}`). The
mathematics is elementary; the contribution is the question, the threshold, and
the record. We are explicit that multi-head projections, RoPE, RMSNorm in the
residual stream and MLPs are not formalized.
