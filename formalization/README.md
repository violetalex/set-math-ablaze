# liouville-lean

A Lean 4 + Mathlib formalization of one step in a conditional Liouville theorem
for ancient axisymmetric Navier–Stokes flow with swirl.

**This repository verifies one lemma, not a theorem about the Navier–Stokes
equations.** Read [Scope and honesty](#scope-and-honesty) before citing anything
here.

## What is verified

The companion paper proves, among other things, the bound
`|Φ(t,ρ,ζ)| ≤ C₁/(2(1+√(-t)))` for the lifted swirl `Φ = Γ/ρ²`, where
`R = 1 + |x| + √(-t)`. Its proof ends with a one-dimensional integration in `ρ`.
That integration step is what is formalized here.

| Ledger | Declaration | Status |
|---|---|---|
| A34 | `Liouville.PhiExt_bound` | **PROVED** (Lean 4 + Mathlib) |
| A35 | `Liouville.PhiExt_bound_tendsto` | **PROVED** (Lean 4 + Mathlib) |
| A9 (`prop:bound`, the full statement) | — | `PROVED-INFORMAL` |

Both declarations satisfy

```
#print axioms Liouville.PhiExt_bound
-- 'Liouville.PhiExt_bound' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

and the library contains no `sorry` or `admit`.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain`; Mathlib is fetched by Lake at the revision in
`lake-manifest.json`.

```bash
git clone https://github.com/<your-account>/set-math-ablaze.git
cd set-math-ablaze/formalization
lake exe cache get   # optional: prebuilt Mathlib oleans, much faster
lake build
```

## Verification

`scripts/check.sh` is the single acceptance criterion. It runs six gates:

| Gate | Checks |
|---|---|
| `build` | `lake build` succeeds |
| `sorry` | no `sorry`/`admit` in `Liouville/**` |
| `axioms` | every declaration in `Audit.lean` has axioms ⊆ `{propext, Classical.choice, Quot.sound}` |
| `statement` | each declaration is definitionally equal in type to its independently written challenge in `Statements.lean` |
| `ledger` | every row of `docs/CLAIMS.md` resolves to a declaration that exists |
| `docs` | the required design documents are present |

The `statement` gate is the one that does not read the proof. `Statements.lean`
restates each `PROVED` proposition, written against the paper rather than against
the formalization; the gate asks Lean whether the two types are definitionally
equal. It catches a theorem that proves something adjacent to what was claimed —
which no compiler error would reveal.

```bash
bash scripts/check.sh
```

## Layout

```
Liouville.lean          library entry point
Liouville/Bound.lean    the two verified theorems and their lemmas
Audit.lean              #print axioms, one line per public declaration
docs/SPEC.md            what is claimed: objects, hypotheses, quantifiers, falsifiability tests
docs/FIDELITY.md        independent audit: is the Lean statement the paper's statement?
docs/AUDIT.md           audit log, including errors found in the first draft
docs/P5-RANKING.md      cost ranking of all results in papers A and B
docs/FRONTIER.md        audit surface: what the proofs borrow from outside (generated)
docs/CLAIMS.md          symlink to the canonical ledger at the repository root
docs/RUNS/              run record: workflow ids, agent counts, gate status
Scratch/                exploratory files, not built and not part of the library
tools/                  vendored `mathlean` checker
```

## Kernel replay

`bash scripts/check.sh` trusts the elaborator. A second path does not:

```bash
python3 tools/run_mathlean.py replay
```

This reads the compiled `.olean` files and replays them through `leanchecker`,
without going through elaboration. It is the only check that catches a proof
whose terms were assumed rather than elaborated (`addDecl`, `kexactB`). It uses
Lean's own kernel, so it does not protect against a kernel bug; `--checker`
accepts a different implementation.

**Documentation language.** The design and audit documents under `docs/` are
written in Chinese; this README and all Lean sources are in English. The Lean
sources are the authority on what is proved — `docs/` explains why each
hypothesis is there and what the independent audit found.

## Scope and honesty

Three things a reader should know.

1. **Only the final integration step is formalized.** Passing from
   hypotheses (H1)–(H3) to `|∂_ρΓ| ≤ C₁ρ/R` requires a curl computation in
   cylindrical coordinates (`ω^ζ = Γ_ρ/ρ`, `|ω^ζ| ≤ |ω|`) over `u : ℝ³ → ℝ³`,
   which this project takes as a hypothesis and does not derive. `A9` therefore
   remains `PROVED-INFORMAL`; `A34`/`A35` cover its last step and its corollary.

2. **The axis value is handled explicitly.** In Lean, `x / 0 = 0`, so writing
   `Φ = Γ/ρ²` and evaluating at `ρ = 0` silently makes the axis statement
   vacuous — whereas in the paper `Φ` is a smooth lift with `Φ(0) ≠ 0` in
   general. The formalization defines `PhiExt`, which takes the limit value
   `Φ₀(ζ,t)` at `ρ = 0`, and carries the existence of that limit as an explicit
   hypothesis. See `docs/SPEC.md` §1.

3. **No unconditional statement is claimed anywhere.** The paper's main theorem
   is conditional, and the largest gap between this repository and that theorem
   is structural: Mathlib has no Feynman–Kac formula and no parabolic maximum
   principle. `docs/P5-RANKING.md` records this.

## Where this sits

This directory is the formalization half of the repository. The papers it
refers to are in [`../papers/`](../papers/), and the canonical ledger is
[`../CLAIMS.md`](../CLAIMS.md); `docs/CLAIMS.md` here is a symlink to it, so the
six gates and the papers cannot disagree about what is claimed.

## License

Code is licensed under the Apache License 2.0 — see [`../LICENSE`](../LICENSE)
and [`../NOTICE`](../NOTICE). The papers are CC BY 4.0, see
[`../LICENSE-papers`](../LICENSE-papers).
