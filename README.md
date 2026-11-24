# set-math-ablaze

One research workflow, and everything it produced.

This repository contains a tool, the staging procedure it enforces, three
papers written under that procedure, and the Lean 4 formalization that came out
of it. The point of putting them in one place is that the papers are not
independent of the workflow: every theorem in them resolves to a row of a
ledger, and every machine-checked row resolves to a declaration in
`formalization/`.

## What is here

| Path | What it is |
|---|---|
| [`workflow/`](workflow/) | `mathlean` — a dependency-free Python checker (111 unit tests, 13 self-test scenarios) plus `workflow.js`, the P0–P9 orchestration |
| [`formalization/`](formalization/) | Lean 4 + Mathlib project: the machine-checked part of paper A |
| [`papers/a-liouville-ns/`](papers/a-liouville-ns/) | Paper A: a conditional Liouville theorem for ancient axisymmetric Navier–Stokes flow with swirl |
| [`papers/b-2d-lemma/`](papers/b-2d-lemma/) | Paper B: the two-dimensional bounded-class Liouville lemma that closes paper A's last step |
| [`papers/c-workflow/`](papers/c-workflow/) | A methods paper describing the workflow itself, with papers A and B as the case study |
| [`CLAIMS.md`](CLAIMS.md) | The ledger: one row per claim, with its state and its evidence |

## The idea

Every sentence of the form "we prove …" must resolve to a ledger row, and every
row carries one of six states:

| State | Evidence |
|---|---|
| `PROVED` | a proof assistant accepted a declaration, with a checked axiom set |
| `PROVED-INFORMAL` | a complete human proof exists in the paper |
| `CONDITIONAL` | a complete proof of an implication; the hypothesis is unproved |
| `OPEN` | neither a proof nor a counterexample |
| `REFUTED` | a counterexample, recorded |
| `CITED` | attributed to another work, not proved here |

Of the thirty-five rows in this project: two are `PROVED`, nineteen
`PROVED-INFORMAL`, nine `CONDITIONAL`, two `OPEN`, three `CITED`.

The workflow splits work in two:

- **Deterministic** — scaffolding, compilation, `sorry` scanning, axiom audit,
  ledger consistency. Implemented as code with tests, and the gates are
  themselves tested by deliberately breaking each one.
- **Judgement** — proving, counterexample search, fidelity of a formal
  statement to the paper. Handed to independent reviewers with assigned lenses,
  and only findings that can be exhibited are allowed to change the text.

## Reproduce

```bash
# 1. the checker's own tests (no Lean needed)
cd workflow
python3 -I run_tests.py        # 111 tests
./bin/mathlean selfcheck       # 12 scenarios, each gate made to fail on purpose

# 2. the formalization (needs elan; Mathlib is fetched by Lake, ~10 min)
cd ../formalization
lake exe cache get
bash scripts/check.sh
python3 tools/run_mathlean.py replay   # kernel replay of the compiled artifacts
```

`scripts/check.sh` is the single acceptance criterion; it runs six gates:

```
✔ build      lake build 通过
✔ sorry      无 sorry/admit/native_decide
✔ axioms     公理 ⊆ {propext, Classical.choice, Quot.sound}
✔ statement  2 条陈述与声明类型等价
✔ ledger     35 条台账，0 个错误
✔ docs       阶段产物齐全
```

The design documents under `formalization/docs/` are written in Chinese; the
Lean sources and this README are in English. `formalization/docs/SPEC.md` and
`docs/FIDELITY.md` are the two to read first — they state what was claimed and
what the independent audit found.

## What is not claimed

- **Two of thirty-five.** The main theorem of paper A is not machine-checked.
  `A34` and `A35` cover the final integration step and its corollary; the step
  from (H1)–(H3) to a pointwise bound on `∂_ρΓ` needs a curl computation in
  cylindrical coordinates that is not formalized. `A9`, the full statement,
  remains `PROVED-INFORMAL`.
- **No unconditional result at the critical endpoint.** Paper A is conditional;
  `A27` is the open problem, and it is labelled `OPEN` in the ledger and in the
  paper.
- **The workflow does not verify informal mathematics.** It makes the strength
  of each claim visible and checkable. The fidelity of a formal statement to the
  paper is judged by people, recorded in `formalization/docs/FIDELITY.md`, and
  is fallible.

## License

Code and formalization: Apache-2.0 — see [`LICENSE`](LICENSE) and
[`NOTICE`](NOTICE). The vendored checker's own terms are in
[`workflow/LICENSE`](workflow/LICENSE).

Papers: CC BY 4.0 — see [`LICENSE-papers`](LICENSE-papers).
