# Scratch

Exploratory files. **Not** part of the library, not covered by `lake build`, and
not scanned by the `sorry` gate (which only reads `Liouville/**`).

They are kept because they are the evidence behind `docs/P5-RANKING.md` (which
records real `lake env lean` exit codes, not estimates) and behind the audit in
`docs/AUDIT.md`.

| File | What it probes |
|---|---|
| `Probe1.lean` | `prop:bound` — the meridional profile estimate (the file the real proof grew out of) |
| `Probe2.lean` | `cor:tradeoff` identities and two refutations |
| `Probe3.lean` | `prop:timedep` and related one-variable reductions |
| `Audit-strength.lean` | statement-strength probe: is the Lean statement stronger or weaker than the paper's? |
| `Audit-lean.lean`, `Check.lean` | ad-hoc `#check` runs against Mathlib |
| `Map-*.lean` | map of which Mathlib lemmas each paper result would need |

Some statements in here are false on purpose; they are refutation probes, not
claims. Nothing in this directory should be cited.
