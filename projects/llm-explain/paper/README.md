# Paper

`main.tex` — the write-up of the 25 proved ledger entries in `docs/CLAIMS.md`.
`abstract.md` is the earlier one-page draft, kept because drafting it caught a
factual error in the regime the results cover.

Build: `tectonic -X compile main.tex` (or `pdflatex` twice).

## What the paper is

An inverse-problem paper: given a layer's output, is its attention recovered?
The answer is a threshold (affine independence of the values) and a dimension
bound on the ambiguity when the threshold fails.

## What it is not

Not a paper about a trained model, not about multi-head/RoPE/MLP, and not
claiming new mathematics — see §1.4 and §8 of the paper, and
`../docs/CITATIONS.md` for what the literature already has.

## Before submission

- Luce (1959) and McFadden (1974) are deliberately uncited: their identifiers
  have not passed P1. Cite them only after checking.
- The "to our knowledge" phrasing for the identifiability result must survive
  copy-editing; the search that supports it is recorded in `../docs/CITATIONS.md`.
