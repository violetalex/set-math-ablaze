# Papers

Three papers, all written under the procedure in [`../workflow/`](../workflow/).

| Directory | Title | Status |
|---|---|---|
| [`a-liouville-ns/`](a-liouville-ns/) | A conditional Liouville theorem for ancient axisymmetric Navier–Stokes flow with swirl at the critical endpoint | under review, *SeMA Journal* |
| [`b-2d-lemma/`](b-2d-lemma/) | A bounded-class Liouville lemma for a two-dimensional steady advection–diffusion equation, and the classes where it holds | under review, *SeMA Journal* |
| [`c-workflow/`](c-workflow/) | A verification-first workflow for research mathematics | draft |

Every theorem, proposition, lemma and substantive remark in A and B has a row
in [`../CLAIMS.md`](../CLAIMS.md). Two rows are machine-checked in
[`../formalization/`](../formalization/); the rest are marked with the kind of
evidence that exists for them.

## Building

Papers A and B have committed PDFs. Paper C does not — build it from source.

```bash
# paper C
cd c-workflow && tectonic -X compile main.tex    # or pdflatex, twice

# papers A and B
cd a-liouville-ns && tectonic -X compile mainA.tex
cd ../b-2d-lemma  && tectonic -X compile mainB.tex
```

Standard `article` class; nothing outside a full TeX Live installation is
required.

## A note on the numbers in paper C

Paper C reports counts taken from this repository: 31 formal statements
extracted from A and B (28 after deduplication), 35 ledger rows, 123 unit tests,
12 self-test scenarios. If you re-run the tooling and get different numbers,
the tooling is right and paper C is stale.
