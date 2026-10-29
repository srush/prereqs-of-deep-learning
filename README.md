# Deep Learning Speedrun

[Read the blog](https://srush.github.io/prequisites-of-deep-learning/).

A Lean-checked path from real numbers, topology, and limits to series,
scalar derivatives, the exponential, backpropagation, and MLP gradients.
The presentation follows Baby Rudin, with source references in code comments.

The proofs use Lean's standard library, without Mathlib. The real-number
interface assumes a complete ordered field; it does not construct the reals.
Definitions and theorem statements are visible, with expandable proofs.

## Build and preview

Install [Lean via elan](https://lean-lang.org/install/), then run:

```sh
make check
make docs
make serve
```

Open <http://127.0.0.1:8000/>. The pinned Lean version is in `lean-toolchain`;
Verso and its dependencies are pinned in `lake-manifest.json`.

## Files

- `Speedrun.lean`: the blog and checked proofs.
- `Speedrun/Foundations.lean`: the real-number interface and supporting lemmas.
- `site/diagrams/`: Penrose sources and rendered SVG illustrations.
- `tools/compact_verso.py`: loads proof states on demand to keep the page responsive.

## Publishing

Pushing to `main` checks the Lean code, renders the article, and deploys it
with GitHub Actions to GitHub Pages. The workflow can also run manually.
