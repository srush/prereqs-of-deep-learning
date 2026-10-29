# Penrose diagrams

The blog uses the checked-in `rudin-*.svg` images. Their `.domain`, `.substance`,
and `.style` sources are included. Ordinary figures share `common.style`;
the tech tree uses its own canvas.

To regenerate a diagram, install the pinned dependencies with `pnpm install --frozen-lockfile`,
then run `pnpm render rudin-tech-tree` (or another diagram name).
Set `CHROME_PATH` to a Chrome executable if it is not installed at the default macOS path.

The tech tree shows the main conceptual prerequisites in the note, not the full
Lean declaration dependency graph. The exp(x) branch continues to its derivative and verified MLP gradients.
The compact tree uses labels only in a 920-by-590 viewport.
