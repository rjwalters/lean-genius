# Erdős #85 paper: where it lives

The released paper, its Lean closure and its certificate receipts are **not on `main`**.
They live on release tags, because the Lean closure is about 4,100 extra modules and
the research tree is about 4.5 GB, and `main`'s lakefile builds every `Proofs.*` module.

| Version | Git tag | Branch | Zenodo |
|---------|---------|--------|--------|
| v1 (12 October 2026) | [`erdos85-paper-v1`](https://github.com/rjwalters/lean-genius/releases/tag/erdos85-paper-v1) | archived as the tag | [10.5281/zenodo.23325806](https://doi.org/10.5281/zenodo.23325806) |
| v1.1 (revision answering review jhpvtq) | [`erdos85-paper-v1.1`](https://github.com/rjwalters/lean-genius/releases/tag/erdos85-paper-v1.1) | `erdos85/review-jhpvtq-v2` | [10.5281/zenodo.23519149](https://doi.org/10.5281/zenodo.23519149) |

The Zenodo concept DOI [10.5281/zenodo.23325805](https://doi.org/10.5281/zenodo.23325805)
always resolves to the latest version.

To read or rebuild a version, check out its tag:

```bash
git fetch origin tag erdos85-paper-v1.1
git worktree add ../erdos85-v1.1 erdos85-paper-v1.1
```

The paper source is `research/problems/erdos-85-wip-01/manuscript/paper/main.tex` at the tag,
and `research/problems/erdos-85-wip-01/manuscript/publication/ZENODO.md` lists what the
Zenodo deposit contains. Do not build the closure with a plain `lake build` (see the repository CLAUDE.md).
