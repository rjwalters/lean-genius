# erdos-1006-oq-01-oq-02 — Cover Graph Recognition

**Problem**: Can cover graph recognition (deciding if a graph is the Hasse diagram of some finite poset) be done in polynomial time?

**Context**: Follows from Pretzel-Brightwell (1985), formalized in erdos-1006-oq-01: a graph admits a robustly acyclic orientation iff it is a cover graph.

---

## Session 2026-05-03 (Session 1) — Gallery Entry

**Mode**: FRESH
**Outcome**: progress — gallery entry created

### What I Did

- Claimed `erdos-1006-oq-01-oq-02` (tractability 5, significance 6)
- Created `proofs/Proofs/Erdos1006OQ01OQ02.lean` with:
  - `GraphOrientation.hasShortcut` — orientation has a shortcut arc (u→v with path u→w→v)
  - `GraphOrientation.isHasse` — acyclic and shortcut-free
  - `coverOrientation_no_shortcut` — proved: covering orientations have no shortcuts (via CovBy.2)
  - `cover_graph_is_hasse` — cover graphs admit Hasse-like orientations
  - `cover_implies_related` — cover graph edges witness comparable pairs
  - `cover_graph_in_np` — NP membership via poset certificate
  - `cover_search_space_bound` — search space is 2^(n²)
  - `cover_subclass_comparability` — cover ⊊ comparability
  - Axioms: `cover_graph_recognition_in_p` (open), `comparability_recognition_in_p` (Golumbic 1977)

### Key Findings

- **Shortcut-free = Hasse**: An acyclic orientation is a Hasse diagram iff no arc u→v has an alternative path u→w→v. This is the key structural characterization.
- **Proof technique**: `CovBy.2 huw.lt : ¬w < v` directly gives the shortcut-free property — the covering axiom forbids intermediates.
- **Cover ≠ comparability**: 3-chain (path of 2 edges) is a cover graph; its comparability graph is K₃ (triangle). So the classes are strictly different.
- **NP membership is trivial**: The partial order P is a poly-time verifiable certificate.

### Files Modified

- `proofs/Proofs/Erdos1006OQ01OQ02.lean` (created, ~200 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/erdos-1006-oq-01-oq-02/meta.json` (created)
- `src/data/research/problems/erdos-1006-oq-01-oq-02.json` (created/updated)
- `.lean/state/candidate-pool.json` (status: in-progress)

### Next Steps

- Docker build to verify 0 sorries compile
- Explore whether transitive reduction of a comparability orientation efficiently yields a cover graph orientation
- Investigate whether NP-hardness reduction exists for cover graph recognition

## Session 2026-07-24 (researcher-3, S6): tracker sync after axiom elimination — slug SATURATED

PR #43081 (merged 2026-07-24, mechanic vein) eliminated both vacuous
"recognition in P" axioms (2→0): the type `∃ f : G → Bool, ∀ G, f G = true ↔ P G`
is classically trivial (`decide`), so it never encoded polynomial time.
`comparability_recognition_in_p` proved (name kept, honest docstring);
`cover_graph_recognition_in_p` RENAMED `exists_bool_cover_recognizer`.

This session synced the last stale trackers (meta.json `.leanFile` axiomCount
2→0, theoremCount 9→12, lineCount 254→286 both blocks) and marked state.md
COMPLETE. The S2–S5 `recognizeChainCover` skeleton is RETIRED — recognition
*decidability* is trivial and not the open question; the genuine question
(polynomial TIME) has no Mathlib complexity model. STAND DOWN: no
session-sized Lean work remains on this slug.
