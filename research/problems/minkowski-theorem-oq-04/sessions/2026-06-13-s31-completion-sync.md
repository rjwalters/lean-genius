# S31 — COMPLETION-SYNC (researcher-2, 2026-06-13)

**Mode.** COMPLETION-SYNC (doc-only). Base SHA `8e86e7b0527` (origin/main).
Status flipped `active`/`ACT` → `completed`/`COMPLETED`.

## §0 Why this fires
Claimed `minkowski-theorem-oq-04` (RICH). The research tracker read
`active`/`ACT` (iteration 30, last touched 2026-06-02), but the stated
problem is already proved and gallery-verified — a status lag.

## §1 The stated problem is solved
OQ04 problem statement: Blichfeldt's theorem (1914) — any measurable
S ⊆ ℝⁿ with vol(S) > k contains k+1 distinct points whose pairwise
differences lie in ℤⁿ; plus the Minkowski corollary.

Evidence (all on origin/main):
- `proofs/Proofs/MinkowskiTheoremOQ04.lean`: 0 real sorries, 0 axioms,
  17 theorems, 1126 LOC.
- Gallery `src/data/proofs/minkowski-theorem-oq-04/meta.json`: status
  `verified`, badge `original`, sorries 0, axiomCount 0, lineCount 1126,
  theoremCount 17 (S30's mechanic-pending count bumps have landed).
- Matching theorems:
  - `blichfeldt_general_finset` (L720): Finset of card k+1 ⊆ S, pairwise
    differences in `stdLattice n` (= ℤⁿ). Exactly the problem statement.
  - `blichfeldt_general_pairwise` (L683): adds `i ≠ j → pts i - pts j ≠ 0`
    (the "distinct points" clause).
  - `minkowski_from_blichfeldt` (L764): the convex centrally-symmetric
    vol > 2ⁿ ⇒ nonzero lattice point corollary.

## §2 Out of scope — optional follow-on
The tracker's open item is the general-LATTICE generalization program
(S23 roadmap): replace `stdLattice n` with `Submodule.span ℤ (Set.range b)`
for an arbitrary basis `b`.
- PR-A (S27): `volume_eq_setLIntegral_indicator_tsum_lattice` — landed.
- PR-B (S30): `blichfeldt_general_lattice` — landed (Docker 3075 jobs clean).
- PR-C (pending): `minkowski_general_k_lattice` (~50 LOC, paste-ready in
  `s23-lattice-generalization-spec.md §2.2`).

This generalization is **beyond the stated OQ04** and is Docker-gated:
`timeout 5 docker info` exits 124 at S31 entry (daemon down — same fleet-wide
outage). It can resume as follow-on; it does not block completion of the
stated problem.

## §3 Decision
Per the status-sync rule (main theorem proves the problem statement →
completed; cf. cramers-rule-oq-03-oq-03, euler-totient completion-syncs),
flip `active` → `completed`. Doc-only, no `.lean`.

## §4 Ship scope
3 files: this memo, `state.md` (S31 block + markers), JSON tracker
(status/phase/focus/nextAction/iteration 30→31/attemptCounts 29→30/
lastUpdate). No `.lean`, no sibling edits, no gallery `meta.json` touch
(already verified + count-synced).
