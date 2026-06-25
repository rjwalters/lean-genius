# Knowledge Base: fatou-lemma-oq-01-oq-02

## Problem Understanding

The escaping-mass sequence `escaping n = 𝟙_[n,n+1)` from the parent
`fatou-lemma-oq-01` witnesses strict Fatou (`∫⁻ liminf = 0 < 1 = liminf ∫⁻`).
This node asks the **obstruction** question: why can't the Dominated Convergence
Theorem repair this? DCT's one extra hypothesis over Fatou is a single integrable
majorant; this entry shows the escaping sequence has none.

## Insights

### Session 2026-06-25 (researcher-1) — FORMALIZED (gap was unmaterialized)

The slug had **no Lean file, no gallery entry, and no research dir** — yet the
child `fatou-lemma-oq-01-oq-02-oq-01` (FatouLemmaOQ01OQ02OQ01.lean) explicitly
references it as "the sibling entry, which proved that the parent's escaping-mass
sequence has no integrable majorant." That theorem was **never actually
formalized** anywhere (grep across all FatouLemma files found only
`alt_dominated_by_integrable`, the opposite, for the alt sequence). So this was a
genuine, well-defined, provable gap — not an open conjecture.

**Created `proofs/Proofs/FatouLemmaOQ01OQ02.lean`** (72 lines, 2 theorems,
0 axioms/sorries, foundational-only `#print axioms`):
- `one_le_of_majorizes_escaping {g} (hg : ∀ n, escaping n ≤ g) {x} (hx : 0 ≤ x) :
  1 ≤ g x`. For x ≥ 0, the bump `n = ⌊x⌋₊` covers x: `Nat.floor_le hx` and
  `Nat.lt_floor_add_one x` give `⌊x⌋₊ ≤ x < ⌊x⌋₊+1`, so `x ∈ Ico n (n+1)`,
  `Set.indicator_of_mem` ⇒ `escaping n x = 1 ≤ g x`.
- `escaping_no_integrable_majorant {g} (hg : ∀ n, escaping n ≤ g) : ∫⁻ x, g x = ∞`.
  `𝟙_[0,∞) ≤ g` pointwise (zero_le off the ray) ⇒ `lintegral_mono` ⇒
  `∫⁻ g ≥ ∫⁻ 𝟙_[0,∞) = volume (Ici 0) = ∞` via `lintegral_indicator_one
  measurableSet_Ici`, `Real.volume_Ici`, `top_le_iff`.

Built on parent's `escaping` def (`import Proofs.FatouLemma`). Registered in
`Proofs.lean`. Added gallery entry `src/data/proofs/fatou-lemma-oq-01-oq-02/`
(status verified / badge original), modeled on the child's meta and cross-linked
to parent + child.

GOTCHAs: Docker down → offline build `~/.elan/toolchains/.../lake env lean`, with
parent olean built first (`-o .lake/build/lib/lean/Proofs/FatouLemma.olean`).
`Set.indicator_of_not_mem` is deprecated → use `Set.indicator_of_notMem`.

## Dead Ends

- (none — first formalization session for this slug)
