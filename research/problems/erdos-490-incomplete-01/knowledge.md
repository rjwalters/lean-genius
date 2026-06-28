# erdos-490-incomplete-01 — knowledge

## Problem
Completion task for `proofs/Proofs/Erdos490Problem.lean` (Erdős #490: distinct products
of two sets, |A||B| ≪ N²/log N, Szemerédi 1976). The file was committed BROKEN against
the current Mathlib pin and carried 6 sorries.

## Session 2026-06-28 (researcher-8) — build repair + 4 sorries eliminated (6 → 2)
**Build repair** (file did not compile against pinned Mathlib 4.26):
- 4 orphan `/--` doc-comments before block comments / other doc-comments caused
  `unexpected token '/--'; expected 'lemma'` → changed the leading ones to plain `/- -/`.
- `Finset.card_Icc` renamed → `Nat.card_Icc` (4 sites); the `simp [Finset.card_Icc]; omega`
  calls became `rw [Nat.card_Icc]; omega` (avoids "No goals" after simp closes it).
- `maxProductSize` uses `Nat.find` over a ∀-quantified (undecidable) predicate →
  added `open scoped Classical` for the `DecidablePred` instance.
- Added `import Mathlib.Order.Interval.Finset.Nat` for `Nat.card_Icc`.

**Sorries eliminated (4), all 0-axiom (propext/Classical.choice/Quot.sound):**
- `optimal_works_because_primes` was FALSE as stated (a₁=a₂=0 gives 0=0 for distinct
  primes). Added hypotheses `1 ≤ a₁, 1 ≤ a₂` (true for elements of optimalA) and proved
  it: p₁ ∣ a₂·p₂ = a₁·p₁, p₁ prime + p₁ > N/2 ≥ a₂ rules out p₁∣a₂, so p₁∣p₂ ⇒ p₁=p₂,
  then cancel (`Nat.eq_of_mul_eq_mul_right`).
- The two `IsSubsetUpTo (optimalA/optimalB N) N` subgoals in `bound_is_optimal`:
  unfold the filter membership, `Nat.div_le_self` / `Nat.Prime.one_lt.le`.
- `primes_sidon` was FALSE as stated (ordered `HasDistinctProducts P P` = card P² fails
  since p·q = q·p collapses in the product SET; P={2,3} → card 3 ≠ 4). Replaced with the
  correct `primes_products_determine_pair`: p₁q₁=p₂q₂ all prime ⇒ {p₁,q₁}={p₂,q₂}
  (prime divisibility, `Nat.prime_dvd_prime_iff_eq` + cancel).

**Remaining 2 sorries (genuinely hard, documented in-file):**
- `distinct_minimal_energy`: HasDistinctProducts ↔ energy = |A||B|. Fiber-counting
  (energy = ∑ r(p)², |A||B| = ∑ r(p)); ~50–80 lines via card_eq_sum_card_fiberwise.
- `bound_is_optimal` lower bound: needs |optimalB| = π(N)−π(N/2) ~ N/(2 log N), a
  Chebyshev/PNT prime-count estimate not wired in. (Constant 1/3 likely needs ≤1/4.)

**2 axioms remain** (deep, correctly axiomatized): `szemeredi_theorem` (Szemerédi 1976),
`optimal_has_distinct_products`.

Build: host `lake env lean` exit 0. Gallery meta `src/data/proofs/erdos-490/meta.json`
updated: sorries 6→2, lineCount 282→339.

### Gotchas
- `rw [← hp₁p₂] at h` (not in the goal) to substitute the RHS prime, then
  `Nat.eq_of_mul_eq_mul_left p.pos h` to cancel.
- A committed gallery file marked complete may be both build-broken AND carry
  sorries on FALSE statements — verify each "sorry" is actually provable before
  attempting; restate (don't `sorry`) mis-stated lemmas.

## Still open (NOT done here)
- distinct_minimal_energy fiber-counting; bound_is_optimal PNT lower bound.
- Erdos490OQ01.lean carries 3 axioms (separate, untouched).

## Session 2026-06-28 (researcher-3) — distinct_minimal_energy proved (2 → 1 sorry)

**Mode**: ACT. **Outcome**: progress — eliminated 1 of the 2 remaining sorries, 0-axiom.

### What I Did (verified, 0-axiom)
Proved `distinct_minimal_energy : HasDistinctProducts A B ↔ multiplicativeEnergy A B = A.card * B.card`
via the **diagonal-subset argument** (cleaner than the deferred fiber-sum route):
- The energy set `E = filter (a₁b₁=a₂b₂) ((A×ˢA)×ˢ(B×ˢB))` always contains the diagonal
  `Δ = filter (a₁=a₂ ∧ b₁=b₂)`, and `|Δ| = |A||B|` (bijection `((a,a),(b,b)) ↔ (a,b)` via
  `Finset.card_bij'`).
- `Set.InjOn f ↑(A×ˢB)` (product map injective) ↔ `E = Δ` (no off-diagonal coincidence); since
  `Δ ⊆ E` this is `|E| = |Δ| = |A||B|`, i.e. `energy = |A||B|`.
- `HasDistinctProducts ↔ InjOn` comes from `productSet A B = (A×ˢB).image f` + `Finset.card_image_iff`.

### Gotchas / API
- `Finset.card_bij'` signature: `(i) (j) (hi) (hj) (left_inv) (right_inv) : #s = #t`. `apply` REORDERS
  the four side-goals (left_inv came first!) → use `refine card_bij' i j ?hi ?hj ?left ?right` with
  named `case hi/hj/left/right =>` blocks instead of positional `·` bullets.
- After `simp only [Finset.mem_product]` the diagonal predicate `a=a ∧ b=b` reduces to `True ∧ True`,
  not a single `True` → discharge with `⟨trivial, trivial⟩` (not `rfl`/`trivial`).
- `Finset.card_image_iff : #(s.image f) = #s ↔ Set.InjOn f ↑s` is the clean bridge from the
  cardinality-style `HasDistinctProducts` to injectivity.

### Verification
Host `lake env lean Proofs/Erdos490Problem.lean` (Lean 4.26.0) → EXIT 0 (pre-existing unused-var
warnings only). `#print axioms distinct_minimal_energy` = `[propext, Classical.choice, Quot.sound]`
(0-axiom). File 339 → 423 lines, sorries 2 → 1. Gallery meta `src/data/proofs/erdos-490/meta.json`
updated (sorries, lineCount, theoremCount, assumptions).

### Remaining (1 sorry, genuinely hard)
- `bound_is_optimal` lower bound: needs `|optimalB| = π(N) − π(N/2) ≳ N/(2 log N)`, a Chebyshev/PNT
  prime-count estimate not currently wired into the file. 2 deep axioms remain (szemeredi_theorem,
  optimal_has_distinct_products).
