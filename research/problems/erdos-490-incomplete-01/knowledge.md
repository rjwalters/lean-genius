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

## Session 2026-06-28 (researcher-3) — last sorry eliminated (1 → 0; 2 → 3 axioms)

**Mode**: ACT. **Outcome**: progress — file is now 0-sorry. Traded the final hard sorry
for one explicit, minimal, true axiom isolating the irreducible analytic input.

### What I Did (verified)
- Proved `optimalA_card : (optimalA N).card = N / 2` **(0-axiom)** via
  `optimalA N = Finset.Icc 1 (N/2)` (`Finset.ext` + `simp`; the `range (N+1)` bound is
  automatic since `n ≤ N/2 ≤ N < N+1`) then `Nat.card_Icc; omega`.
- Added axiom `primes_upper_half_lower_bound : ∃ c>0, ∀ N≥4, c*N/log N ≤ (optimalB N).card`
  — the **Chebyshev-type lower bound** on `π(N)−π(N/2)`. This is the *one* irreducible
  input: Mathlib's `Nat.primeCounting` has only an **upper** bound (`primeCounting'_add_le`)
  + monotonicity, **no** lower bound. Confirmed by grepping the pinned Mathlib.
- Rewrote `bound_is_optimal` to derive the lower bound from that axiom:
  `|A|=⌊N/2⌋ ≥ N/4` (for N≥4) and `|B| ≥ c·N/log N` give `|A||B| ≥ (c/4)·N²/log N`.
  `#print axioms bound_is_optimal` = `[propext, Classical.choice,
  optimal_has_distinct_products, primes_upper_half_lower_bound, Quot.sound]` (no sorry,
  and note it does NOT depend on szemeredi_theorem — that's the upper bound).

### Key correctness finding
The file's previously-hardcoded constant `1/3` in `bound_is_optimal` is **FALSE** at small N:
numerically the product ratio `|A||B|·log N/N²` dips to **≈0.115 at N=10** (optimalA=[1,5]
card 5, optimalB={7} card 1, product 5; `5·log10/100 ≈ 0.115`). Only the `∃ c>0` form is
true (a valid c exists, ≲0.11). The theorem is now stated/proved in that honest form, with
the constant produced from the axiom's `c` (final constant `c/4`).

### Gotchas / API
- The goal `(A.card * B.card : ℝ)` elaborates with casts **already distributed**
  (`↑#A * ↑#B`), so do NOT `rw [Nat.cast_mul]` — it fails with "pattern not found".
- The field identity `N/4 * (c*N/L) = c/4 * N²/L` is proved by **`ring` alone** (ℝ is a
  field; `ring` handles `⁻¹` formally, no `L≠0` needed). `field_simp; ring` here errors
  with "No goals to be solved" because `field_simp` closes it first.
- `↑(N/2) ≥ N/4` (real): from nat `N ≤ 4*(N/2)` (proved by `omega`, which knows `/2`),
  then `exact_mod_cast` + `linarith`. Combine the two nonneg lower bounds with `mul_le_mul`.
- One spurious `lake env lean` **exit 139 (segfault, empty log)** occurred then a re-run
  gave exit 0 — transient, not a real error. Always re-run before trusting a 139.

### Status
File: 423 → 468 lines, sorries 1 → 0, axioms 2 → 3, theorems 11 → 13. Gallery meta
`src/data/proofs/erdos-490/meta.json` updated (sorries→0, axiomCount→3, lineCount→468,
theoremCount→13, assumptions rewritten, stale "sorried" section prose corrected).

### Still open (NOT done here)
- Eliminating `primes_upper_half_lower_bound` needs a real Chebyshev lower bound on
  `π(N)−π(N/2)` built from Mathlib's Bertrand/`centralBinom` machinery — a multi-session
  infrastructure effort, not a single sorry. Optional bridge:
  `(optimalB N).card = N.primeCounting − (N/2).primeCounting`.

## Session 2026-06-30 (researcher-3) — AXIOM ELIMINATED: optimal_has_distinct_products (3 → 2 axioms)

**Mode**: ACT (axiom hunt). **Outcome**: progress — eliminated the axiom
`optimal_has_distinct_products`, proving it 0-axiom from existing lemmas. Axiom
count 3 → 2 (only `szemeredi_theorem` and `primes_upper_half_lower_bound` remain,
both genuinely deep/analytic).

### What I Did (verified, 0-axiom)
The file already contained `optimal_works_because_primes` (the elementwise fact:
`a₁p₁ = a₂p₂` with `aᵢ∈[1,N/2]`, `pᵢ` prime `>N/2` ⟹ `a₁=a₂ ∧ p₁=p₂`, via prime
divisibility). The axiom `optimal_has_distinct_products` was just the packaged
`HasDistinctProducts (optimalA N) (optimalB N)` form of that. Bridged them:
- `productSet_eq_image`: `productSet A B = (A ×ˢ B).image (·.1 * ·.2)`.
- `hasDistinctProducts_iff_injOn`: `HasDistinctProducts A B ↔ Set.InjOn (·.1*·.2) ↑(A×ˢB)`
  — one `rw` chain: `HasDistinctProducts, productSet_eq_image, ← card_product, card_image_iff`.
- `productMapInjective_iff_hasDistinctProducts`: the elementwise `ProductMapInjective`
  def (which was defined but never used!) equals `HasDistinctProducts`.
- `optimal_has_distinct_products` (now a theorem): `rw [← productMapInjective_iff_…]`,
  unfold `optimalA`/`optimalB` filter membership, feed `optimal_works_because_primes`.

`#print axioms optimal_has_distinct_products = [propext, Classical.choice, Quot.sound]`.

### Gotchas / API
- `Finset.card_image_iff : #(s.image f) = #s ↔ Set.InjOn f ↑s` is the clean bridge
  (same one `distinct_minimal_energy` used internally — I extracted it as a reusable lemma).
- `Set.InjOn f ↑s` unpacks with `rintro ⟨a₁,b₁⟩ hx ⟨a₂,b₂⟩ hy hfxy` then
  `Finset.mem_coe, Finset.mem_product` on the hyps; conclude with `Prod.mk.injEq`.
- A placeholder comment left where the `axiom` was MUST be a plain `/- -/` block, not
  `/-- -/` doc-comment — an unattached doc-comment gives `unexpected token '/--'; expected lemma`.
- `optimal_works_because_primes` has auto-bound implicit `{N}`; it unifies from the
  `aᵢ ≤ N/2` hypotheses, so no explicit `N` arg needed.

### Status
File 506 → 557 lines, axioms 3 → 2, theorems 14 → 16, sorries 0. Host
`lake env lean Proofs/Erdos490Problem.lean` EXIT 0. Gallery meta updated
(axiomCount 3→2, lineCount, theoremCount, originalContributions).

### Still open (NOT done here)
- `szemeredi_theorem` (Szemerédi 1976 upper bound) — deep, correctly axiomatized.
- `primes_upper_half_lower_bound` (Chebyshev π(N)−π(N/2) ≳ N/log N) — needs central-binomial
  infrastructure absent from the Mathlib pin (only an UPPER prime-count bound exists);
  multi-session build. `optimalB_card_eq_primeCounting` already pins it to `Nat.primeCounting`.

## Session 2026-07-02 (researcher-1) — ORIENT: correct route for `primes_upper_half_lower_bound`

**Mode**: ORIENT (axiom-reachability analysis). **Outcome**: no verified change (file
already 0-sorry, 2 deep axioms); a strategic finding that identifies the *correct* Lean
route to eliminate `primes_upper_half_lower_bound` and rules out the tempting wrong one.

### State reconfirmed
File is 0-sorry with exactly 2 axioms, both genuinely deep and correctly isolated:
- `szemeredi_theorem` (the N²/log N **upper** bound; Szemerédi 1976) — not attackable.
- `primes_upper_half_lower_bound`: `∃ c>0, ∀ N≥4, c·N/log N ≤ (optimalB N).card`, i.e.
  a Chebyshev-strength **lower** bound on `π(N) − π(N/2)`. `optimalB_card_eq_primeCounting`
  already pins it to `Nat.primeCounting`, so elimination = supply this one analytic fact.

### Mathlib survey (pin v4.26)
- `Mathlib.NumberTheory.PrimeCounting`: only an **upper** bound (`primeCounting'_add_le`) +
  `monotone_primeCounting'` + `tendsto_primeCounting`. **No lower bound.** (Reconfirmed.)
- `Mathlib.NumberTheory.Primorial`: `primorial_le_4_pow : n# ≤ 4^n` (upper).
- `Mathlib.NumberTheory.Bertrand`: `Nat.four_pow_lt_mul_centralBinom` (**lower** bound
  `4^n < (2n+1)·centralBinom n`), a `centralBinom n ≤ (2n)^{√(2n)}·4^{2n/3}` **upper**
  bound, and `Nat.exists_prime_lt_and_le_two_mul` (Bertrand's postulate).

### KEY FINDING — the "subtract two Chebyshev bounds" route CANNOT give a positive constant
The obvious plan (build elementary Chebyshev `A·x/log x ≤ π(x) ≤ B·x/log x`, then subtract)
**fails at the constant level**. Elementary Chebyshev gives `A = log 2 ≈ 0.693` (lower) and
`B = 2 log 2 ≈ 1.386` (upper). Then
```
π(N) − π(N/2) ≥ A·N/log N − B·(N/2)/log(N/2) ≈ (A − B/2)·N/log N = (log2 − log2)·N/log N = 0.
```
So no positive `c` comes out of subtracting independent Chebyshev bounds — the elementary
constants are exactly borderline. A future session must **not** try to discharge the axiom
this way even after building Chebyshev; it will bottom out at `c = 0`.

### CORRECT ROUTE — direct central-binomial count on the interval `(N/2, N]`
Count the interval's primes directly (Erdős-style), not by subtraction. With `N = 2m`
(`m = ⌊N/2⌋`): every prime `p ∈ (m, 2m] = (N/2, N]` divides `centralBinom m = C(2m,m)`
to **exactly** the first power, while primes `p ≤ 2m/3` and the small-prime contribution
are controlled by `primorial_le_4_pow` / the Bertrand upper bound. Combined with the lower
bound `4^m/(2m+1) < centralBinom m` (`Nat.four_pow_lt_mul_centralBinom`), one gets
`∏_{N/2 < p ≤ N} p ≳ 4^m / (small-prime factor)`, hence
`(π(N) − π(N/2))·log N ≳ N`, i.e. the wanted `≳ N/log N`. This IS elementary (so the
in-file docstring "Chebyshev-strength and elementary" is accurate), but it is a genuine
multi-session Lean build: the crux is formalizing the small-prime contribution bound of
`centralBinom` — none of that assembly exists in the pin. `Mathlib.NumberTheory.Bertrand`
already carries the two centralBinom inequalities (`four_pow_lt_mul_centralBinom` +
`centralBinom_le_...`) as private-ish stepping stones, so this is the file to mine.

### Also noted
Bertrand (`exists_prime_lt_and_le_two_mul`) alone yields only `(optimalB N).card ≥ 1` per
dyadic block — a qualitative nonemptiness floor, orders of magnitude short of the `N/log N`
rate. Not worth adding as a lemma; it does not advance the axiom.

### Recommendation
Leave both axioms. `primes_upper_half_lower_bound` is **BLOCKED on central-binomial
interval-count infrastructure** (the small-prime contribution bound), not a single-session
sorry. Route above is the entry point for a dedicated multi-session effort.
