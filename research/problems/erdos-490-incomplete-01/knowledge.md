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

## Session 2026-07-04 (researcher-11) — gallery-integrity sync + frontier reconfirm

**Mode**: ORIENT + gallery-integrity fix. **Outcome**: no `.lean` change (file already
0-sorry / 2-axiom and merged on `main` at 588 lines); corrected a stale metadata defect
and sharpened the runway. Does **not** touch the two deep axioms.

### State reconfirmed (on `main`)
`Erdos490Problem.lean` = 588 lines, **0 sorries, 2 axioms** (`szemeredi_theorem`,
`primes_upper_half_lower_bound`), 19 theorems, 15 defs. The 07-04 Bertrand session
(#34644, researcher-5) is on `main` but was **absent from this knowledge file** — its
lemmas `optimalB_nonempty` / `optimalB_card_pos` / `primeCounting_half_lt` discharge the
*qualitative* content of the Chebyshev axiom (there is ≥1 prime in `(N/2,N]` for `N≥2`,
via Mathlib's `Nat.exists_prime_lt_and_le_two_mul`); the axiom now asserts purely the
*quantitative* rate `c·N/log N`.

### Gallery-integrity defect fixed (this session)
Commit #34644's message claimed it synced the gallery meta to 588 lines / 19 theorems,
but it only updated a *section-summary* block — the **canonical `leanFile` block** in
`src/data/proofs/erdos-490/meta.json` was left stale at `lineCount 557 / theoremCount 16`.
Synced it to `588 / 19` (axiomCount 2, definitionCount 15, sorries 0 were already correct).
Pure metadata; the already-merged `.lean` file is untouched, so no rebuild needed.
- **Worktree gotcha (recorded):** the `Edit` tool's writes silently did **not** persist to
  disk in this researcher worktree (git diff stayed empty though Read showed the change) —
  a `python3`/`Bash` in-place write was needed. Verify writes with `git diff`, not Read,
  in these worktrees.

### Frontier reconfirmed — quantitative axiom stays BLOCKED (multi-session)
`primes_upper_half_lower_bound` = the only in-scope elimination target, and it remains
**blocked on central-binomial interval-count infrastructure** absent from the Mathlib pin,
exactly as researcher-1's 07-02 ORIENT found. The one correct route (do NOT subtract two
Chebyshev bounds — that bottoms out at `c=0`) is the **direct central-binomial count on
`(N/2,N]`**: primes `p∈(m,2m]` (`m=⌊N/2⌋`) divide `centralBinom m` to exactly the first
power, so `∏_{m<p≤2m} p ∣ centralBinom m`; combine `Nat.four_pow_lt_mul_centralBinom`
(`4^m < (2m+1)·centralBinom m`) with the **small-prime contribution upper bound** on
`centralBinom` to get `∏_{N/2<p≤N} p ≳ 4^m/poly(m)`, hence with `p ≤ N` per factor
`(π(N)−π(N/2))·log N ≳ N`. The crux (and the multi-session cost) is formalizing that
small-prime contribution bound; `Mathlib.NumberTheory.Bertrand` carries the two
`centralBinom` inequalities as the stepping stones to mine. `szemeredi_theorem` (the
N²/log N *upper* bound) is not attackable.

**Recommendation:** leave both axioms; they are correctly isolated and minimal. This
problem is at a stable frontier — the next genuine advance is a dedicated multi-session
central-binomial build, not a single-session sorry. `optimalB_card_eq_primeCounting`
already pins the target to `Nat.primeCounting`, so that build's deliverable is exactly a
lower bound on `π(N) − π(N/2)`.

## Session 2026-07-07 (researcher-10) — ORIENT: upstream confirms axiom is blocked (Mathlib Chebyshev.lean)

**Mode**: ORIENT (axiom-reachability, upstream re-survey). **Outcome**: no `.lean` change
(file unchanged on `main`: 588 lines, 0 sorries, 2 axioms). A definitive *upstream* finding
that settles the elimination question for `primes_upper_half_lower_bound` with an authoritative
citation, superseding the earlier "PrimeCounting.lean has no lower bound" reasoning.

### KEY UPSTREAM FINDING (via `gh api .../contents/...?ref=v4.26.0`)
Mathlib v4.26.0 **now ships `Mathlib/NumberTheory/Chebyshev.lean`** (it did not when the earlier
sessions surveyed only `PrimeCounting.lean` / `Bertrand.lean`). It defines the Chebyshev
functions `θ` (`Chebyshev.theta`) and `ψ` (`Chebyshev.psi`) with scoped notation, plus:
- `theta_le_log4_mul_x : 0 ≤ x → θ x ≤ log 4 * x`  — Chebyshev **upper** bound.
- `psi_le_const_mul_self`                          — Chebyshev **upper** bound on ψ.
- `theta_mono`, `psi_mono`, `theta_nonneg`, `psi_nonneg`, `theta_eq_log_primorial`,
  `psi_eq_theta_add_sum_theta`, `sum_PrimePow_eq_sum_sum`, `theta_le_psi`.

**Crucially, the module's own "Future work" docstring (line ~44) lists**:
> - Prove Chebyshev's lower bound.

So Mathlib itself does **not** yet have any lower bound on θ/ψ (hence none on `π`), and flags it
as unproven future work. This is the *exact* analytic input that `primes_upper_half_lower_bound`
isolates. Conclusion, now upstream-authoritative: the axiom is **not eliminable** against the
current pin by any Mathlib lemma — eliminating it means *proving Chebyshev's lower bound from
scratch* (central-binomial route: `ψ(2n) ≥ log C(2n,n) ≥ n·log4 − log(2n+1)`, using
`Nat.four_pow_lt_mul_centralBinom`). That is a genuine multi-session build, exactly as the
07-02 / 07-04 ORIENT sessions found. `szemeredi_theorem` (the N²/log N *upper* bound) stays
axiomatized (deep, not attackable).

### Runway upgrade for the eventual build
When that build happens it should now target Mathlib's `Chebyshev.psi`/`theta` API directly
(reuse `theta_eq_log_primorial`, `psi_eq_theta_add_sum_theta`) rather than rolling bespoke
prime-product machinery — the θ↔ψ scaffolding and the centralBinom inequalities in
`Mathlib.NumberTheory.Bertrand` are the two pieces to bridge. If/when a `theta_ge_*` lower
bound lands upstream, `primes_upper_half_lower_bound` collapses to a short derivation via
`optimalB_card_eq_primeCounting` + a θ→π count on `(N/2, N]`.

### Unmerged sibling branch (flagged, not merged)
`research/erdos-490-chebyshev-theta-gap` (commit `48cca03a48c`, **not on `main`**) restates the
analytic axiom against `Chebyshev.theta` and adds a verified θ→π bridge but **does not reduce
the axiom count** (still 2). It is a pure hygiene refactor pinning the axiom to the canonical θ
lower bound. A build-capable session should evaluate whether to merge it; this ORIENT session
did not (cannot build-verify here, and it yields no axiom reduction so the merge risk is not
justified without a green build).

### Status
No math change. Both axioms remain correctly isolated and minimal. Problem stays at a stable,
well-characterized frontier: the sole in-scope elimination target is blocked on an input that
Mathlib upstream itself lists as future work.

## Session 2026-07-07 (researcher-4) — combinatorial crux of Chebyshev θ-gap axiom VERIFIED

**Mode**: ACT (axiom-reduction). **Outcome**: progress — new standalone 0-axiom/0-sorry file
`Erdos490Chebyshev.lean` (205 lines, 5 lemmas) reduces the remaining analytic axiom
`chebyshev_theta_upper_half_lower_bound` to an elementary explicit lower bound. Axiom NOT
eliminated (main file unchanged, still 2 axioms).

### What I built (verified 0-axiom: `#print axioms` = [propext, Classical.choice, Quot.sound])
- `small_prime_prod_le`: `∏_{p≤2n/3, prime} p^{v_p} ≤ (2n)^√(2n)·4^(2n/3)` — extracted/adapted
  from Mathlib's `centralBinom_le_of_no_bertrand_prime` inner argument (kept the large primes
  as a separate factor instead of assuming they don't exist).
- `centralBinom_le_small_mul_large` (THE CRUX): `centralBinom n ≤ (2n)^√(2n)·4^(2n/3)·∏_{n<p≤2n}p`.
  Three-way factorisation split of `range(2n+1)` by `(·≤n)`: small band via the lemma above,
  middle band `(2n/3,n]` contributes 1 (`factorization_centralBinom_of_two_mul_self_lt_three_mul`),
  large band `n<p≤2n` has `v_p ≤ 1` (`factorization_choose_le_one`, since `p>n ⇒ 2n<p²`).
- `four_pow_lt_bound`: `4^n < n·(2n)^√(2n)·4^(2n/3)·∏_{n<p≤2n}p` (combine crux with
  `Nat.four_pow_lt_mul_centralBinom`).
- `theta_gap_eq_log_prod`: `θ(2n)−θ(n) = log ∏_{n<p≤2n}p` (mirror of main file's
  `theta_gap_eq_sum_optimalB` for the interval (n,2n]; `Chebyshev.theta` + `sum_sdiff` + `log_prod`).
- `theta_gap_lower_bound` (deliverable): `θ(2n)−θ(n) ≥ n·log4 − ⌊2n/3⌋·log4 − log n − √(2n)·log(2n)`
  for `n≥4` (cast `four_pow_lt_bound` to ℝ, take logs, `linarith`). RHS `≥ (n/3)log4 − log n − √(2n)log(2n)`.

### Key facts
- Mathlib's `Mathlib.NumberTheory.Chebyshev` explicitly TODOs "Prove Chebyshev's lower bound" — so
  the θ lower bound is a genuine gap, and the axiom is not laziness.
- The Mathlib Bertrand factorisation lemmas are PUBLIC (`Nat.` namespace): `pow_factorization_choose_le`,
  `factorization_choose_le_one`, `factorization_centralBinom_of_two_mul_self_lt_three_mul`,
  `prod_pow_factorization_centralBinom`, `four_pow_lt_mul_centralBinom`, `primorial_le_4_pow`.
- To reuse Mathlib's `centralBinom_le_of_no_bertrand_prime` inner argument as a standalone lemma,
  use `let S/f` + `show ∏ p ∈ S, f p ≤ ...` (NOT `set`, which breaks the `primorial` defeq at the
  `prod_le_prod_of_subset_of_one_le'`/`primorial_le_4_pow` step).
- `Real.log_prod {s}{f}(hf)` takes ONLY the ≠0 hypothesis (s,f implicit) — `Real.log_prod _ _ (…)` errors.

### Gotchas / infra
- **exit-135 with NO line number that reproduces on a KNOWN-GOOD file = corrupt Mathlib cache volume**
  (built Erdos490Problem.lean, on main, → identical 135 at 462ms). Fix: `LEAN_SKIP_CACHE=true
  ./proofs/scripts/docker-build.sh …` rebuilds fresh and SUCCEEDS. Retrying with cache did NOT clear it.
- `.loom/worktrees/researcher-4` was DELETED mid-session (concurrent cleanup) → durable worktree at
  `/Users/rwalters/lg-r4-wt`. Heartbeat needs `RESEARCHER_ID=researcher-4` exported (else it reports a
  random runtime id and refuses).
- Aristotle MCP down ("Resource not found").

### Remaining to eliminate the axiom (NOT done here)
1. Analytic tail: `√(2n)·log(2n) = o(n)` and `log n = o(n)` (Mathlib has `Real.isLittleO_log_id_atTop`)
   ⇒ `∃c>0 ∃N₀ ∀n≥N₀, (n/3)log4 − log n − √(2n)log(2n) ≥ c·n`.
2. Small-n reconciliation (4 ≤ N < N₀) via Bertrand (`optimalB_nonempty`, finite min of positive values).
3. Alignment `(2n,n) ↦ (N,N/2)`: set `n=⌊N/2⌋`, `2n∈{N−1,N}`, use `Chebyshev.theta_mono`.
Then replace `axiom chebyshev_theta_upper_half_lower_bound` with a theorem importing this file (2→1 axioms).

## Session 2026-07-08 (researcher-1) — isolate self-contained analytic-tail crux (no verified change: build gate CLOSED + Aristotle DOWN)

**Mode**: BUILD-prep. **Outcome**: no `.lean` change. Sharpened the runway by
isolating the *single* self-contained analytic lemma that eliminates
`chebyshev_theta_upper_half_lower_bound`, with explicit constant and the exact
bridge/alignment/small-N assembly. See session note
`2026-07-08-s-analytic-tail-lemma-isolated.md`.

- **Crux lemma (pure Mathlib, no context files):** `erdos490_analytic_tail`:
  `∃ c>0, ∃ N₀, ∀ n≥N₀, c·n ≤ n·log4 − (2n/3)·log4 − log n − √(2n)·log(2n)`.
  Take `c = log4/6`; RHS `= (n/3)log4 − log n − √(2n)log(2n)`; both tails are
  `o(n)` (`Real.isLittleO_log_id_atTop`; `√(2n)log(2n)/n = log(2n)/√(2n)·√2 → 0`).
- **Bridge** (clean-real RHS ≤ `theta_gap_lower_bound`'s RHS): `⌊2n/3⌋ ≤ 2n/3`
  and `Nat.sqrt(2n) ≤ Real.sqrt(2n)` with `log4>0`, `log(2n)≥0`.
- **Alignment**: `n = ⌊N/2⌋`, `θ(N/2)=θ(n)`, `θ(N)≥θ(2n)` via `Chebyshev.theta_mono`
  (since `N ≥ 2⌊N/2⌋`); `n ≥ N/3` ⇒ constant `c/3 = log4/18` for `N ≥ 2·max N₀ 4`.
- **Small N** (`4 ≤ N < N₁`): each `θ(N)−θ(N/2) > 0` (Bertrand: `optimalB_nonempty`;
  `theta_gap_eq_sum_optimalB` with `log p > 0`); take finite min of `(θgap)/N`.
- **Why no commit**: both verification paths down; math PRs auto-merge without
  Lean CI, so unbuilt `.lean` on `main` is unsafe. Recipe documented for a
  build-capable / Aristotle-up session to paste-and-verify (axiomCount 2 → 1).

## Session 2026-07-08 (researcher-3) — feasibility assessment, no code change

**Current file state** (ahead of the notes above): `Erdos490Problem.lean` is now
**0 sorries, 2 axioms** — the last `bound_is_optimal`/PNT sorry was cleared in
#31355/#31517/#31625/#34644/#35166. Remaining axioms:
- `szemeredi_theorem` (Szemerédi 1976) — deep, correctly axiomatized.
- `chebyshev_theta_upper_half_lower_bound`: `∃ c>0, ∀ N≥4, c·N ≤ θ(N) − θ(N/2)`.

**Feasibility of discharging the Chebyshev axiom (2→1): confirmed HARD / Mathlib gap.**
Surveyed `Mathlib.NumberTheory.Chebyshev`, `Primorial`, `Bertrand`, `Choose.Central`
(v4.26): Mathlib supplies only **upper** bounds on θ/ψ/primorial
(`theta_le_log4_mul_x`, `psi_le_const_mul_self`, `primorial_le_4_pow`,
`primorial_add_le`) and structural lemmas (`theta_eq_log_primorial`,
`psi_sub_theta_eq_sum_not_prime`, `psi_eq_theta_add_sum_theta`). There is **no**
lower bound on θ, ψ, `primorial`, or the product of primes in a dyadic gap.
The one usable lower-bound seed is `four_pow_le_two_mul_self_mul_centralBinom`
(`4^n ≤ 2n · centralBinom n`), which yields a ψ(2n) lower bound but NOT directly
the θ-gap `θ(N)−θ(N/2)`: bridging needs (i) ψ→θ within `c·√N·log N` via
`psi_sub_theta_eq_sum_not_prime`, and (ii) a dyadic-gap decomposition of ψ. This is
the classical Erdős central-binomial argument (~150–300 LOC of analytic NT), a
genuine multi-session formalization — not a quick axiom elimination. The author's
in-file docstring correctly frames it as "the one irreducible analytic input."
Left axiomatized; the problem's completion task (the 6 original sorries) is done.

## Session 2026-07-08 (researcher-2) — AXIOM ELIMINATED (chebyshev θ-gap → theorem, 2→1 axioms)
**Result**: `chebyshev_theta_upper_half_lower_bound` is now a **theorem** (0-axiom), not an axiom.
`Erdos490Problem.lean` → 1 axiom (only `szemeredi_theorem`), 0 sorries. Docker build green (7744 jobs).

**How** (the crux the prior sessions isolated, now verified):
- New lemma `Erdos490Cheb.erdos490_analytic_tail` (added to `Erdos490Chebyshev.lean`, 0-axiom):
  `∃c>0,∃N₀,∀n≥N₀: c·n ≤ (n/3)·log4 − log n − √(2n)·log(2n)`. Proof: `log n = o(n)` via
  `Real.isLittleO_log_id_atTop`; `√(2n)·log(2n) = o(n)` via `isLittleO_log_rpow_atTop (r=1/2)` +
  `Real.sqrt_eq_rpow` (log x ≤ ε√x ⟹ √x·log x ≤ ε·x); extract N₀ from `Filter.eventually_atTop`,
  final `nlinarith`. Built green first try.
- Wiring in `Erdos490Problem.lean`: chain `c₀·n ≤ realRHS ≤ natRHS ≤ θ(2n)−θ(n)` where the nat
  floor `⌊2n/3⌋ ≤ 2n/3` (`Nat.cast_div_le`) and `Nat.sqrt(2n) ≤ √(2n)` (`Real.nat_sqrt_le_real_sqrt`)
  only enlarge the elementary RHS. Alignment N↦n=⌊N/2⌋ via `Chebyshev.theta_mono` (2⌊N/2⌋≤N) and
  N≤3⌊N/2⌋. Small N (4≤N<N₁=2·max(N₀,4)): uniform `θ(N)−θ(N/2) ≥ log 2 > 0` from `optimalB_nonempty`
  (Bertrand) + `theta_gap_eq_sum_optimalB`, so `c_small = log2/N₁` works — NO finite-min needed.
  Final `c = min (c₀/3) (log2/N₁)`.
- **Reorg**: moved `optimalB_nonempty`/`optimalB_card_pos` above the new theorem (the axiom was
  consumed at `primes_upper_half_lower_bound` before those lemmas were defined).

**Still open**: `szemeredi_theorem` (N²/log N upper bound) — the deep result, stays axiomatized.
**Infra**: exit-135 volume corruption (#35184) hit 5/7 builds; the Problem file needed ~5 retries to
go green. Line-less 135 = infra, RETRY (crux + wiring both correct once a clean run landed).

## Session 2026-07-08 (researcher-10) — AXIOM ELIMINATED in sibling OQ01 (2→1 axioms)

**Mode**: ACT (family axiom-reduction). **Outcome**: progress — eliminated `optimal_lower`
in `Erdos490OQ01.lean` (the open-question sibling file), axiom count **2 → 1**. The main
completion file `Erdos490Problem.lean` was reconfirmed at its stable frontier (0 sorries,
1 deep axiom `szemeredi_theorem`; meta.json in sync — no change).

**What I did (verified 0-axiom, docker 7745 jobs green):** Converted `axiom optimal_lower`
(`maxProd(N) ≥ c·N²/log N`) into a **theorem** by transferring the main file's now-verified
`Erdos490.bound_is_optimal` (the optimal example's lower bound, itself the fruit of
researcher-2's Chebyshev θ-gap work). Since `maxProd N` dominates any valid pair's product
(`maxProd_is_upper`), the specific pair from `bound_is_optimal` (N ≥ 4) transfers the bound;
small cases N ∈ {2,3} use a new helper `maxProd_ge_self` (pair `A=Icc 1 N`, `B={1}`,
`|A||B|=N`) with constant `c = min c₀ (min (log2/2)(log3/3))` so `c ≤ logN/N`.
`#print axioms optimal_lower = [propext, Classical.choice, Quot.sound]` (no sorryAx/ofReduceBool).

**Key wiring:** the two files carry distinct-but-identical defs — OQ01's `IsSubsetUpTo'` =
main's `IsSubsetUpTo`, and OQ01's `HasDistinctProducts'` = main's `ProductMapInjective` (bridge
`Erdos490.productMapInjective_iff_hasDistinctProducts`); convert by `intro`+re-`exact`. Keep the
ℕ→ℝ cast of `maxProd_is_upper` in the same `(A.card*B.card : ℝ)` shape as `bound_is_optimal`'s
`≥` so `linarith` unifies the atom. Constant scaling avoids `gcongr`/`div_le_div_*` name-drift via
`mul_div_assoc` + `mul_le_mul_of_nonneg_right`. Full detail in
`sessions/2026-07-08-r10-oq01-optimal-lower-deaxiom.md`.

**Still open:** `szemeredi_upper` (= `szemeredi_theorem`, the deep N²/log N upper bound) stays
axiomatized in both files — the genuinely hard result, not attackable.
