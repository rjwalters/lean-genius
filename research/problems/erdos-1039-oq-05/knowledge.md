# Knowledge Base: erdos-1039-oq-05

## Session 2026-07-21 (researcher-1) — asymptotic sharpness of the root-of-unity lower bound (0-axiom); ELEMENTARY LAYER SATURATED

**Mode**: REVISIT (RICH). **Triage first**: the scoped "general lower bound
dₙ ≥ n^{1/(n-1)}" that earlier sessions flagged as NEXT is **already on main** —
`transfiniteDiameterN_rootsOfUnity_ge` (#40737) plus `one_le_transfiniteDiameter`
and `transfiniteDiameter_mem_Icc_one_two` (`d ∈ [1,2]`), and the transformation
laws (#40759). Verified against the actual `.lean`, not the tracker's stale
`nextAction`. So the elementary lower-bound program is complete.

**Added** (1 axiom-free theorem, host-verified v4.31.0 `lake env lean` exit 0,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`):
- `tendsto_rootsOfUnity_lowerBound_one` — **`(m+2)^{1/(m+1)} → 1`** as `m → ∞`.
  The root-of-unity lower bounds `dₙ ≥ n^{1/(n-1)}` converge to `1`, so the
  elementary method is **asymptotically sharp**: it certifies exactly `d ≥ 1`
  (= logarithmic capacity of the disc) and its per-term bounds cannot exceed `1`
  in the limit — it recovers the Fekete–Szegő value `d = 1` sharply *from below*.
  Proof: `tendsto_rpow_div_mul_add 1 1 (-1)` gives `x^{1/(x-1)} → 1`; compose
  with `m ↦ (m:ℝ)+2` (`tendsto_atTop_add_const_right … tendsto_natCast_atTop_atTop`)
  and `congr 1; ring` on the exponent. ~15 lines.

**Reusable idiom**: `n^{1/(n-1)} → 1` (and any `x^{a/(bx+c)} → 1`) is
`Real.tendsto_rpow_div_mul_add a b c` (Mathlib `.../Pow/Asymptotics.lean`) — no
need to go through `Real.exp`/`Real.log` by hand.

**STATE: elementary layer SATURATED.** Remaining work is DEEP and now recorded as
blocked routes in the tracker: (1) sharp value `d = 1` needs the Fekete–Szegő
matching *upper* bound `d ≤ 1` (potential-theory API absent from Mathlib);
(2) exact `dₙ = n^{1/(n-1)}` for `n ≥ 3` needs the extremality (upper) bound that
roots of unity maximise the spread product — same deep obstruction. Do NOT
attempt per-`n` enumeration (d₅, d₆, …) — that is enumeration theater with no new
mechanism. Future sessions on this slug should STAND DOWN unless Mathlib gains
capacity/Fekete–Szegő API.

## Session 2026-07-21 (researcher-1-6) — transformation laws: scaling covariance + translation invariance (0-axiom)

Added 4 axiom-free theorems to `Erdos1039TransfiniteDiameter.lean` (host-verified
v4.31.0, `lake env lean` exit 0; `#print axioms` on all four =
`[propext, Classical.choice, Quot.sound]`):

- `spreadProduct_smul (c z) : spreadProduct (fun i => c*z i) = ‖c‖^(pairCount n) * spreadProduct z`.
  Each of the `pairCount n` gap factors scales by `‖c‖`. Proof: per-row `← Finset.prod_const`
  + `← Finset.prod_mul_distrib` + `← norm_mul, mul_sub`, then outer `Finset.prod_mul_distrib`
  + `Finset.prod_pow_eq_pow_sum` (∑ card = pairCount by `rfl`).
- `discreteDiameter_smul (hn : 2 ≤ n) (c z) : discreteDiameter (fun i => c*z i) = ‖c‖ * discreteDiameter z`.
  Scaling COVARIANCE. `Real.mul_rpow` + `← Real.rpow_natCast` + `← Real.rpow_mul` then the
  existing private `pairCount_mul_exp hn : (pairCount n)·(2/(n(n-1))) = 1` collapses `‖c‖^{#pairs·e}`
  to `‖c‖^1`. Reuse `pairCount_mul_exp` — do NOT re-derive the exponent identity.
- `spreadProduct_add_const` / `discreteDiameter_add_const` : translation INVARIANCE, since
  `(z i + c) - (z j + c) = z i - z j` (`congr 1; ring` per factor).

These are the finite-`n` shadows of `cap(cK+a) = ‖c‖·cap(K)` — they explain why the
transfinite diameter of a disc of radius `R` (centred anywhere) is `R`. General over all
`n` and all configurations (no disc constraint).

### Feasibility scan for the general lower bound dₙ ≥ n^{1/(n-1)} (deferred)
Needs `spreadProduct(n-th roots of unity) = n^{n/2}` = the discriminant of `X^n-1`.
**Mathlib has no direct roots-of-unity Vandermonde/discriminant product API** (checked
`NumberTheory/Cyclotomic/Discriminant`, `RingTheory/RootsOfUnity/*`, `LinearAlgebra/Vandermonde`).
Route: for `f = X^n-1`, `∏_{j≠k}(ζ_k-ζ_j) = f'(ζ_k) = n·ζ_k^{n-1}`, so `|f'(ζ_k)| = n`,
hence `∏_{k≠j}|ζ_k-ζ_j| = n^n` and `spreadProduct = n^{n/2}`, giving `dₙ = n^{1/(n-1)}`.
~200+ lines from `Polynomial.derivative`/`nthRoots` — a full dedicated session; do NOT attempt
per-`n` bounds (d₅, d₆, …) — that is enumeration theater.

## Session 2026-07-21 (researcher-1) — third term `d₄ ≥ 4^{1/3}` (0-axiom)

**Mode**: REVISIT (RICH, live vein) · **Outcome**: progress — added the third exact
lower-bound term to the sharp-value program, Docker-verified v4.31.

Following the d₃ ≥ √3 term (PR #40639), the natural next milestone was d₄, which makes
the general pattern `dₙ ≥ n^{1/(n-1)}` visible from three data points.

**New content** (`proofs/Proofs/Erdos1039TransfiniteDiameter.lean`, +~140 lines, all
`#print axioms` = `[propext, Classical.choice, Quot.sound]`, Docker build succeeded):
- `spreadProduct_four` — the `4`-point spread is the product of the six pairwise gaps
  (Fin-4 `Ioi` expansion, mirrors `spreadProduct_three`).
- `discreteDiameter_four` — `d₄(z) = (∏ gaps)^{1/6}` (exponent `2/(4·3) = 1/6`).
- `transfiniteDiameterN_four_ge` — **`d₄ ≥ 4^{1/3}`**, attained by the square
  `{1, i, -1, -i}` of fourth roots of unity: four side gaps `√2`, two diagonal gaps `2`,
  spread product `(√2)⁴·2² = 16`, diameter `16^{1/6} = 4^{1/3}` (base-4 rpow identity
  `16^{1/6} = 4^{1/3}` via `Real.rpow_mul`).
- `transfiniteDiameterN_four_mem_Icc` — `d₄ ∈ [4^{1/3}, 2]` (lower bound + Fekete
  `d₄ ≤ d₃ ≤ d₂ = 2`).

The three terms now read `d₂ = 2 = 2^{1/1}`, `d₃ ≥ √3 = 3^{1/2}`, `d₄ ≥ 4^{1/3}`,
i.e. `dₙ ≥ n^{1/(n-1)}`.

**Next (general result, route now fully scoped).** The general lower bound
`dₙ ≥ n^{1/(n-1)}` (which gives `d = limₙ dₙ ≥ 1 =` logarithmic capacity of the disc,
item-1 structural value) reduces to `spreadProduct(nth roots of unity) = n^{n/2}`. All
Mathlib pieces are located: `Complex.isPrimitiveRoot_exp`, `X_pow_sub_C_eq_prod`
(`X^n-1 = ∏(X - ζ^i)`), `eval_multiset_prod_X_sub_C_derivative`
(`∏_{j≠k}(ζ^k-ζ^j) = eval ζ^k of derivative = n·(ζ^k)^{n-1}`, norm `n`). The one piece
to build locally (~40 lines) is the off-diagonal identity
`∏_k ∏_{j≠k} ‖z k - z j‖ = spreadProduct²` (`univ.erase i = Iio i ∪ Ioi i` disjoint,
`Finset.prod_comm` to swap `Iio ↔ Ioi`, `norm_sub_rev`). Estimated ~200 lines total,
0-axiom.

### Files modified
- `proofs/Proofs/Erdos1039TransfiniteDiameter.lean` (+d₄ section)

---

## Session 2026-07-20 (researcher-1, iter 5) — first exact term `d₂ = 2`

**Mode**: continue a RICH node; the elementary transfinite-diameter scaffolding
(spread product, Fekete monotonicity `transfiniteDiameterN_succ_le`, the limit
`transfiniteDiameter = ⨅ₙ d_{n+2}` with antitone/bddBelow/tendsto/`∈[0,2]`) was
already complete on main. **Outcome**: progress — 4 new axiom-free theorems in
`Proofs/Erdos1039TransfiniteDiameter.lean` (`[propext, Classical.choice, Quot.sound]`,
0 sorry / 0 axiom), host-verified directly (`import Mathlib` only, `lake env lean`
exit 0, `#print axioms` on all four).

### What I added
- `spreadProduct_two (z : Fin 2 → ℂ) : spreadProduct z = ‖z 0 - z 1‖` — the double
  product `∏ᵢ ∏_{j>i}` collapses to the single pair `(0,1)` in `Fin 2`.
- `discreteDiameter_two : discreteDiameter z = ‖z 0 - z 1‖` — the normalising
  exponent `2/(n(n-1))` is `1` at `n = 2`, so `dₙ = spreadProduct^1 = ‖z₀-z₁‖`.
- `transfiniteDiameterN_two : transfiniteDiameterN 2 = 2` — the upper bound `d₂ ≤ 2`
  (`discreteDiameter_le_two`) is **attained** by the antipodal pair `![1,-1]`
  (`d₂ = ‖1-(-1)‖ = 2`), via `le_csSup`. The only exactly-computed stage of the
  sequence.
- `transfiniteDiameter_le_two_via_d2 : transfiniteDiameter ≤ 2` — the `d ≤ 2` bound
  is exactly the `n=0` term of the defining `⨅`, now that `d₂ = 2`.

### Key findings / reusable Lean recipe
- **Collapsing `∏ i : Fin 2, ∏ j ∈ Finset.Ioi i, f i j`**: `Fin.prod_univ_two`, then
  `Finset.Ioi (0:Fin 2) = {1}` and `Finset.Ioi (1:Fin 2) = ∅` both close by
  `decide` (Fin is a decidable `LocallyFiniteOrder`); finish with
  `Finset.prod_singleton`, `Finset.prod_empty`, `mul_one`.
- **`![1,-1] : Fin 2 → ℂ` membership/value goals** discharge by `norm_num`
  (evaluates `Matrix.cons_val`, `‖(2:ℂ)‖ = 2`, `‖±1‖ = 1`); the disc-membership
  `∀ i, ‖z i‖ ≤ 1` by `fin_cases i <;> norm_num`.
- **State.md was STALE**: it claimed Fekete monotonicity `dₙ₊₁ ≤ dₙ` was still "next",
  but `transfiniteDiameterN_succ_le` (sup level) + the full limit were already on
  main. Verify the actual .lean before trusting the tracker's "Next Action".

### Next steps (all fiddly, not clearly session-sized)
- Exact `d₃` via 3 cube-roots-of-unity on the boundary (spread `3√3`, `d₃ = 3^{1/2}`).
- Strict `d₃ < d₂ = 2` (Fekete monotonicity strict at the top).
- Sharp limit `d = 1` (= log-capacity of disc) stays deep-blocked (Fekete–Szegő).

## Session 2026-07-20 (researcher-1) — Fekete monotonicity at the SUPREMUM level

Added the sup-over-configurations capstone to `Erdos1039TransfiniteDiameter.lean` (host-verified
v4.31.0; `#print axioms` = propext/Classical.choice/Quot.sound, 0 sorry/0 axiom):

- `unitDiscDiameters n` — the set { dₙ(Z) : Z an n-point config in the closed unit disc }.
- `transfiniteDiameterN n = sSup (unitDiscDiameters n)` — the n-point transfinite diameter of the disc.
- `zero_mem_unitDiscDiameters` / `unitDiscDiameters_nonempty` / `unitDiscDiameters_bddAbove` (≤ 2).
- `transfiniteDiameterN_succ_le` — **d_{n+1} ≤ dₙ for n ≥ 2**. Lifts the pointwise
  `exists_deleteAt_discreteDiameter_ge` over the config sup: `csSup_le` + per-config bound
  (injective ⟹ some deletion in the disc has larger diameter ⟹ `le_csSup`; non-injective ⟹
  diameter 0 ≤ dₙ). NO compactness API needed — only that deletion keeps values in the disc.
- `transfiniteDiameterN_mem_Icc` — `0 ≤ dₙ ≤ 2`, so `d = infₙ dₙ` is a well-defined monotone
  bounded limit.

This resolves the "needs sup over configurations" caveat on next-step #1 (the pointwise heart
was already done as `exists_deleteAt_discreteDiameter_ge`). The compactness worry was unfounded:
the closed unit disc bound `dₙ(Z) ≤ 2` alone makes the sup exist and the monotonicity go through.

### API used
`csSup_le`, `le_csSup`, `BddAbove`, `Set.Nonempty`, `discreteDiameter_le_two`,
`discreteDiameter_pos_iff` (non-injective ⟹ diameter 0), `deleteAt` norm-preservation.

### Remaining open
- Package `d(disc) = ⨅ₙ transfiniteDiameterN n` + `Tendsto` (Antitone+BddBelow).
- Logarithmic capacity + cap=1 (axiomatize, Fekete–Szegő); ρ(f) ≳ g(d,cap) (Pommerenke/KLR axioms).
- Parent ρ(f) ≫ 1/n remains OPEN.


Insights accumulated during research on this problem.

---

## Problem Understanding

Relate ρ(f) (largest inscribed disc of the lemniscate interior {|f|<1}) to two
potential-theoretic invariants of the root set Z = {z₁,…,zₙ}:
- the **transfinite diameter** d(Z), and
- the **logarithmic capacity** of the lemniscate complement {|f|≥1}.

Parent conjecture ρ(f) ≫ 1/n is OPEN. Scope here: make the transfinite-diameter /
capacity objects precise and machine-checkable (Key Lemma 1 of `problem.md`).

---

## Insights

- **The finite discrete spread is entirely elementary.** The finite-n truncation
  of the transfinite diameter, dₙ(Z) = (∏_{i<j}‖zᵢ−zⱼ‖)^{2/(n(n-1))}, needs NO
  capacity infrastructure. The spread product ∏_{i<j}‖zᵢ−zⱼ‖ equals the modulus of
  the **Vandermonde determinant** (Mathlib `Matrix.det_vandermonde`), so the whole
  Key Lemma 1 is host-verifiable Mathlib-only (no Docker).
- **dₙ(K) ≤ diam(K).** For roots in the closed unit disc every gap ‖zᵢ−zⱼ‖ ≤ 2, and
  the Gauss count 2·#{i<j} = n(n−1) makes the exponent cancel exactly, giving the
  clean axiom-free bound dₙ(Z) ≤ 2. The substantive open content is the LOWER
  direction and the Fekete monotonicity dₙ₊₁ ≤ dₙ (which defines the limit d(Z)).

---

## Built (this session — axiom-free, `Proofs/Erdos1039TransfiniteDiameter.lean`)

- `spreadProduct z = ∏_{i<j} ‖zᵢ − zⱼ‖` — the Vandermonde spread.
- `discreteDiameter z = spreadProduct z ^ (2/(n(n−1)))` — the n-point diameter.
- `spreadProduct_nonneg`, `spreadProduct_pos_iff` (>0 ⇔ `Function.Injective z`).
- `spreadProduct_eq_norm_det_vandermonde` — spread = |det Vandermonde| (discriminant link).
- `spreadProduct_le_two_pow` + `two_mul_pairCount` (2·#pairs = n(n−1)).
- `discreteDiameter_nonneg`, `discreteDiameter_le_two` (dₙ ≤ 2 for n≥2 unit-disc roots).
- `logSpread`, `log_spreadProduct`, `discreteDiameter_eq_exp` — the **logarithmic-energy bridge** dₙ(Z) = exp((2/(n(n−1)))·∑_{i<j}log‖zᵢ−zⱼ‖), linking the (multiplicative) transfinite diameter to the (additive) logarithmic energy / capacity.

All theorems depend only on `propext / Classical.choice / Quot.sound` (axiom-free
per the axiom-integrity policy).

## Built (iteration 3 — Fekete deletion identity, axiom-free)

- `deleteAt z k = z ∘ (Fin.succAbove k)` — remove the `k`-th point of an `(n+1)`-tuple.
- `deleteAt_injective` — deleting preserves distinctness of roots.
- `spreadProduct_deleteAt` — **reindexing lemma**: `V(delete k Z)` equals the product
  of `‖zₐ−z_b‖` over exactly the pairs `a<b` avoiding index `k` (double `Finset.prod_bij`
  along the order-embedding `succAbove`, using `succAbove_lt_succAbove_iff` /
  `exists_succAbove_eq`).
- `card_filter_avoid` — `#{k : a≠k ∧ b≠k} = n−1` for distinct `a,b` in `Fin (n+1)`.
- `prod_spreadProduct_deleteAt` — **Fekete deletion identity** `∏ₖ V(delete k Z) = V(Z)^{n−1}`,
  the combinatorial heart of Fekete monotonicity. Each pair survives exactly the `n−1`
  deletions removing neither endpoint; proof: reindex → convert `erase` guards to `if` →
  `prod_comm` to pull `∏ₖ` inside → per-pair `∏ₖ (if … then c else 1) = c^{#avoid} = c^{n−1}`
  → `prod_pow`. Holds for **every** tuple (distinct roots or not).
- `sum_logSpread_deleteAt` — additive/energy form: `∑ₖ logSpread(delete k Z) = (n−1)·logSpread Z`
  for injective `z`, the `log`-shadow of the product identity (bridges to the energy section).

★RECIPE: order-preserving pair reindexing under `Fin.succAbove` = nested `Finset.prod_bij`
with forward map `fun i _ => k.succAbove i`; membership via `succAbove_ne` (≠k) +
`succAbove_lt_succAbove_iff` (order), surjectivity via `Fin.exists_succAbove_eq`. To pull an
index-independent `∏ₖ` through a `k`-dependent `erase` set, first rewrite `s.erase k =
s.filter (·≠k)` (`Finset.filter_ne'`) + `Finset.prod_filter` into an `if`-guard, THEN `prod_comm`.

All iteration-3 theorems: axioms `[propext, Classical.choice, Quot.sound]` (verified via
`#print axioms`) — axiom-free.

---

## Built (iteration 4 — pointwise Fekete monotonicity, axiom-free)

- `exists_deleteAt_discreteDiameter_ge (hn : 2 ≤ n) (z : Fin (n+1) → ℂ)
  (hz : Injective z) : ∃ k, discreteDiameter z ≤ discreteDiameter (deleteAt z k)`.
  For every injective (n+1)-tuple of roots (n ≥ 2), some n-point deletion has
  n-point diameter ≥ the (n+1)-point diameter of the whole tuple — i.e.
  d_{n+1}(Z) ≤ dₙ(delete k Z), the **finite heart of Fekete monotonicity**.
  Proof: additive deletion identity `sum_logSpread_deleteAt`
  (∑ₖ logSpread(delete k Z) = (n−1)·logSpread Z over n+1 terms) ⇒ some term meets
  the mean (`Finset.exists_le_of_sum_le` against the constant (n−1)E/(n+1)) ⇒
  exponent bookkeeping 2/(n(n−1)) · (n−1)/(n+1) = 2/((n+1)n) ⇒ compare via
  `discreteDiameter_eq_exp` + `Real.exp_le_exp`. Axiom-free
  (`#print axioms` = [propext, Classical.choice, Quot.sound]).

★RECIPE: "some sample beats the mean" over a Finset — build the constant function
`fun _ => (∑ f)/card`, show its sum equals ∑ f (`Finset.sum_const` +
`card_univ`/`Fintype.card_fin` + `nsmul_eq_mul` + `field_simp`), then
`Finset.exists_le_of_sum_le univ_nonempty (le_of_eq ...)`. Cast bridge for the
(n+1)-point exponent: `((n+1:ℕ):ℝ) = (n:ℝ)+1` by `push_cast; ring`, then
`add_sub_cancel_right` clears the `((n:ℝ)+1)-1`.

---

## Dead Ends

None recorded yet. The capacity/Green's-function route (Approach A) and the
transfinite-diameter limit require Mathlib API that does not yet exist.

---

## Next

1. ✅ DONE (iter 4, pointwise form `exists_deleteAt_discreteDiameter_ge`). Remaining: upgrade to sup-over-configurations dₙ₊₁ ≤ dₙ (needs compactness/sSup API) and d(Z) = infₙ dₙ.
2. Logarithmic capacity of {|f|≥1}∩B(0,R) + cap=1 normalization (axiomatize, cite Fekete–Szegő).
3. State ρ(f) ≳ g(d(Z), cap) (theorems where provable / axioms citing Pommerenke/KLR).

## Built (iteration 5 — strict positivity of the discrete diameter, axiom-free)

- `discreteDiameter_pos (z) (hz : Injective z) : 0 < discreteDiameter z`.
  `dₙ z = spreadProduct z ^ (2/(n(n−1)))`; injectivity ⇒ `0 < spreadProduct z`
  (`spreadProduct_pos_iff`), and `Real.rpow_pos_of_pos` keeps it positive.
- `discreteDiameter_pos_iff (hn : 2 ≤ n) : 0 < discreteDiameter z ↔ Injective z`.
  Backward = `discreteDiameter_pos`; forward uses that the exponent `2/(n(n−1))`
  is nonzero for `n ≥ 2`, so a vanishing spread product forces `dₙ = 0`
  (`Real.zero_rpow`).

These sharpen `discreteDiameter_nonneg` and supply the strict positivity that
`Real.log (discreteDiameter z)` and `discreteDiameter_eq_exp` silently rely on.
Host-verified `bin/lake env lean` exit 0; `#print axioms` on both =
`[propext, Classical.choice, Quot.sound]`.

## Session 2026-07-20 (researcher-1) — transfinite diameter as a limit (0-axiom)

**Mode**: REVISIT (RICH, live vein) · **Outcome**: closed the limit existence in
`Erdos1039TransfiniteDiameter.lean`, host-verified v4.31.

The knowledge "Next #1" (upgrade the pointwise deletion to the sup-over-configurations
`d_{n+1} ≤ dₙ`) was already DONE in-tree as `transfiniteDiameterN_succ_le` (Fekete
monotonicity, supremum form), with `transfiniteDiameterN_mem_Icc` giving `dₙ ∈ [0,2]`.
So the natural next milestone was assembling the **limit**.

**New content** (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`):
- `transfiniteDiameter := ⨅ n, transfiniteDiameterN (n+2)` — indexed over the `n ≥ 2`
  monotone regime.
- `transfiniteDiameterN_shift_antitone` / `_shift_bddBelow` — the shifted sequence is
  antitone (Fekete) and bounded below by `0`.
- `tendsto_transfiniteDiameterN` — `d_{n+2} → transfiniteDiameter` via Mathlib
  `tendsto_atTop_ciInf` (antitone + bddBelow ⟹ converges to the infimum). The
  transfinite diameter is now a genuine **limit**, not merely an infimum.
- `transfiniteDiameter_mem_Icc` (`d ∈ [0,2]`) and `transfiniteDiameter_le`
  (`d ≤ d_{n+2}` for all `n`).

**Open crux (unchanged).** The sharp value `d = 1` (= logarithmic capacity of the unit
disc) needs the Fekete–Szegő theorem plus extremal root-of-unity configurations: the
`spreadProduct` of the `n`-th roots of unity is the Vandermonde discriminant, giving the
matching lower bound `dₙ ≥ n^{1/(n-1)} → 1`. The current upper bound is the coarse
`dₙ ≤ 2`. Not formalized here.

### Files modified
- `proofs/Proofs/Erdos1039TransfiniteDiameter.lean` (+~55 lines, limit section)

## Session 2026-07-21 (researcher-1): general roots-of-unity lower bound dₙ ≥ n^{1/(n-1)}

Proved the **general** lower bound the sharp-value program was building toward
(docker-verified `Proofs.Erdos1039TransfiniteDiameter`, 0 axioms, 0 sorries):

- **`transfiniteDiameterN_rootsOfUnity_ge (m) : (m+2)^{1/(m+1)} ≤ transfiniteDiameterN (m+2)`**
  — realised by the `n = m+2` complex n-th roots of unity `ζᵏ` (ζ = exp(2πi/n)),
  all on the unit circle. Generalises the bespoke `d₂ = 2`, `d₃ ≥ √3`, `d₄ ≥ 4^{1/3}`.
- **`one_le_transfiniteDiameter : 1 ≤ transfiniteDiameter`** and
  **`transfiniteDiameter_mem_Icc_one_two : transfiniteDiameter ∈ [1,2]`** —
  each `d_{n+2} ≥ (n+2)^{1/(n+1)} ≥ 1`, so the infimum `d = infₙ dₙ ≥ 1`.

### Mechanism (Vandermonde discriminant `spreadProduct = n^{n/2}`)
- `spreadProduct_rootConfig_sq`: `(spreadProduct (rootConfig ζ (m+2)))² = n^n`.
  - Per index `i`, `∏_{j≠i} ‖ζⁱ - ζʲ‖ = n` (`prod_erase_root`): translate `j ↦ j-i`
    on `Fin n` (a `Finset.prod_equiv` group bijection) and pull out the unit `ζⁱ`,
    reducing to `∏_{d≠0} ‖1 - ζᵈ‖ = |∏_{k=1}^{n-1}(1-ζᵏ)| = |n| = n` (`prod_erase_zero`
    from `IsPrimitiveRoot.prod_one_sub_pow_eq_order`).
  - Multiplying over the `n` indices gives the ORDERED off-diagonal product `n^n`,
    which `= (spreadProduct)²` since lower/upper triangles `{j<i}`/`{i<j}` carry equal
    products (`norm_sub_rev` + `Finset.prod_comm'`).
- `discreteDiameter_rootConfig`: `dₙ = (n^{n/2})^{2/(n(n-1))} = n^{1/(n-1)}` (rpow algebra).

### Gotchas (v4.31)
- **`Fin n` has no global `NatCast`** (scoped with the CommRing instance), so
  `((k+1 : ℕ) : Fin (m+2))` does NOT coerce — build the element explicitly as
  `⟨(k+1) % (m+2), Nat.mod_lt _ …⟩` and reason on `.val` via `Fin.ext` / `Fin.ne_of_val_ne`.
- `abel` failed to close `(j - i) + i = j` in `Fin (m+2)`; `by simp` (the `sub_add_cancel`
  / `add_sub_cancel_right` simp set) closes it.
- Annotate `Finset.prod_nbij'` lambda domains (`fun d : Fin (m+2) => …`, `fun k : ℕ => …`)
  or `apply` mis-infers the index types.

### Frontier (UNCHANGED)
The sharp value `d = 1` (logarithmic capacity of the disc) needs the Fekete–Szegő
extremal **upper** bound — DEEP. Parent Erdős #1039 remains OPEN.

### Files modified
- `proofs/Proofs/Erdos1039TransfiniteDiameter.lean` (+~215 lines, roots-of-unity section)

## Session 2026-07-22 (researcher-1-9) — ROUTE DISCOVERY: sharp d = 1 needs only Hadamard's inequality, not Fekete–Szegő

**Mode**: assessment of the two blocked routes. **Outcome**: the "DEEP
Fekete–Szegő / potential theory" assessment for the sharp value d = 1 is
OVERESTIMATED for the disc. Both blockers reduce to **Hadamard's determinant
inequality** — elementary linear algebra:

For n points z₁,…,zₙ in the closed unit disc, the Vandermonde matrix V (rows
(1, zᵢ, …, zᵢⁿ⁻¹)) satisfies
- |det V| = spreadProduct(z) (Mathlib `Matrix.det_vandermonde` ✓ exists), and
- Hadamard: |det V|² ≤ ∏ᵢ (row-norm²) = ∏ᵢ Σₖ |zᵢ|²ᵏ ≤ nⁿ (each |zᵢ| ≤ 1).

Hence **spreadProduct ≤ n^{n/2}**, i.e. dₙ ≤ n^{1/(n-1)} — matching the
formalized roots-of-unity lower bound `transfiniteDiameterN_rootsOfUnity_ge`
EXACTLY. Consequences: **dₙ = n^{1/(n-1)} exactly** (blocker 2 falls) and,
since n^{1/(n-1)} → 1 with `one_le_transfiniteDiameter` already proved,
**d = 1 on the nose** (blocker 1 falls). No potential theory, no Fekete–Szegő.

**Missing ingredient**: Hadamard's inequality is NOT in Mathlib (checked: only
Hadamard product/matrices; no `det ≤ ∏ row norms`, no PosSemidef
`det ≤ ∏ diag`). Formalization plan (2 sessions):
1. **Hadamard via Gram**: for A : Matrix (Fin n) (Fin n) ℂ,
   |det A|² = det (A * Aᴴ) and PSD G := A * Aᴴ has det G ≤ ∏ diag G.
   The PSD lemma by induction via Schur complement, or directly via
   Gram–Schmidt: det A = det of orthogonalized rows × unit triangular, and
   ‖orthogonalized rowᵢ‖ ≤ ‖rowᵢ‖ (Mathlib has `gramSchmidt` +
   `gramSchmidt_orthogonal` in Analysis.InnerProductSpace.GramSchmidtOrtho —
   the determinant link needs building). Mathlib-general, upstream-worthy.
2. **Apply**: row norm² = Σ_{k<n} |zᵢ|²ᵏ ≤ n; chain with det_vandermonde and
   the existing rpow algebra (`discreteDiameter_rootConfig` pattern) to get
   dₙ = n^{1/(n-1)} and d = 1.

This mirrors today's pattern on erdos-85 (f(9), f(10)): "deep" blockers
repeatedly turn out to have elementary mechanisms. Blocker reopen criteria are
hereby met (materially new mechanism identified: Hadamard/Gram, not
potential theory).

## Session 2026-07-23 (researcher-1) — SHARP VALUE CLOSED: d = 1 via Hadamard's inequality (docker-verified, 0-axiom)

**Mode**: REVISIT (executing the 2026-07-22 Hadamard plan). **Outcome**: the full
plan landed in ONE session, not the projected two. `Erdos1039TransfiniteDiameter.lean`
+162 lines (new `Hadamard` section), builds clean in Docker, still 0 axioms / 0 sorries.

### What was proved
- `norm_det_le_prod_norm_row` — **Hadamard's determinant inequality** (complex, row
  form): `‖det M‖ ≤ ∏ᵢ ‖rowᵢ‖₂`. NOT in Mathlib; proved via
  `gramSchmidtOrthonormalBasis_det` (determinant = ∏ ⟪eᵢ, fᵢ⟫ in the Gram–Schmidt
  orthonormal basis) + Cauchy–Schwarz (`norm_inner_le_norm`) with `‖eᵢ‖ = 1`.
  Upstream-worthy standalone lemma.
- `norm_matrixRow_vandermonde_le` — each Vandermonde row of unit-disc points has
  ℓ²-norm ≤ √n (entries are powers `zᵢᵏ`, each ≤ 1).
- `spreadProduct_le_sqrt_pow` — `spreadProduct ≤ (√n)ⁿ = n^{n/2}`.
- `discreteDiameter_le_rpow` / `transfiniteDiameterN_le_rpow` — `dₙ(Z) ≤ n^{1/(n-1)}`
  for all unit-disc configurations (rpow exponent algebra: `(n/2)·(2/(n(n-1))) = 1/(n-1)`).
- `transfiniteDiameterN_eq_rpow` — **exact value** `dₙ = n^{1/(n-1)}` for all n ≥ 2:
  upper = Hadamard, lower = roots of unity (`transfiniteDiameterN_rootsOfUnity_ge`).
  Root-of-unity configurations are extremal at EVERY finite level.
- `transfiniteDiameter_le_one` + `transfiniteDiameter_eq_one` — **d = 1 on the nose**,
  the logarithmic-capacity value of the closed unit disc, with NO Fekete–Szegő and NO
  potential theory. Combines `ge_of_tendsto'` on `tendsto_rootsOfUnity_lowerBound_one`
  with `transfiniteDiameter_le`.

### Lean technique notes (v4.31)
- `gramSchmidtOrthonormalBasis` needs `hrank : finrank = Fintype.card`; supply
  `finrank_euclideanSpace`. Its `.toBasis.det` link to `M.det`: factor through
  `Basis.toMatrix_mul_toMatrix` with the standard basis; the standard-basis coordinate
  matrix of the row family is `Mᵀ` (so `det_transpose` bridges), and
  `OrthonormalBasis.det_to_matrix_orthonormalBasis` kills the unimodular factor in norm.
- Row extraction: `WithLp.toLp 2 (M i) : EuclideanSpace ℂ (Fin n)` (`matrixRow`) makes
  `EuclideanSpace.norm_eq` applicable; the entry rewrite is a `show`-then-`vandermonde_apply`.
- rpow chain: `(√n)ⁿ` → `n^{n/2}` via `Real.rpow_natCast` + `Real.sqrt_eq_rpow` +
  `Real.rpow_mul`; final exponent equality by `field_simp` (needs `n ≠ 0`, `n - 1 ≠ 0`).

### Status
Both 2026-07-22 REROUTED blockers are now RESOLVED (formalized). The scoped
transfinite-diameter program of this OQ is COMPLETE: definition, monotonicity,
transformation laws, exact finite-n values, and the sharp limit d = 1 = cap(disc),
all 0-axiom. Remaining frontier is the ρ(f)-capacity bridge (Green's functions,
Harnack/Koebe) — parent-strength DEEP, out of scope; parent Erdős #1039 stays OPEN.
