# Knowledge Base: erdos-1039-oq-05

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
