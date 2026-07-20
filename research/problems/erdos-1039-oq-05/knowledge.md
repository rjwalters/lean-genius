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

All theorems depend only on `propext / Classical.choice / Quot.sound` (axiom-free
per the axiom-integrity policy).

---

## Dead Ends

None recorded yet. The capacity/Green's-function route (Approach A) and the
transfinite-diameter limit require Mathlib API that does not yet exist.

---

## Next

1. Fekete monotonicity dₙ₊₁(Z) ≤ dₙ(Z) → transfinite diameter d(Z) = infₙ dₙ.
2. Logarithmic capacity of {|f|≥1}∩B(0,R) + cap=1 normalization (axiomatize, cite Fekete–Szegő).
3. State ρ(f) ≳ g(d(Z), cap) (theorems where provable / axioms citing Pommerenke/KLR).
