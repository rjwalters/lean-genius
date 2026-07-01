# Problem: Higher-Moment British Flag Defect for Orthotopes — the 2k-th Power Alternating Sum

**Slug**: british-flag-theorem-oq-01-oq-02-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap (open-question child of british-flag-theorem-oq-01-oq-02)

## Problem Statement

### Formal Statement

Fix `n ≥ 1` and an axis-aligned box in `ℝⁿ` with opposite corners `a, b : Fin n → ℝ`.
Each of the `2ⁿ` vertices is indexed by a subset `t ⊆ Fin n`, coordinate `i` taking the
"far" value `b i` when `i ∈ t` and the "near" value `a i` otherwise:

  `vertex a b t i = if i ∈ t then b i else a i`   (exactly the parent's definition).

The parent studies the **squared** distance `sqDist a b P t = ∑ᵢ (Pᵢ − vertexᵢ(t))²`.
This problem replaces it by the `2k`-th moment `‖P − vertex(t)‖^{2k} = (sqDist a b P t)^k`
and asks for the vanishing/defect law of the alternating parity sum

  `A_k(P) := ∑_{t ⊆ Fin n} (−1)^{|t|} · (sqDist a b P t)^k`
          `= ∑_{|t| even} ‖P − vertex(t)‖^{2k}  −  ∑_{|t| odd} ‖P − vertex(t)‖^{2k}.`

For `k = 1`, `A_1 ≡ 0` for all `n ≥ 2` is exactly the parent theorem
`alternating_sqDist_zero`; for `n = 2, k = 1` it is the classical British Flag Theorem.

**Conjecture (box moment law).** Write `δᵢ := (Pᵢ − bᵢ)² − (Pᵢ − aᵢ)² = (aᵢ − bᵢ)(2Pᵢ − aᵢ − bᵢ)`
for the per-coordinate squared-distance increment. Then:

1. **Vanishing (main target).** If `k ≤ n − 1` (equivalently `k < n`), then `A_k(P) = 0` for
   *every* box `a, b` and every observer `P`.

2. **Sharp first defect.** If `k = n`, then
     `A_n(P) = n! · ∏ᵢ ((Pᵢ − aᵢ)² − (Pᵢ − bᵢ)²) = (−1)ⁿ · n! · ∏ᵢ δᵢ`,
   which is generically nonzero; it is independent of the observer only up to the
   product structure and vanishes iff some coordinate is "centered" (`Pᵢ = (aᵢ+bᵢ)/2`)
   or degenerate (`aᵢ = bᵢ`). For `n = 2, k = 2` this reads `A_2 = 2·δ₀·δ₁`.

3. **General defect (research core).** For `k ≥ n`, `A_k(P) = (−1)ⁿ ·` [coefficient of the
   full-support multilinear monomial `x₁x₂⋯xₙ` in the reduction of `(C + ∑ᵢ xᵢδᵢ)^k` modulo
   `xᵢ² = xᵢ`], where `C = ∑ᵢ (Pᵢ − aᵢ)²`. Give this coefficient in closed symmetric form.

**Lean theorem shape** (namespace, e.g., `BritishFlagMomentOQ010202`, importing
`Proofs.BritishFlagOrthotopeOQ0102`):

```
def sqDistPow (a b P : Fin n → ℝ) (k : ℕ) (t : Finset (Fin n)) : ℝ :=
  (BritishFlagOrthotopeOQ0102.sqDist a b P t) ^ k

theorem box_moment_vanishes (hk : k < n) (a b P : Fin n → ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * sqDistPow a b P k t = 0

theorem box_moment_first_defect (a b P : Fin n → ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * sqDistPow a b P n t
      = (n ! : ℝ) * ∏ i, ((P i - a i) ^ 2 - (P i - b i) ^ 2)
```

### Plain Language

Stand at any point `P` and look at the `2ⁿ` corners of a rectangular box in `n` dimensions.
Colour a corner "even" or "odd" by the parity of how many of its coordinates sit at the far
face. The British Flag Theorem says the even corners and odd corners give the same **sum of
squared distances**. What if we sum the **fourth** powers instead? The sixth? The `2k`-th?

The engine is the same "telescoping finite difference over the vertex hypercube": summing a
quantity over all corners with alternating `±` signs is the `n`-fold discrete derivative, one
step per coordinate, and each derivative step kills anything that does not genuinely depend on
that coordinate. For a right-angled box the squared distance is a *sum* over coordinates
(`∑ᵢ (Pᵢ − vertexᵢ)²`) — an affine function of the corner's `0/1` toggle vector, so its
`k`-th power reaches "cross-terms" touching at most `k` distinct coordinates. As long as
`k < n`, no term touches all `n` coordinates at once, so the `n`-fold alternating derivative
annihilates everything and `A_k = 0`. Exactly at `k = n` the first full-coordinate cross-term
appears — the product `δ₀δ₁⋯δ_{n−1}` weighted by `n!` — and the parity sum stops vanishing.

### Why This Matters

- **A reusable annihilation lemma.** The whole British-flag family (parent squared-distance,
  the sibling fourth moment, this problem) is one statement: *the alternating powerset sum
  `∑_t (−1)^{|t|} F(t)` annihilates every function `F` whose multilinear expansion in the
  membership toggles omits at least one coordinate, and otherwise returns `(−1)ⁿ` times the
  full-support coefficient.* Isolating "vanishing degree < n ⇒ 0; degree = n ⇒ explicit top
  coefficient" turns each moment identity into a one-line corollary.

- **It unifies and *sharpens* the two existing branches.** The sibling
  (british-flag-theorem-oq-01-oq-02-oq-01) proves the fourth-moment defect for a *general
  parallelepiped* (skew edges), where the squared distance is degree **2** in the toggles, so
  the vanishing threshold is `n ≥ 2k+1` (n≥5 for k=2). For a *right-angled box* the off-diagonal
  Gram entries `⟨uᵢ,uⱼ⟩` vanish, dropping the degree to **1** and improving the threshold to the
  sharper `n ≥ k+1`. This problem pins down that the orthogonality of the box is precisely what
  halves the required dimension.

- **Top Walsh coefficient.** The weight `(−1)^{|t|}` is the top Walsh–Fourier character
  `χ_{univ}` on the hypercube `{0,1}ⁿ`; `A_k(P)` is exactly the top Fourier coefficient of the
  function `t ↦ ‖P − vertex(t)‖^{2k}`. The vanishing law is the statement that a bounded-degree
  polynomial has no top Fourier mass — connecting to the parent entry's third open question.

### Known Results

- **Parent (`k = 1`):** `alternating_sqDist_zero` proves `A_1 ≡ 0` for `n ≥ 2`; the mechanism
  is `∑_{s ⊆ univ∖{i}} (−1)^{|s|} = 0` per coordinate (Mathlib
  `Finset.sum_powerset_neg_one_pow_card_of_nonempty`, cast to ℝ). The `n = 1` segment is the
  sharp boundary where `A_1 ≠ 0`. This is the `k < n` law at `k = 1`.

- **Sibling (`k = 2`, parallelepiped):** `BritishFlagFourthMomentOQ010201.lean` proves
  `fourth_moment_defect_eq_zero` (`n ≥ 5`), `defect4_eq_quartic_piece` (`n ≥ 4` collapses to the
  degree-4 Gram-square piece), and the first nonvanishing value `fourth_moment_defect_n4`:
  `defect₄ = 8·(⟨u₀,u₁⟩⟨u₂,u₃⟩ + ⟨u₀,u₂⟩⟨u₁,u₃⟩ + ⟨u₀,u₃⟩⟨u₁,u₂⟩)`. It already isolates the
  key abstraction `monomial_term_zero` (`∑_t (−1)^{|t|}[S ⊆ t] = 0` for `S ≠ univ`) and its
  evaluator `monomial_term_eval` (`= (−1)ⁿ` iff `S = univ`) — valid for *every* `n`. **Note:**
  for orthogonal edges (a box) all cross Gram entries are `0`, so `fourth_moment_defect_n4`
  collapses to `0`, consistent with the sharper box threshold `k < n` (`A_2 = 0` for `n ≥ 3`,
  and `A_2 = 2δ₀δ₁` at `n = 2`).

- **Finite-difference / inclusion–exclusion:** the general principle that an `n`-fold alternating
  sum extracts the top-degree multilinear coefficient is classical (Stanley, *Enumerative
  Combinatorics* I). Mathlib's `Finset.prod_add` gives the exact telescoping
  `∑_{t ⊆ univ} (∏_{i∈t} pᵢ)(∏_{i∉t} qᵢ) = ∏ᵢ (pᵢ + qᵢ)`.

### Suggested Approach

The recommended path proves the box case cleanly by *factoring over coordinates*, avoiding the
full multinomial bookkeeping the sibling needed for skew edges.

1. **Reduce to a product-of-affine structure.** For a box, `sqDist a b P t = ∑ᵢ gᵢ(t)` with
   `gᵢ(t) = if i∈t then βᵢ else αᵢ`, `αᵢ = (Pᵢ−aᵢ)²`, `βᵢ = (Pᵢ−bᵢ)²`. This is the parent's
   `sqDist`/`vertex` unfolding (`split_ifs`), reused by `import Proofs.BritishFlagOrthotopeOQ0102`.

2. **Vanishing `k < n` — telescoping product.** The cleanest engine is the identity
   `∑_{t⊆univ} (−1)^{|t|} ∏ᵢ fᵢ(t) = ∏ᵢ (fᵢ(∉) − fᵢ(∈))`, an instance of Mathlib
   `Finset.prod_add` (write the sign into one factor). For `(sqDist)^k`, expand the `k`-th power
   as a sum of products of `k` coordinate-indexed factors (via `Finset.sum_pow`/repeated
   `Finset.sum_mul_sum` or `Finset.mul_sum` + `Finset.sum_comm`, mirroring the sibling's
   `hrw`/`sum_comm` cascade). Each resulting product `∏` ranges over a multiset of at most `k`
   coordinates; if `k < n` some coordinate `i₀` is *absent*, so summing the `(−1)^{|t|}` weight
   over `t` factors out `∑_{s ⊆ univ∖{i₀}} (−1)^{|s|} = 0` — precisely the parent's
   `alt_sum_ite_eq_zero` / `real_alt_powerset_zero`, or the sibling's `monomial_term_zero`
   with `S ≠ univ` since `|S| ≤ k < n`.

3. **First defect `k = n`.** Only the full-support term survives. Using `monomial_term_eval`
   (`(−1)ⁿ` on `S = univ`) and the multinomial coefficient counting the `n!` orderings that hit
   each of the `n` coordinates exactly once, obtain
   `A_n(P) = (−1)ⁿ · n! · ∏ᵢ δᵢ = n! · ∏ᵢ (αᵢ − βᵢ)`. Verify the `n = 2` sanity value `2δ₀δ₁`
   against a direct 4-vertex computation (`Fin.sum_univ_four`, as in `fourth_moment_defect_n4`).

4. **General defect `k > n` (research core).** Characterize the full-support coefficient of
   `(C + ∑ᵢ xᵢδᵢ)^k` mod `xᵢ² = xᵢ` in closed form (a sum over surjections `[k] ↠ [n]`, i.e.
   Stirling-number-weighted symmetric functions in `δᵢ` and `C`). This is the genuinely open,
   higher-effort part; the vanishing law and first defect (steps 2–3) are the shippable core.

**Real Mathlib names to lean on:** `Finset.sum_powerset_neg_one_pow_card_of_nonempty`,
`Finset.prod_add`, `Finset.powerset_insert`, `Finset.sum_comm`, `Finset.mul_sum`,
`Finset.sum_mul_sum`, `Finset.sum_filter_add_sum_filter_not`, `Even.neg_one_pow`,
`Odd.neg_one_pow`, `Fin.sum_univ_four`, `Nat.factorial`. Plus the project lemmas
`BritishFlagOrthotopeOQ0102.alt_sum_ite_eq_zero`, `.real_alt_powerset_zero`, and the sibling's
`monomial_term_zero` / `monomial_term_eval`. Do **not** assume a Mathlib multinomial-theorem
lemma exists by a guessed name; check before use.

### Classification

```yaml
tier: B
significance: 5
tractability: 5
tags:
  - geometry
  - euclidean-geometry
  - orthotope
  - british-flag-theorem
  - inclusion-exclusion
  - powerset
  - alternating-sum
  - finite-difference
domain: geometry
parent: british-flag-theorem-oq-01-oq-02
category: generalization
```

Notes on classification: the **vanishing law `k < n ⇒ A_k = 0`** and the **first defect
`A_n = n!·∏(αᵢ−βᵢ)`** are highly tractable — they reuse the parent's and sibling's existing
lemmas almost verbatim (tractability 5). The **general closed-form defect for `k > n`** is
harder (surjection/Stirling combinatorics) and can be deferred or stated as a further open
question; a shippable, verified entry needs only the vanishing law plus the first defect.

### Related Gallery Proofs

- **british-flag-theorem-oq-01-oq-02** (parent) — the orthotope squared-distance identity
  `A_1 ≡ 0` for `n ≥ 2`; supplies `vertex`, `sqDist`, `alt_sum_ite_eq_zero`,
  `real_alt_powerset_zero`. This problem is its `k`-th moment generalization.
- **british-flag-theorem-oq-01-oq-02-oq-01** (sibling) — fourth-moment defect for a *general
  parallelepiped* (`n ≥ 5` vanishing, explicit `n = 4` pairing-sum defect); supplies the reusable
  `monomial_term_zero` / `monomial_term_eval` finite-difference abstraction. This problem is the
  *orthogonal* (box) counterpart with the sharper `n ≥ k+1` threshold, for all `k`.
- **british-flag-theorem-oq-01-oq-01** — the 2-D non-orthogonal parallelogram defect `2⟨u,v⟩`;
  the `k = 1` skew case underlying the sibling's higher-degree generalization.
- **british-flag-theorem-oq-01** — the British Flag Theorem in ℝ²; the `n = 2, k = 1` slice.
