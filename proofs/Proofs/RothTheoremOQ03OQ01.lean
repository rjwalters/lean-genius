/-
  Roth Theorem OQ-03-OQ-01: Foundational Identities for the
  Gowers Norm and the k-AP Counting Operator

  The parent entry `RothTheoremOQ03` introduces, constructively, the two
  analytic operators at the heart of the density-increment / generalized
  von Neumann approach to Szemerédi's theorem:

    * the Gowers `U^s` uniformity norm
        ‖f‖_{U^s}^{2^s} = E_{x,h} ∏_{ω ∈ {0,1}^s} C^{|ω|} f(x + ω·h),
    * the k-AP counting operator
        Λ_k(f₀,…,f_{k-1}) = E_{x,d} ∏_{i} fᵢ(x + i·d).

  but records *no* algebraic properties of either.  This child proves the
  foundational degenerate / normalization identities that every later
  argument relies on, all fully machine-checked (0 axioms, no
  `native_decide`):

    * `conjugateByWeight_zero`     — the conjugation factor fixes `0`;
    * `gowersNorm_zero`            — ‖0‖_{U^s} = 0;
    * `kAPCount_const`             — Λ_k(c,…,c) = cᵏ;
    * `kAPCount_const_one`         — Λ_k(1,…,1) = 1 (total normalized mass);
    * `kAPCount_eq_zero_of_zero`   — a single zero slot annihilates Λ_k;
    * `kAPCount_diag_eq_sum_subsets` — the **generalized von Neumann telescoping**:
      `Λ_k(g,…,g) = ∑_{S⊆[k]} δ^{k−|S|}·Λ_k(i↦ if i∈S then g−δ·1 else 1)`, the full
      `2^k`-term multilinear expansion with the `δ^k` major term isolated at `S=∅`.
    * `kAPCount_diag_eq_major_add_remainder` — the same expansion with the `S=∅`
      summand evaluated: `Λ_k(g,…,g) = δ^k + ∑_{∅≠S⊆[k]} δ^{k−|S|}·Λ_k(…)`, the
      "main `k`-AP count `δ^k` plus a balanced (Gowers-controlled) remainder" form.

  These are precisely the checks that pin the operators down as genuine
  averages `E_{x,d} ∏ᵢ fᵢ(x+i·d)` (the `(N⁻¹)²·N² = 1` normalization),
  and the constant/zero base cases of the multilinear expansion
  `1_A = δ·1 + (1_A − δ)` that opens the generalized von Neumann argument.

  Self-contained: the operators are re-declared here in their own
  namespace using the current Mathlib norm `‖·‖` (rather than the parent's
  `Complex.abs`), so the file is robust to merge order and toolchain drift.

  References:
  - Gowers, "A new proof of Szemerédi's theorem" (2001)
  - Tao, "Higher order Fourier analysis" (2012)
-/

import Mathlib

namespace RothTheoremOQ03OQ01

open Finset BigOperators

-- ============================================================
-- The operators (constructive; norm via `‖·‖`)
-- ============================================================

/-- The shift determined by a hypercube vertex `ω` and shift vectors `h`:
    `ω · h = Σᵢ (if ωᵢ then hᵢ else 0)`. -/
noncomputable def hypercubeShift {N s : ℕ} (h : Fin s → ZMod N)
    (ω : Fin s → Bool) : ZMod N :=
  ∑ i : Fin s, if ω i then h i else 0

/-- Conjugation factor: conjugate exactly when the Hamming weight of `ω`
    is odd. `C^{|ω|}(z) = z` if `|ω|` even, `conj z` if `|ω|` odd. -/
noncomputable def conjugateByWeight {s : ℕ} (ω : Fin s → Bool) (z : ℂ) : ℂ :=
  if (Finset.univ.filter (fun i => ω i = true)).card % 2 = 0
  then z else starRingEnd ℂ z

/-- The Gowers `U^s` norm of `f : ZMod N → ℂ` (raised to the power `2^s`),
    `‖f‖_{U^s}^{2^s} = |E_{x,h} ∏_{ω} C^{|ω|} f(x + ω·h)|`, written as the
    modulus of a normalized finite sum. -/
noncomputable def gowersNorm (N s : ℕ) [NeZero N] (f : ZMod N → ℂ) : ℝ :=
  ‖(((N : ℂ)⁻¹) ^ (s + 1) *
      ∑ x : ZMod N, ∑ h : Fin s → ZMod N,
        ∏ ω : Fin s → Bool,
          conjugateByWeight ω (f (x + hypercubeShift h ω)))‖

/-- The k-AP counting operator, a normalized finite average:
    `Λ_k(f₀,…,f_{k-1}) = E_{x,d ∈ ZMod N} ∏_{i} fᵢ(x + i·d)`. -/
noncomputable def kAPCount {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) : ℂ :=
  ((N : ℂ)⁻¹) ^ 2 * ∑ x : ZMod N, ∑ d : ZMod N,
    ∏ i : Fin k, f i (x + i.val • d)

/-- The complex indicator `1_A : ZMod N → ℂ` of a finite set `A ⊆ ZMod N`:
    `1` on `A`, `0` off it.  Feeding `1_A` into every slot of `kAPCount`
    turns the analytic operator `Λ_k` into a genuine combinatorial count
    of arithmetic progressions lying inside `A`
    (`kAPCount_indicator_eq_count`). -/
noncomputable def indicatorZMod {N : ℕ} (A : Finset (ZMod N)) : ZMod N → ℂ :=
  fun x => if x ∈ A then 1 else 0

-- ============================================================
-- Foundational identities
-- ============================================================

/-- The conjugation-by-weight factor sends `0` to `0`: both branches
    (the identity and complex conjugation) fix the origin. -/
@[simp] theorem conjugateByWeight_zero {s : ℕ} (ω : Fin s → Bool) :
    conjugateByWeight ω 0 = 0 := by
  unfold conjugateByWeight
  split <;> simp

/-- The Gowers `U^s` norm of the zero function is `0`: every hypercube
    factor is `conjugateByWeight ω 0 = 0`, so each `2^s`-fold product
    vanishes, the averaging sum is `0`, and `‖0‖ = 0`. -/
theorem gowersNorm_zero (N s : ℕ) [NeZero N] :
    gowersNorm N s (0 : ZMod N → ℂ) = 0 := by
  unfold gowersNorm
  have hzero : ∀ (x : ZMod N) (h : Fin s → ZMod N),
      (∏ ω : Fin s → Bool,
        conjugateByWeight ω ((0 : ZMod N → ℂ) (x + hypercubeShift h ω))) = 0 :=
    fun x h => Finset.prod_eq_zero (Finset.mem_univ (default : Fin s → Bool))
      (by rw [Pi.zero_apply]; exact conjugateByWeight_zero _)
  rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun h _ => hzero x h))]
  simp

/-- The k-AP counting operator on the constant tuple `(c,…,c)` equals
    `c ^ k`: the inner product is `∏_{i} c = cᵏ`, and the normalized
    double average `(N⁻¹)² · ∑_{x,d} cᵏ = cᵏ` cancels the `N²` pairs
    against the `(N⁻¹)²` prefactor. -/
theorem kAPCount_const {N : ℕ} [NeZero N] (k : ℕ) (c : ℂ) :
    kAPCount k (fun (_ : Fin k) (_ : ZMod N) => c) = c ^ k := by
  unfold kAPCount
  have hprod : ∀ (x d : ZMod N),
      (∏ i : Fin k, (fun (_ : Fin k) (_ : ZMod N) => c) i (x + i.val • d))
        = c ^ k := by
    intro x d
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun d _ => hprod x d))]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [show ((N : ℂ)⁻¹) ^ 2 * ((N : ℂ) * ((N : ℂ) * c ^ k))
        = ((N : ℂ)⁻¹ * (N : ℂ)) ^ 2 * c ^ k from by ring,
      inv_mul_cancel₀ hN, one_pow, one_mul]

/-- Normalization: the count of the all-ones tuple is `1`, i.e.
    `Λ_k(1,…,1) = 1` — the total normalized `k`-AP mass and the base
    point of the `1_A = δ·1 + (1_A − δ)` decomposition. -/
theorem kAPCount_const_one {N : ℕ} [NeZero N] (k : ℕ) :
    kAPCount k (fun (_ : Fin k) (_ : ZMod N) => (1 : ℂ)) = 1 := by
  rw [kAPCount_const]; simp

/-- A single zero argument annihilates the whole count: if `f j` is the
    zero function for some position `j`, then `Λ_k(f₀,…,f_{k-1}) = 0`,
    because the `j`-th factor of every product term vanishes. -/
theorem kAPCount_eq_zero_of_zero {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (hj : f j = 0) :
    kAPCount k f = 0 := by
  unfold kAPCount
  have hprod : ∀ (x d : ZMod N), (∏ i : Fin k, f i (x + i.val • d)) = 0 :=
    fun x d => Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun d _ => hprod x d))]
  simp

-- ============================================================
-- Multilinearity in each slot
--
-- The k-AP counting operator is *multilinear*: linear separately in
-- each of its `k` function arguments.  These are exactly the identities
-- that drive the generalized von Neumann argument, where one slot is
-- expanded as `1_A = δ·1 + (1_A − δ)` and the count is split by linearity
-- in that slot.  We record linearity in an arbitrary slot `j` via
-- `Function.update`.
-- ============================================================

/-- Factor out the `j`-th slot of the inner product: replacing `f j` by an
    arbitrary function `g` (via `Function.update`) pulls the `j`-th factor
    `g (x + j·d)` out in front of the product over the remaining slots. -/
theorem prod_update_factor {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g : ZMod N → ℂ) (x d : ZMod N) :
    (∏ i : Fin k, Function.update f j g i (x + i.val • d))
      = g (x + j.val • d) *
          ∏ i ∈ Finset.univ.erase j, f i (x + i.val • d) := by
  rw [← Finset.mul_prod_erase Finset.univ
        (fun i => Function.update f j g i (x + i.val • d)) (Finset.mem_univ j)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [hi.1]

/-- Additivity in slot `j`: `Λ_k` is additive in each function argument.
    Splitting the `j`-th slot as a sum `g₁ + g₂` splits the whole count.
    This is the linear step that lets the generalized von Neumann argument
    decompose `1_A = δ·1 + (1_A − δ)` inside a single AP-count slot. -/
theorem kAPCount_update_add {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g₁ g₂ : ZMod N → ℂ) :
    kAPCount k (Function.update f j (g₁ + g₂))
      = kAPCount k (Function.update f j g₁)
        + kAPCount k (Function.update f j g₂) := by
  unfold kAPCount
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [prod_update_factor, prod_update_factor, prod_update_factor, Pi.add_apply]
  ring

/-- Scalar homogeneity in slot `j`: scaling one function argument by a
    constant `c` scales the whole count by `c`.  Together with
    `kAPCount_update_add` this establishes multilinearity of `Λ_k`. -/
theorem kAPCount_update_smul {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (c : ℂ) (g : ZMod N → ℂ) :
    kAPCount k (Function.update f j (c • g))
      = c * kAPCount k (Function.update f j g) := by
  unfold kAPCount
  have key : (∑ x : ZMod N, ∑ d : ZMod N,
                ∏ i : Fin k, Function.update f j (c • g) i (x + i.val • d))
      = c * ∑ x : ZMod N, ∑ d : ZMod N,
                ∏ i : Fin k, Function.update f j g i (x + i.val • d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [prod_update_factor, prod_update_factor, Pi.smul_apply, smul_eq_mul]
    ring
  rw [key]; ring

/-- A zero slot makes the whole count vanish, phrased via `Function.update`:
    overwriting slot `j` with the zero function gives `Λ_k = 0`.  The
    `Function.update`-flavoured companion of `kAPCount_eq_zero_of_zero`, and the
    additive unit for the slotwise linear structure. -/
@[simp] theorem kAPCount_update_zero {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) :
    kAPCount k (Function.update f j 0) = 0 :=
  kAPCount_eq_zero_of_zero k _ j (Function.update_self j 0 f)

/-- Subtractivity in slot `j`: `Λ_k` is additive under subtraction in each
    function argument.  Combined with `kAPCount_update_add`/`kAPCount_update_smul`
    this is the full linear structure the generalized von Neumann argument uses to
    telescope a slot expanded as `1_A = δ·1 + (1_A − δ)`. -/
theorem kAPCount_update_sub {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g₁ g₂ : ZMod N → ℂ) :
    kAPCount k (Function.update f j (g₁ - g₂))
      = kAPCount k (Function.update f j g₁)
        - kAPCount k (Function.update f j g₂) := by
  have h1 : g₁ - g₂ = g₁ + (-1 : ℂ) • g₂ := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h1, kAPCount_update_add, kAPCount_update_smul, neg_one_mul, ← sub_eq_add_neg]

/-- **The generalized von Neumann slot-split.**  For any scalar `δ`, expanding
    the `j`-th slot as `g = δ·1 + (g − δ·1)` splits the count into its *major
    term* `δ · Λ_k(…,1,…)` and a *balanced remainder* whose `j`-th slot
    `g − δ·1` has mean-zero flavour.  Taking `g = 1_A` and `δ = |A|/N` (the
    density) this is exactly the first step of the density-increment / von
    Neumann decomposition: the major term is the main `k`-AP count and the
    remainder is controlled by a Gowers uniformity norm. -/
theorem kAPCount_update_split {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) (j : Fin k) (g : ZMod N → ℂ) (δ : ℂ) :
    kAPCount k (Function.update f j g)
      = δ * kAPCount k (Function.update f j 1)
        + kAPCount k (Function.update f j (g - δ • (1 : ZMod N → ℂ))) := by
  have hadd := kAPCount_update_add k f j (δ • (1 : ZMod N → ℂ))
    (g - δ • (1 : ZMod N → ℂ))
  have hg : δ • (1 : ZMod N → ℂ) + (g - δ • (1 : ZMod N → ℂ)) = g := by
    rw [add_sub_cancel]
  rw [hg] at hadd
  rw [hadd, kAPCount_update_smul]

-- ============================================================
-- The generalized von Neumann telescoping
--
-- Iterating the one-slot split `kAPCount_update_split` across all `k` slots
-- expands the *diagonal* count `Λ_k(g,…,g)` into `2^k` subset-indexed terms.
-- Writing `g = δ·1 + b` with `b = g − δ·1`, the standard "product of sums"
-- identity `Finset.prod_add` at the level of the inner product `∏ᵢ g(x+i·d)`
-- expands it into a sum over subsets `S ⊆ {0,…,k−1}`, where `S` marks the
-- slots carrying the balanced part `b` and the complement carries `δ`.
-- ============================================================

/-- **Generalized von Neumann expansion (diagonal).**  Writing each slot of the
    diagonal count `Λ_k(g,…,g)` as `g = δ·1 + (g − δ·1)` and expanding
    multilinearly telescopes the count into `2^k` terms indexed by subsets
    `S ⊆ {0,…,k−1}` — `S` marks the slots carrying the *balanced* part
    `b = g − δ·1`, the complement carries the scalar `δ`:

        Λ_k(g,…,g) = ∑_{S ⊆ [k]} δ^{k−|S|} · Λ_k(i ↦ if i ∈ S then b else 1).

    The `S = ∅` term is the *major term* `δ^k · Λ_k(1,…,1) = δ^k`
    (`kAPCount_const_one`); every other term has at least one balanced slot `b`
    (mean-zero when `δ = |A|/N` and `g = 1_A`), which is exactly what the
    Gowers-uniformity control step then bounds.  This is the full slot
    telescoping that iterating `kAPCount_update_split` produces, obtained here in
    one shot from `Finset.prod_add` on the inner AP product. -/
theorem kAPCount_diag_eq_sum_subsets {N : ℕ} [NeZero N] (k : ℕ)
    (g : ZMod N → ℂ) (δ : ℂ) :
    kAPCount k (fun _ : Fin k => g)
      = ∑ S : Finset (Fin k),
          δ ^ (k - S.card) *
            kAPCount k (fun i => if i ∈ S then (g - δ • (1 : ZMod N → ℂ)) else 1) := by
  classical
  set b : ZMod N → ℂ := g - δ • (1 : ZMod N → ℂ) with hb
  -- Pointwise decomposition `g y = b y + δ`.
  have hg : ∀ y : ZMod N, g y = b y + δ := by
    intro y
    simp only [hb, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    ring
  -- In each RHS term only the balanced slots `i ∈ S` survive the inner product.
  have hRinner : ∀ (S : Finset (Fin k)) (x d : ZMod N),
      (∏ i : Fin k, (if i ∈ S then b else (1 : ZMod N → ℂ)) (x + i.val • d))
        = ∏ i ∈ S, b (x + i.val • d) := by
    intro S x d
    have happ : ∀ i : Fin k,
        (if i ∈ S then b else (1 : ZMod N → ℂ)) (x + i.val • d)
          = if i ∈ S then b (x + i.val • d) else 1 := by
      intro i; split <;> simp
    rw [Finset.prod_congr rfl (fun i _ => happ i), Finset.prod_ite_mem, Finset.univ_inter]
  -- `Finset.prod_add` expands the diagonal inner product into the subset sum.
  have hLinner : ∀ (x d : ZMod N),
      (∏ i : Fin k, g (x + i.val • d))
        = ∑ S : Finset (Fin k), δ ^ (k - S.card) * ∏ i ∈ S, b (x + i.val • d) := by
    intro x d
    rw [Finset.prod_congr rfl (fun i _ => hg (x + i.val • d)), Finset.prod_add,
        Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ S),
        Finset.card_univ, Fintype.card_fin]
    ring
  -- Both sides equal the canonical triple sum.
  have hL : kAPCount k (fun _ : Fin k => g)
      = ((N : ℂ)⁻¹) ^ 2 * ∑ x : ZMod N, ∑ d : ZMod N,
          ∑ S : Finset (Fin k), δ ^ (k - S.card) * ∏ i ∈ S, b (x + i.val • d) := by
    unfold kAPCount
    congr 1
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro d _
    exact hLinner x d
  have hR : (∑ S : Finset (Fin k), δ ^ (k - S.card) *
        kAPCount k (fun i => if i ∈ S then b else (1 : ZMod N → ℂ)))
      = ((N : ℂ)⁻¹) ^ 2 * ∑ x : ZMod N, ∑ d : ZMod N,
          ∑ S : Finset (Fin k), δ ^ (k - S.card) * ∏ i ∈ S, b (x + i.val • d) := by
    unfold kAPCount
    -- Simplify each summand: rewrite its inner product and hoist the scalars.
    have step : ∀ S : Finset (Fin k),
        δ ^ (k - S.card) * (((N : ℂ)⁻¹) ^ 2 * ∑ x : ZMod N, ∑ d : ZMod N,
            ∏ i : Fin k, (if i ∈ S then b else (1 : ZMod N → ℂ)) (x + i.val • d))
          = ((N : ℂ)⁻¹) ^ 2 * ∑ x : ZMod N, ∑ d : ZMod N,
              δ ^ (k - S.card) * ∏ i ∈ S, b (x + i.val • d) := by
      intro S
      rw [Finset.sum_congr rfl (fun x _ =>
            Finset.sum_congr rfl (fun d _ => hRinner S x d))]
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun S _ => step S), ← Finset.mul_sum]
    congr 1
    -- Reorder `∑ S ∑ x ∑ d` into `∑ x ∑ d ∑ S`.
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_comm]
  rw [hL, hR]

/-- **Major term + balanced remainder.**  Separating the `S = ∅` summand of the von
    Neumann expansion `kAPCount_diag_eq_sum_subsets` isolates the *major term* `δ^k`
    from the *balanced remainder*.  The `S = ∅` term carries the scalar `δ` in every
    slot, so it equals `δ^k · Λ_k(1,…,1) = δ^k` (`kAPCount_const_one`); every remaining
    term is indexed by a *nonempty* `S`, hence has at least one mean-zero slot
    `b = g − δ·1`.  With `g = 1_A` and `δ = |A|/N` this is exactly the
    "main `k`-AP count plus a Gowers-controlled error" split that the density-increment
    argument feeds into the generalized von Neumann inequality:

        Λ_k(g,…,g) = δ^k + ∑_{∅ ≠ S ⊆ [k]} δ^{k−|S|} · Λ_k(i ↦ if i ∈ S then b else 1). -/
theorem kAPCount_diag_eq_major_add_remainder {N : ℕ} [NeZero N] (k : ℕ)
    (g : ZMod N → ℂ) (δ : ℂ) :
    kAPCount k (fun _ : Fin k => g)
      = δ ^ k
        + ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin k))),
            δ ^ (k - S.card) *
              kAPCount k (fun i => if i ∈ S then (g - δ • (1 : ZMod N → ℂ)) else 1) := by
  classical
  rw [kAPCount_diag_eq_sum_subsets k g δ,
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (∅ : Finset (Fin k)))]
  congr 1
  -- The `S = ∅` term collapses to `δ ^ k`: no balanced slots, so all slots carry `1`.
  have hfun : (fun i => if i ∈ (∅ : Finset (Fin k)) then (g - δ • (1 : ZMod N → ℂ))
        else (1 : ZMod N → ℂ)) = (fun (_ : Fin k) (_ : ZMod N) => (1 : ℂ)) := by
    funext i y; simp
  rw [Finset.card_empty, Nat.sub_zero, hfun, kAPCount_const_one, mul_one]

-- ============================================================
-- Bridge to combinatorics: `kAPCount` of an indicator counts APs
--
-- All the identities above are analytic facts about the *operator*
-- `Λ_k`.  This block ties `Λ_k` back to the combinatorial object it is
-- designed to measure: feeding the indicator `1_A` into every slot,
-- `Λ_k(1_A,…,1_A)` becomes exactly `(N⁻¹)²` times the number of pairs
-- `(x,d)` whose length-`k` progression `x, x+d, …, x+(k−1)d` lies wholly
-- inside `A`.  This is the concrete meaning of "the normalized `k`-AP
-- count of `A`" that Roth's theorem (`k = 3`) is a statement about.
-- ============================================================

/-- The indicator of the whole group is the constant `1` function. -/
@[simp] theorem indicatorZMod_univ {N : ℕ} [NeZero N] :
    indicatorZMod (Finset.univ : Finset (ZMod N)) = fun _ => (1 : ℂ) := by
  funext x
  simp [indicatorZMod]

/-- **Combinatorial bridge.**  The analytic count of the diagonal indicator
    tuple is `(N⁻¹)²` times the number of `(x, d)` pairs for which the entire
    length-`k` progression `x + i·d` (`0 ≤ i < k`) lies inside `A`:

        Λ_k(1_A,…,1_A) = (N⁻¹)² · #{(x,d) : ∀ i, x + i·d ∈ A}.

    Each inner product `∏ᵢ 1_A(x + i·d)` is `1` exactly when every term of the
    progression hits `A` and `0` otherwise (`Finset.prod_boole`); summing these
    indicators over all pairs `(x,d)` counts the progressions (`Finset.sum_boole`).
    This is what makes `kAPCount` the *normalized `k`-AP density* of `A`: the
    quantity Roth's theorem forces to be positive once `A` is dense. -/
theorem kAPCount_indicator_eq_count {N : ℕ} [NeZero N] (k : ℕ)
    (A : Finset (ZMod N)) :
    kAPCount k (fun _ : Fin k => indicatorZMod A)
      = ((N : ℂ)⁻¹) ^ 2 *
          ((Finset.univ.filter
              (fun p : ZMod N × ZMod N =>
                ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card : ℂ) := by
  classical
  simp only [kAPCount, indicatorZMod]
  congr 1
  -- Collapse the double sum into a single sum over pairs.
  rw [← Finset.sum_product', Finset.univ_product_univ]
  -- Each inner product of indicators is the indicator of "all terms hit `A`"
  -- (`prod_boole`); summing those indicators over all pairs counts the
  -- progressions lying inside `A` (`sum_boole`), and `∀ i ∈ univ` collapses to
  -- the plain `∀ i` on the counted set.
  simp [Finset.prod_boole, Finset.sum_boole]

/-- Consistency check: the normalized `k`-AP count of the whole group is `1`,
    recovering `kAPCount_const_one` through the combinatorial definition
    (every pair `(x,d)` gives a progression inside `univ`). -/
theorem kAPCount_indicator_univ {N : ℕ} [NeZero N] (k : ℕ) :
    kAPCount k (fun _ : Fin k => indicatorZMod (Finset.univ : Finset (ZMod N)))
      = 1 := by
  simp only [indicatorZMod_univ]
  exact kAPCount_const_one k

end RothTheoremOQ03OQ01
