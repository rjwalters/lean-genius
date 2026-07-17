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
    * `kAPCount_count_split` / `kAPCount_indicator_eq_diag_add_nondeg` — the
      diagonal / nondegenerate split of the combinatorial `k`-AP count (`k ≥ 1`):
      `#{(x,d) : ∀ i, x+i·d ∈ A} = #A + #{(x,d) : d ≠ 0 ∧ …}`, giving
      `Λ_k(1_A) = (N⁻¹)²·(#A + #nondegenerate)` — the trivial diagonal term
      separated from the genuine `d ≠ 0` count Roth's theorem controls.
    * `kAPCount_count_length_antitone` / `kAPCount_nondeg_length_antitone` — **length
      monotonicity**: the (nondegenerate) `k`-AP count is antitone in the progression
      length `k`, since demanding more terms `x + i·d ∈ A` only shrinks the counted set
      (restrict a witness along `Fin.castLE`).

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

/-- **Conjugation symmetry of the k-AP count.**  Complex-conjugating every function
    argument conjugates the count: `conj (Λ_k(f₀,…,f_{k-1})) = Λ_k(conj f₀,…,conj f_{k-1})`.
    The complex conjugation `starRingEnd ℂ` is a ring homomorphism, so it distributes over
    the finite double sum and the length-`k` product; the real prefactor `(N⁻¹)²` is fixed
    (`N` is a natural-number cast).  Conjugation is the operation at the heart of the Gowers
    `U^{k-1}` norm (`gowersNorm`, via `conjugateByWeight`), so this symmetry is a basic
    building block of the generalized von Neumann argument. -/
theorem kAPCount_conj {N : ℕ} [NeZero N] (k : ℕ) (f : Fin k → ZMod N → ℂ) :
    starRingEnd ℂ (kAPCount k f) = kAPCount k (fun i x => starRingEnd ℂ (f i x)) := by
  unfold kAPCount
  rw [map_mul, map_pow, map_inv₀, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_prod]

/-- **The combinatorial k-AP count is real (self-conjugate).**  Feeding the real-valued
    indicator `1_A` into every slot gives a self-conjugate value: `conj (Λ_k(1_A,…,1_A)) =
    Λ_k(1_A,…,1_A)`.  Immediate from `kAPCount_conj` together with `conj (1_A x) = 1_A x`
    (the indicator takes only the real values `0, 1`).  Consistent with
    `kAPCount_indicator_eq_count`, which exhibits the same value as `(N⁻¹)²` times a natural
    number. -/
theorem kAPCount_indicator_conj {N : ℕ} [NeZero N] (k : ℕ) (A : Finset (ZMod N)) :
    starRingEnd ℂ (kAPCount k (fun _ => indicatorZMod A))
      = kAPCount k (fun _ => indicatorZMod A) := by
  rw [kAPCount_conj]
  congr 1
  funext i x
  unfold indicatorZMod
  split <;> simp

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

/-- **Diagonal / nondegenerate split of the `k`-AP count.**  For `k ≥ 1`, the pairs
    `(x, d)` whose length-`k` progression `x + i·d` lies entirely in `A` split into the
    *diagonal* `d = 0` (a constant progression `x, x, …, x`, which lies in `A` iff `x ∈ A`,
    contributing exactly `#A` pairs) and the *nondegenerate* `d ≠ 0` progressions:

        #{(x,d) : ∀ i, x + i·d ∈ A}
          = #A  +  #{(x,d) : d ≠ 0 ∧ ∀ i, x + i·d ∈ A}.

    This is the standard first step separating the trivial diagonal term from the genuine
    (`d ≠ 0`) `k`-AP count that Roth's theorem controls. -/
theorem kAPCount_count_split {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card
      = A.card
        + (Finset.univ.filter (fun p : ZMod N × ZMod N =>
             (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card := by
  classical
  set P := Finset.univ.filter (fun p : ZMod N × ZMod N =>
      ∀ i : Fin k, p.1 + i.val • p.2 ∈ A) with hP
  -- Partition `P` according to whether the common difference `d = p.2` vanishes.
  have hsplit :
      (P.filter (fun p => p.2 = 0)).card + (P.filter (fun p => ¬ p.2 = 0)).card = P.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (fun p : ZMod N × ZMod N => p.2 = 0)
  -- The diagonal slice `d = 0` is exactly `A ×ˢ {0}`.
  have hdiag : P.filter (fun p => p.2 = 0) = A ×ˢ ({0} : Finset (ZMod N)) := by
    ext p
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hall, h0⟩
      simp only [h0, smul_zero, add_zero] at hall
      exact ⟨hall ⟨0, hk⟩, h0⟩
    · rintro ⟨hA, h0⟩
      refine ⟨?_, h0⟩
      intro i
      simp only [h0, smul_zero, add_zero]
      exact hA
  have hdiagcard : (P.filter (fun p => p.2 = 0)).card = A.card := by
    rw [hdiag, Finset.card_product, Finset.card_singleton, mul_one]
  -- The `d ≠ 0` slice unfolds to the nondegenerate filter.
  have hnondeg : P.filter (fun p => ¬ p.2 = 0)
      = Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0) := by
    rw [hP, Finset.filter_filter]
  rw [hnondeg, hdiagcard] at hsplit
  omega

/-- **Analytic form of the diagonal / nondegenerate split.**  Combining the combinatorial
    bridge `kAPCount_indicator_eq_count` with `kAPCount_count_split`, the analytic `k`-AP
    operator on the indicator of `A` decomposes (for `k ≥ 1`) into its lower-order diagonal
    term `(N⁻¹)²·#A` and the normalized count of nondegenerate (`d ≠ 0`) progressions:

        Λ_k(1_A,…,1_A) = (N⁻¹)² · (#A + #{(x,d) : d ≠ 0 ∧ ∀ i, x + i·d ∈ A}).

    The diagonal term `(N⁻¹)²·#A = δ/N` (with density `δ = #A/N`) vanishes as `N → ∞`,
    so the content of `Λ_k(1_A)` lives in the nondegenerate count — the quantity Roth's
    theorem (`k = 3`) forces to be positive for dense `A`. -/
theorem kAPCount_indicator_eq_diag_add_nondeg {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    kAPCount k (fun _ : Fin k => indicatorZMod A)
      = ((N : ℂ)⁻¹) ^ 2 *
          ((A.card : ℂ) +
            ((Finset.univ.filter (fun p : ZMod N × ZMod N =>
                (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card : ℂ)) := by
  rw [kAPCount_indicator_eq_count, kAPCount_count_split hk]
  push_cast
  ring

/-- Consistency check: the normalized `k`-AP count of the whole group is `1`,
    recovering `kAPCount_const_one` through the combinatorial definition
    (every pair `(x,d)` gives a progression inside `univ`). -/
theorem kAPCount_indicator_univ {N : ℕ} [NeZero N] (k : ℕ) :
    kAPCount k (fun _ : Fin k => indicatorZMod (Finset.univ : Finset (ZMod N)))
      = 1 := by
  simp only [indicatorZMod_univ]
  exact kAPCount_const_one k

/-- **Every counted progression starts in `A`.**  For `k ≥ 1`, a pair `(x, d)` whose
    length-`k` progression lies entirely in `A` has, in particular, its `i = 0` term
    `x + 0·d = x` in `A`.  Hence the counted set embeds in `A ×ˢ univ`. -/
theorem kAPCount_count_start_subset {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A))
      ⊆ A ×ˢ Finset.univ := by
  classical
  intro p hp
  rw [Finset.mem_filter] at hp
  have hx : p.1 ∈ A := by simpa using hp.2 ⟨0, hk⟩
  exact Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩

/-- **Trivial upper bound on the `k`-AP count.**  Since every counted progression starts in
    `A` (`kAPCount_count_start_subset`), the number of pairs `(x, d)` with `x + i·d ∈ A` for
    all `i` is at most `#A · N`.  This is the loose companion to the diagonal/nondegenerate
    split `kAPCount_count_split`: the total count never exceeds `#A` starting points times the
    `N` available common differences. -/
theorem kAPCount_count_le {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card ≤ A.card * N := by
  classical
  calc
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card
        ≤ (A ×ˢ Finset.univ).card :=
          Finset.card_le_card (kAPCount_count_start_subset hk A)
    _ = A.card * Fintype.card (ZMod N) := by
          rw [Finset.card_product, Finset.card_univ]
    _ = A.card * N := by rw [ZMod.card]

/-- **Upper bound on the nondegenerate `k`-AP count.**  The `d ≠ 0` progressions counted in
    `kAPCount_count_split` embed in `A ×ˢ (univ \ {0})` — they start in `A` and have a nonzero
    common difference — so their number is at most `#A · (N − 1)`.  Together with
    `kAPCount_count_split` this brackets the genuine (nondiagonal) `k`-AP count between `0` and
    `#A · (N − 1)`. -/
theorem kAPCount_nondeg_le {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card
      ≤ A.card * (N - 1) := by
  classical
  have hsub :
      (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0))
        ⊆ A ×ˢ (Finset.univ.erase 0) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hall, hd⟩ := hp
    have hx : p.1 ∈ A := by simpa using hall ⟨0, hk⟩
    exact Finset.mem_product.mpr ⟨hx, Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩⟩
  calc
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card
        ≤ (A ×ˢ (Finset.univ.erase 0)).card := Finset.card_le_card hsub
    _ = A.card * (Finset.univ.erase (0 : ZMod N)).card := by rw [Finset.card_product]
    _ = A.card * (N - 1) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-- **Monotonicity of the `k`-AP count in the set.**  Enlarging `A` can only add
    progressions: if `A ⊆ B` then every pair `(x, d)` whose length-`k` progression lies
    in `A` also has it in `B`, so the counted set for `A` embeds in that for `B`.  This is
    the basic structural fact behind density-increment arguments — the `k`-AP count is a
    monotone functional of the underlying set. -/
theorem kAPCount_count_mono {N : ℕ} [NeZero N] {k : ℕ} {A B : Finset (ZMod N)}
    (hAB : A ⊆ B) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card
      ≤ (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          ∀ i : Fin k, p.1 + i.val • p.2 ∈ B)).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, fun i => hAB (hp.2 i)⟩

/-- **Monotonicity of the nondegenerate `k`-AP count in the set.**  The `A ⊆ B` version of
    `kAPCount_count_mono` restricted to nonzero common difference `d ≠ 0`: the genuine
    (nondiagonal) `k`-AP count controlled by Roth's theorem is likewise monotone in the set,
    since enlarging `A` preserves both the "all terms in the set" and the `d ≠ 0`
    conditions. -/
theorem kAPCount_nondeg_mono {N : ℕ} [NeZero N] {k : ℕ} {A B : Finset (ZMod N)}
    (hAB : A ⊆ B) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card
      ≤ (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ B) ∧ p.2 ≠ 0)).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, ⟨fun i => hAB (hp.2.1 i), hp.2.2⟩⟩

/-- **Lower bound on the `k`-AP count.**  The diagonal `d = 0` already contributes exactly
    `#A` constant progressions (`kAPCount_count_split`), so the total number of length-`k`
    progressions inside `A` is at least `#A`.  This is the missing lower companion to the
    trivial upper bound `kAPCount_count_le`. -/
theorem kAPCount_count_ge {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    A.card ≤ (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card := by
  rw [kAPCount_count_split hk]
  exact Nat.le_add_right _ _

/-- **Two-sided bracket on the `k`-AP count.**  Combining the diagonal lower bound
    `kAPCount_count_ge` with the trivial upper bound `kAPCount_count_le` pins the count between
    the diagonal contribution and `#A` starting points times the `N` available differences:

        #A ≤ #{(x,d) : ∀ i, x + i·d ∈ A} ≤ #A · N. -/
theorem kAPCount_count_bracket {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    A.card ≤ (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card ∧
      (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card ≤ A.card * N :=
  ⟨kAPCount_count_ge hk A, kAPCount_count_le hk A⟩

/-- **Positivity of the `k`-AP count for nonempty `A`.**  A nonempty set contains at least one
    constant (diagonal) progression, so its `k`-AP count is strictly positive — immediate from
    `kAPCount_count_ge` and `Finset.card_pos`. -/
theorem kAPCount_count_pos {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    {A : Finset (ZMod N)} (hA : A.Nonempty) :
    0 < (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card :=
  lt_of_lt_of_le (Finset.card_pos.mpr hA) (kAPCount_count_ge hk A)

/-- **Positivity characterizes nonemptiness.**  For `k ≥ 1`, the `k`-AP count of `A` is
    strictly positive iff `A` is nonempty: a nonempty set supplies its diagonal (constant)
    progressions (`kAPCount_count_pos`), and conversely any counted progression contains its
    `i = 0` starting term `x` in `A`.  The biconditional packaging of `kAPCount_count_pos`,
    which pins down exactly when Roth's positivity hypothesis is even meaningful. -/
theorem kAPCount_count_pos_iff {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    {A : Finset (ZMod N)} :
    0 < (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card ↔ A.Nonempty := by
  classical
  refine ⟨fun hpos => ?_, fun hA => kAPCount_count_pos hk hA⟩
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hp
  exact ⟨p.1, by simpa using hp.2 ⟨0, hk⟩⟩

/-- **Vanishing characterizes emptiness.**  For `k ≥ 1`, the `k`-AP count of `A` is `0` iff
    `A` is empty: a nonempty set always supplies its diagonal (constant) progressions, so the
    only way the count can vanish is `A = ∅`.  The vanishing (`δ = 0`) companion of the
    positivity characterization `kAPCount_count_pos_iff`, and the "iff" strengthening of the
    empty-set base case `kAPCount_count_empty`. -/
theorem kAPCount_count_eq_zero_iff {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    {A : Finset (ZMod N)} :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card = 0 ↔ A = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty, ← kAPCount_count_pos_iff hk]
  omega

/-- **Exact count for the whole group.**  Every pair `(x, d)` has its length-`k` progression
    inside `univ`, so the `k`-AP count of the full group is exactly `N²` — the combinatorial
    companion of the normalized identity `kAPCount_indicator_univ`
    (`Λ_k(1_univ) = 1 = (N⁻¹)²·N²`), and the saturation case `A = univ` of the trivial upper
    bound `kAPCount_count_le` (`#univ · N = N · N`). -/
theorem kAPCount_count_univ {N : ℕ} [NeZero N] (k : ℕ) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ (Finset.univ : Finset (ZMod N)))).card = N ^ 2 := by
  classical
  rw [Finset.filter_true_of_mem (fun p _ i => Finset.mem_univ _),
      Finset.card_univ, Fintype.card_prod, ZMod.card]
  ring

-- ============================================================
-- Empty-set base case
--
-- The degenerate companion of the `A = univ` saturation block: the empty
-- set carries no `k`-AP mass at all.  Its indicator is the zero function
-- (`indicatorZMod_empty`), so — for `k ≥ 1`, where the `i = 0` term forces
-- the starting point into `A` — both the combinatorial count and the
-- analytic operator `Λ_k` vanish.  This is the `δ = 0` end of the density
-- scale, opposite the `Λ_k(1_univ) = 1` normalization.
-- ============================================================

/-- The indicator of the empty set is the zero function: `1_∅ = 0`.  The
    degenerate companion of `indicatorZMod_univ` (`1_univ = 1`), feeding the
    additive/multiplicative base points of the `1_A = δ·1 + (1_A − δ)`
    decomposition. -/
@[simp] theorem indicatorZMod_empty {N : ℕ} :
    indicatorZMod (∅ : Finset (ZMod N)) = fun _ => (0 : ℂ) := by
  funext x
  simp [indicatorZMod]

/-- **The empty set carries no `k`-AP mass.**  For `k ≥ 1`, no pair `(x, d)` has its
    length-`k` progression inside `∅` — the `i = 0` term `x` would have to lie in `∅` —
    so the count is `0`.  Immediate from the trivial upper bound `kAPCount_count_le`
    (`≤ #∅ · N = 0`), and the `A = ∅` degenerate case of the exact univ count
    `kAPCount_count_univ`. -/
theorem kAPCount_count_empty {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ (∅ : Finset (ZMod N)))).card = 0 := by
  simpa using kAPCount_count_le hk (∅ : Finset (ZMod N))

/-- **`Λ_k(1_∅) = 0`.**  For `k ≥ 1`, the analytic `k`-AP operator on the empty
    indicator vanishes: `1_∅ = 0` (`indicatorZMod_empty`) is the zero function, and a
    single zero slot annihilates the count (`kAPCount_eq_zero_of_zero`).  The degenerate
    companion of `kAPCount_indicator_univ` (`Λ_k(1_univ) = 1`), and the analytic shadow of
    the combinatorial `kAPCount_count_empty`. -/
theorem kAPCount_indicator_empty {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k) :
    kAPCount k (fun _ : Fin k => indicatorZMod (∅ : Finset (ZMod N))) = 0 := by
  refine kAPCount_eq_zero_of_zero k _ ⟨0, hk⟩ ?_
  funext x
  simp [indicatorZMod]

-- ============================================================
-- Nondegenerate-count boundary values
--
-- `kAPCount_count_empty` / `kAPCount_count_univ` pin the *total* `k`-AP count at
-- the two ends of the density scale (`0` and `N²`). The genuine content of Roth's
-- theorem, however, lives in the *nondegenerate* (`d ≠ 0`) count split off by
-- `kAPCount_count_split`. The two lemmas below pin that nondegenerate count at the
-- same two ends: it vanishes for `A = ∅` and saturates at `N·(N − 1) = N² − N` for
-- `A = univ` (every ordered pair `(x, d)` with `d ≠ 0`).
-- ============================================================

/-- **No nondegenerate progressions in the empty set.**  For `k ≥ 1`, no pair `(x, d)`
    with `d ≠ 0` has its length-`k` progression inside `∅`, so the nondegenerate count is
    `0`.  Immediate from the nondegenerate upper bound `kAPCount_nondeg_le`
    (`≤ #∅ · (N − 1) = 0`); the `d ≠ 0` companion of `kAPCount_count_empty`. -/
theorem kAPCount_nondeg_empty {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ (∅ : Finset (ZMod N))) ∧ p.2 ≠ 0)).card = 0 := by
  simpa using kAPCount_nondeg_le hk (∅ : Finset (ZMod N))

/-- **Every nonzero difference gives a nondegenerate progression in the whole group.**
    For `k ≥ 1`, the nondegenerate (`d ≠ 0`) `k`-AP count of `univ` is exactly
    `N·(N − 1) = N² − N`: every one of the `N²` pairs `(x, d)` lies inside `univ`, and
    removing the `N` diagonal pairs with `d = 0` leaves the nonzero-difference count.
    This saturates the `kAPCount_nondeg_le` bound (`≤ #univ · (N − 1) = N·(N − 1)`) and is
    the `A = univ` companion of `kAPCount_count_univ`.  Obtained from the diagonal split
    `kAPCount_count_split` at `A = univ` together with `kAPCount_count_univ`. -/
theorem kAPCount_nondeg_univ {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ (Finset.univ : Finset (ZMod N))) ∧ p.2 ≠ 0)).card
      = N ^ 2 - N := by
  have hsplit := kAPCount_count_split hk (Finset.univ : Finset (ZMod N))
  rw [kAPCount_count_univ, Finset.card_univ, ZMod.card] at hsplit
  omega

/-- **A singleton carries no nondegenerate progression.**  For `k ≥ 2` the nondegenerate
    (`d ≠ 0`) `k`-AP count of a one-point set `{a}` is `0`: the `i = 0` term forces the start
    `x = a`, and then the `i = 1` term forces `a + d = a`, i.e. `d = 0`, contradicting `d ≠ 0`.

    This is the sharp qualitative contrast between the nondegenerate count and the *total*
    count: the total count vanishes **iff** the set is empty (`kAPCount_count_eq_zero_iff`),
    whereas the nondegenerate count already vanishes on the nonempty singleton.  It is exactly
    this failure of "nonempty ⟹ nondegenerate progression" that makes Roth's theorem a genuine
    theorem rather than the trivial diagonal count — the nondegenerate mass only appears once
    the set is large enough, and pinning down *how* large is the content of the problem. -/
theorem kAPCount_nondeg_singleton {N : ℕ} [NeZero N] {k : ℕ} (hk : 2 ≤ k)
    (a : ZMod N) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ ({a} : Finset (ZMod N))) ∧ p.2 ≠ 0)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p -
  rintro ⟨hall, hd⟩
  -- `i = 0` term: the start is `a`
  have h0 : p.1 = a := by simpa using hall ⟨0, by omega⟩
  -- `i = 1` term (needs `k ≥ 2`): `a + d = a`, forcing `d = 0`
  have h1 : p.1 + p.2 = a := by simpa using hall ⟨1, by omega⟩
  refine hd (add_left_cancel (a := a) ?_)
  rw [h0] at h1
  rw [add_zero]
  exact h1

/-- **Exact total `k`-AP count of a singleton.**  For `k ≥ 2` the singleton `{a}` supports
    exactly one length-`k` progression lying inside it: the constant diagonal `x = a, d = 0`.
    Its diagonal contribution is `#{a} = 1` (`kAPCount_count_split`) and its nondegenerate
    contribution is `0` (`kAPCount_nondeg_singleton`), so the total count is `1`.  Together
    with the empty (`0`) and univ (`N²`) counts this pins the third natural boundary value of
    the total `k`-AP count. -/
theorem kAPCount_count_singleton {N : ℕ} [NeZero N] {k : ℕ} (hk : 2 ≤ k) (a : ZMod N) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ ({a} : Finset (ZMod N)))).card = 1 := by
  rw [kAPCount_count_split (show 0 < k by omega) ({a} : Finset (ZMod N)),
      kAPCount_nondeg_singleton hk a]
  simp

/-- **`Λ_k(1_{a}) = (N⁻¹)²`.**  For `k ≥ 2` the analytic `k`-AP operator on a singleton
    indicator equals `(N⁻¹)²`: the only counted progression is the constant diagonal
    (`kAPCount_count_singleton` gives count `1`), so the combinatorial bridge
    `kAPCount_indicator_eq_count` yields `(N⁻¹)²·1`.  This is the singleton value on the
    density scale between `Λ_k(1_∅) = 0` and `Λ_k(1_univ) = 1`. -/
theorem kAPCount_indicator_singleton {N : ℕ} [NeZero N] {k : ℕ} (hk : 2 ≤ k) (a : ZMod N) :
    kAPCount k (fun _ : Fin k => indicatorZMod ({a} : Finset (ZMod N)))
      = ((N : ℂ)⁻¹) ^ 2 := by
  rw [kAPCount_indicator_eq_count, kAPCount_count_singleton hk]
  simp

/-- **Global upper bound on the `k`-AP count.**  Since every set embeds in `univ` and the
    `k`-AP count is monotone (`kAPCount_count_mono`), the count for any `A` is at most the
    count for `univ`, which is exactly `N²` (`kAPCount_count_univ`).  The uniform (`A`-free)
    ceiling refining the set-dependent bound `kAPCount_count_le` (`≤ #A·N`). -/
theorem kAPCount_count_le_sq {N : ℕ} [NeZero N] (k : ℕ) (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card ≤ N ^ 2 := by
  calc
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card
        ≤ (Finset.univ.filter (fun p : ZMod N × ZMod N =>
            ∀ i : Fin k, p.1 + i.val • p.2 ∈ (Finset.univ : Finset (ZMod N)))).card :=
          kAPCount_count_mono (Finset.subset_univ A)
    _ = N ^ 2 := kAPCount_count_univ k

/-- **Global upper bound on the nondegenerate `k`-AP count.**  The `d ≠ 0` count is monotone
    (`kAPCount_nondeg_mono`) and saturates at `univ`, where it equals `N² − N`
    (`kAPCount_nondeg_univ`).  Hence the nondegenerate count of any `A` is at most `N² − N`,
    the uniform ceiling refining the set-dependent `kAPCount_nondeg_le` (`≤ #A·(N−1)`). -/
theorem kAPCount_nondeg_le_sq {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k) (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card ≤ N ^ 2 - N := by
  calc
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card
        ≤ (Finset.univ.filter (fun p : ZMod N × ZMod N =>
            (∀ i : Fin k, p.1 + i.val • p.2 ∈ (Finset.univ : Finset (ZMod N))) ∧ p.2 ≠ 0)).card :=
          kAPCount_nondeg_mono (Finset.subset_univ A)
    _ = N ^ 2 - N := kAPCount_nondeg_univ hk

/-- **Longer progressions are rarer: the `k`-AP count is antitone in the length `k`.**  For
    `k ≤ k'`, requiring all `k'` terms `x + i·d` (`i < k'`) to lie in `A` is a stronger
    constraint than requiring only the first `k` of them, so the `k'`-progression pairs `(x, d)`
    form a subset of the `k`-progression pairs (restrict a witness along `Fin.castLE`).  Hence
    the count can only decrease as the progression length grows.  Note the `k = 1` case recovers
    the loose bound `kAPCount_count_le` (`≤ #A·N`) since the length-`1` count is exactly `#A·N`,
    and combined with `kAPCount_count_univ` it re-proves `kAPCount_count_le_sq`. -/
theorem kAPCount_count_length_antitone {N : ℕ} [NeZero N] {k k' : ℕ} (hkk : k ≤ k')
    (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k', p.1 + i.val • p.2 ∈ A)).card
      ≤ (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card := by
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, fun i => hp.2 (Fin.castLE hkk i)⟩

/-- **The nondegenerate (`d ≠ 0`) `k`-AP count is antitone in the length `k`.**  The length
    monotonicity of `kAPCount_count_length_antitone` survives the extra `d ≠ 0` restriction:
    for `k ≤ k'`, every nondegenerate `k'`-progression pair restricts to a nondegenerate
    `k`-progression pair (same `d ≠ 0`, fewer membership constraints), so the nondegenerate
    count decreases with progression length. -/
theorem kAPCount_nondeg_length_antitone {N : ℕ} [NeZero N] {k k' : ℕ} (hkk : k ≤ k')
    (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k', p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card
      ≤ (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card := by
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, ⟨fun i => hp.2.1 (Fin.castLE hkk i), hp.2.2⟩⟩

/-- **Translation invariance of the `k`-AP count.**  Translating `A` by any `t` leaves the
    number of length-`k` progressions unchanged: the map `(x, d) ↦ (x + t, d)` bijects the
    progressions of `A` with those of `A + t` (it fixes the common difference `d` and shifts
    the start).  The `k`-AP count is thus a *translation-invariant* functional of the set — the
    companion symmetry to `kAPCount_count_mono`, and the reason Roth's problem may fix a
    normalisation (e.g. `0 ∈ A`) without loss. -/
theorem kAPCount_count_translate {N : ℕ} [NeZero N] {k : ℕ} (A : Finset (ZMod N))
    (t : ZMod N) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => a + t))).card
      = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card := by
  classical
  have hmem : ∀ (x : ZMod N), x ∈ A.image (fun a => a + t) ↔ x - t ∈ A := by
    intro x
    rw [Finset.mem_image]
    exact ⟨by rintro ⟨a, ha, rfl⟩; simpa using ha, fun h => ⟨x - t, h, by ring⟩⟩
  have hset :
      (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          ∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => a + t)))
        = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
            ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).image (fun p => (p.1 + t, p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hmem]
    constructor
    · intro h
      refine ⟨(p.1 - t, p.2), fun i => ?_, by simp⟩
      have := h i
      rwa [show p.1 - t + i.val • p.2 = p.1 + i.val • p.2 - t from by abel]
    · rintro ⟨q, hq, rfl⟩ i
      have := hq i
      rwa [show q.1 + t + i.val • q.2 - t = q.1 + i.val • q.2 from by abel]
  rw [hset, Finset.card_image_of_injective]
  intro a b hab
  simp only [Prod.mk.injEq, add_left_inj] at hab
  exact Prod.ext hab.1 hab.2

/-- **Translation invariance of the nondegenerate `k`-AP count.**  The `d ≠ 0` restriction of
    `kAPCount_count_translate`: since the bijection `(x, d) ↦ (x + t, d)` fixes the common
    difference `d`, it preserves the nondegeneracy condition `d ≠ 0`.  Hence the genuine
    (nondiagonal) `k`-AP count that Roth's theorem controls is likewise translation-invariant. -/
theorem kAPCount_nondeg_translate {N : ℕ} [NeZero N] {k : ℕ} (A : Finset (ZMod N))
    (t : ZMod N) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => a + t)) ∧ p.2 ≠ 0)).card
      = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card := by
  classical
  have hmem : ∀ (x : ZMod N), x ∈ A.image (fun a => a + t) ↔ x - t ∈ A := by
    intro x
    rw [Finset.mem_image]
    exact ⟨by rintro ⟨a, ha, rfl⟩; simpa using ha, fun h => ⟨x - t, h, by ring⟩⟩
  have hset :
      (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => a + t)) ∧ p.2 ≠ 0))
        = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
            (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).image (fun p => (p.1 + t, p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hmem]
    constructor
    · rintro ⟨h, hd⟩
      refine ⟨(p.1 - t, p.2), ⟨fun i => ?_, hd⟩, by simp⟩
      have := h i
      rwa [show p.1 - t + i.val • p.2 = p.1 + i.val • p.2 - t from by abel]
    · rintro ⟨q, ⟨hq, hd⟩, rfl⟩
      refine ⟨fun i => ?_, hd⟩
      have := hq i
      rwa [show q.1 + t + i.val • q.2 - t = q.1 + i.val • q.2 from by abel]
  rw [hset, Finset.card_image_of_injective]
  intro a b hab
  simp only [Prod.mk.injEq, add_left_inj] at hab
  exact Prod.ext hab.1 hab.2

/-- **Analytic translation invariance.**  The normalized `k`-AP operator on an indicator is
    unchanged by translating the set: `Λ_k(1_{A+t}) = Λ_k(1_A)`.  Immediate from the
    combinatorial bridge `kAPCount_indicator_eq_count` and `kAPCount_count_translate`. -/
theorem kAPCount_indicator_translate {N : ℕ} [NeZero N] (k : ℕ) (A : Finset (ZMod N))
    (t : ZMod N) :
    kAPCount k (fun _ : Fin k => indicatorZMod (A.image (fun a => a + t)))
      = kAPCount k (fun _ : Fin k => indicatorZMod A) := by
  rw [kAPCount_indicator_eq_count, kAPCount_indicator_eq_count, kAPCount_count_translate]

/-- **Reflection invariance of the `k`-AP count.**  Negating the set, `A ↦ -A`, preserves
    the number of `k`-APs: the map `(x, d) ↦ (-x, -d)` is a bijection on pairs that sends the
    AP `x, x+d, …` inside `-A` to the AP `-x, -x-d, …` inside `A` (common difference negated).
    Together with `kAPCount_count_translate` this exhibits the affine symmetry `x ↦ -x + t` of
    the count; the reflection `x ↦ -x` is the order-two generator beyond translation. -/
theorem kAPCount_count_neg {N : ℕ} [NeZero N] {k : ℕ} (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => -a))).card
      = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card := by
  classical
  have hmem : ∀ (x : ZMod N), x ∈ A.image (fun a => -a) ↔ -x ∈ A := by
    intro x
    rw [Finset.mem_image]
    exact ⟨by rintro ⟨a, ha, rfl⟩; simpa using ha, fun h => ⟨-x, h, by ring⟩⟩
  have hset :
      (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          ∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => -a)))
        = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
            ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).image (fun p => (-p.1, -p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hmem]
    constructor
    · intro h
      refine ⟨(-p.1, -p.2), fun i => ?_, by simp⟩
      have := h i
      rwa [show (-p.1) + i.val • (-p.2) = -(p.1 + i.val • p.2) from by rw [smul_neg]; abel]
    · rintro ⟨q, hq, rfl⟩ i
      have := hq i
      rwa [show -((-q.1) + i.val • (-q.2)) = q.1 + i.val • q.2 from by rw [smul_neg]; abel]
  rw [hset, Finset.card_image_of_injective]
  intro a b hab
  simp only [Prod.mk.injEq, neg_inj] at hab
  exact Prod.ext hab.1 hab.2

/-- **Reflection invariance of the nondegenerate `k`-AP count.**  The `d ≠ 0` restriction of
    `kAPCount_count_neg`: the bijection `(x, d) ↦ (-x, -d)` sends `d ≠ 0` to `-d ≠ 0`, so the
    genuine (nondiagonal) `k`-AP count that Roth's theorem controls is likewise invariant under
    negating the set. -/
theorem kAPCount_nondeg_neg {N : ℕ} [NeZero N] {k : ℕ} (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => -a)) ∧ p.2 ≠ 0)).card
      = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card := by
  classical
  have hmem : ∀ (x : ZMod N), x ∈ A.image (fun a => -a) ↔ -x ∈ A := by
    intro x
    rw [Finset.mem_image]
    exact ⟨by rintro ⟨a, ha, rfl⟩; simpa using ha, fun h => ⟨-x, h, by ring⟩⟩
  have hset :
      (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => -a)) ∧ p.2 ≠ 0))
        = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
            (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).image (fun p => (-p.1, -p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hmem]
    constructor
    · rintro ⟨h, hd⟩
      refine ⟨(-p.1, -p.2), ⟨fun i => ?_, ?_⟩, by simp⟩
      · have := h i
        rwa [show (-p.1) + i.val • (-p.2) = -(p.1 + i.val • p.2) from by rw [smul_neg]; abel]
      · simpa using hd
    · rintro ⟨q, ⟨hq, hd⟩, rfl⟩
      refine ⟨fun i => ?_, by simpa using hd⟩
      have := hq i
      rwa [show -((-q.1) + i.val • (-q.2)) = q.1 + i.val • q.2 from by rw [smul_neg]; abel]
  rw [hset, Finset.card_image_of_injective]
  intro a b hab
  simp only [Prod.mk.injEq, neg_inj] at hab
  exact Prod.ext hab.1 hab.2

/-- **Analytic reflection invariance.**  The normalized `k`-AP operator on an indicator is
    unchanged by negating the set: `Λ_k(1_{-A}) = Λ_k(1_A)`.  Immediate from the combinatorial
    bridge `kAPCount_indicator_eq_count` and `kAPCount_count_neg`. -/
theorem kAPCount_indicator_neg {N : ℕ} [NeZero N] (k : ℕ) (A : Finset (ZMod N)) :
    kAPCount k (fun _ : Fin k => indicatorZMod (A.image (fun a => -a)))
      = kAPCount k (fun _ : Fin k => indicatorZMod A) := by
  rw [kAPCount_indicator_eq_count, kAPCount_indicator_eq_count, kAPCount_count_neg]

/-- **Dilation invariance of the `k`-AP count.**  Scaling the set by a unit `c ∈ (ℤ/N)ˣ`,
    `A ↦ c·A`, preserves the number of `k`-APs: the map `(x, d) ↦ (c·x, c·d)` is a bijection
    on pairs (as `c` is invertible) sending a progression `x, x+d, …` inside `c·A` to the
    progression `c⁻¹x, c⁻¹x + c⁻¹d, …` inside `A` (common difference scaled by `c⁻¹`).
    Together with `kAPCount_count_translate` this exhibits the full affine symmetry
    `x ↦ c·x + t` — the action of `AGL(1, ℤ/N)` — on the count; the reflection
    `kAPCount_count_neg` is exactly the special case `c = -1`. -/
theorem kAPCount_count_dilate {N : ℕ} [NeZero N] {k : ℕ} (A : Finset (ZMod N))
    (c : (ZMod N)ˣ) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => (c : ZMod N) * a))).card
      = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card := by
  classical
  -- `x ∈ c·A` iff `c⁻¹·x ∈ A`.
  have hmem : ∀ (x : ZMod N),
      x ∈ A.image (fun a => (c : ZMod N) * a) ↔ (↑c⁻¹ : ZMod N) * x ∈ A := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rwa [← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      exact ⟨(↑c⁻¹ : ZMod N) * x, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
  -- Scaling commutes with forming the progression `x + i·d`.
  have hshift : ∀ (s y d : ZMod N) (i : Fin k),
      (s * y) + i.val • (s * d) = s * (y + i.val • d) := by
    intro s y d i; simp only [nsmul_eq_mul]; ring
  have hset :
      (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          ∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => (c : ZMod N) * a)))
        = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
            ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).image
              (fun p => ((c : ZMod N) * p.1, (c : ZMod N) * p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hmem]
    constructor
    · intro h
      refine ⟨((↑c⁻¹ : ZMod N) * p.1, (↑c⁻¹ : ZMod N) * p.2), fun i => ?_, ?_⟩
      · rw [hshift (↑c⁻¹ : ZMod N) p.1 p.2 i]; exact h i
      · have e1 : (c : ZMod N) * ((↑c⁻¹ : ZMod N) * p.1) = p.1 := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        have e2 : (c : ZMod N) * ((↑c⁻¹ : ZMod N) * p.2) = p.2 := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        rw [Prod.ext_iff]; exact ⟨e1, e2⟩
    · rintro ⟨q, hq, rfl⟩ i
      rw [hshift (c : ZMod N) q.1 q.2 i, ← mul_assoc, Units.inv_mul, one_mul]
      exact hq i
  rw [hset, Finset.card_image_of_injective]
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  have hinj : ∀ {x y : ZMod N}, (c : ZMod N) * x = (c : ZMod N) * y → x = y := by
    intro x y h
    have h2 : (↑c⁻¹ : ZMod N) * ((c : ZMod N) * x) = (↑c⁻¹ : ZMod N) * ((c : ZMod N) * y) := by
      rw [h]
    rwa [← mul_assoc, Units.inv_mul, one_mul, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact Prod.ext (hinj hab.1) (hinj hab.2)

/-- **Dilation invariance of the nondegenerate `k`-AP count.**  The `d ≠ 0` restriction of
    `kAPCount_count_dilate`: since `c` is a unit, `c·d = 0 ↔ d = 0`, so the bijection
    `(x, d) ↦ (c·x, c·d)` preserves nondegeneracy.  Hence the genuine (nondiagonal) `k`-AP
    count that Roth's theorem controls is invariant under scaling the set by any unit. -/
theorem kAPCount_nondeg_dilate {N : ℕ} [NeZero N] {k : ℕ} (A : Finset (ZMod N))
    (c : (ZMod N)ˣ) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => (c : ZMod N) * a)) ∧ p.2 ≠ 0)).card
      = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card := by
  classical
  have hmem : ∀ (x : ZMod N),
      x ∈ A.image (fun a => (c : ZMod N) * a) ↔ (↑c⁻¹ : ZMod N) * x ∈ A := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rwa [← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      exact ⟨(↑c⁻¹ : ZMod N) * x, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
  have hshift : ∀ (s y d : ZMod N) (i : Fin k),
      (s * y) + i.val • (s * d) = s * (y + i.val • d) := by
    intro s y d i; simp only [nsmul_eq_mul]; ring
  -- A unit never sends a nonzero element to `0`.
  have hmul_ne : ∀ (u : (ZMod N)ˣ) {y : ZMod N}, y ≠ 0 → (↑u : ZMod N) * y ≠ 0 := by
    intro u y hy hcy
    apply hy
    have h2 : (↑u⁻¹ : ZMod N) * ((u : ZMod N) * y) = (↑u⁻¹ : ZMod N) * 0 := by rw [hcy]
    rwa [← mul_assoc, Units.inv_mul, one_mul, mul_zero] at h2
  have hset :
      (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => (c : ZMod N) * a)) ∧ p.2 ≠ 0))
        = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
            (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).image
              (fun p => ((c : ZMod N) * p.1, (c : ZMod N) * p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hmem]
    constructor
    · rintro ⟨h, hd⟩
      refine ⟨((↑c⁻¹ : ZMod N) * p.1, (↑c⁻¹ : ZMod N) * p.2), ⟨fun i => ?_, ?_⟩, ?_⟩
      · rw [hshift (↑c⁻¹ : ZMod N) p.1 p.2 i]; exact h i
      · exact hmul_ne c⁻¹ hd
      · have e1 : (c : ZMod N) * ((↑c⁻¹ : ZMod N) * p.1) = p.1 := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        have e2 : (c : ZMod N) * ((↑c⁻¹ : ZMod N) * p.2) = p.2 := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        rw [Prod.ext_iff]; exact ⟨e1, e2⟩
    · rintro ⟨q, ⟨hq, hd⟩, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · rw [hshift (c : ZMod N) q.1 q.2 i, ← mul_assoc, Units.inv_mul, one_mul]
        exact hq i
      · exact hmul_ne c hd
  rw [hset, Finset.card_image_of_injective]
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  have hinj : ∀ {x y : ZMod N}, (c : ZMod N) * x = (c : ZMod N) * y → x = y := by
    intro x y h
    have h2 : (↑c⁻¹ : ZMod N) * ((c : ZMod N) * x) = (↑c⁻¹ : ZMod N) * ((c : ZMod N) * y) := by
      rw [h]
    rwa [← mul_assoc, Units.inv_mul, one_mul, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact Prod.ext (hinj hab.1) (hinj hab.2)

/-- **Analytic dilation invariance.**  The normalized `k`-AP operator on an indicator is
    unchanged by scaling the set by a unit: `Λ_k(1_{c·A}) = Λ_k(1_A)` for `c ∈ (ℤ/N)ˣ`.
    Immediate from the combinatorial bridge `kAPCount_indicator_eq_count` and
    `kAPCount_count_dilate`.  This is the multiplicative half of the affine invariance of the
    density-`k`-AP-count functional at the heart of the density-increment argument. -/
theorem kAPCount_indicator_dilate {N : ℕ} [NeZero N] (k : ℕ) (A : Finset (ZMod N))
    (c : (ZMod N)ˣ) :
    kAPCount k (fun _ : Fin k => indicatorZMod (A.image (fun a => (c : ZMod N) * a)))
      = kAPCount k (fun _ : Fin k => indicatorZMod A) := by
  rw [kAPCount_indicator_eq_count, kAPCount_indicator_eq_count, kAPCount_count_dilate]

/-! ### Affine invariance: the full `x ↦ c·x + t` symmetry in one theorem

Translation (`kAPCount_*_translate`, `t`), dilation by a unit (`kAPCount_*_dilate`, `c`),
and negation (the `c = -1` case) are the generators of the affine group `x ↦ c·x + t`
(`c ∈ (ZMod N)ˣ`, `t ∈ ZMod N`) acting on `ZMod N`.  The `k`-AP count is invariant under
each generator; the theorems below record the invariance under a **general** affine map in a
single statement, obtained by factoring `A.image (·↦ c·+t)` as `dilate` followed by
`translate` (`affine_image_eq`) and chaining the two existing invariances.  This is the
exact symmetry group under which "`A` contains a nondegenerate `k`-AP" is invariant, so it is
the natural home for normalising a set before an increment/density argument. -/

/-- Factor the affine image `c·A + t` as the translate of the dilate: `A.image (a ↦ c·a + t)
= (A.image (a ↦ c·a)).image (b ↦ b + t)`. -/
theorem affine_image_eq {N : ℕ} (A : Finset (ZMod N)) (c : (ZMod N)ˣ) (t : ZMod N) :
    A.image (fun a => (c : ZMod N) * a + t)
      = (A.image (fun a => (c : ZMod N) * a)).image (fun b => b + t) := by
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨(c : ZMod N) * a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩

/-- **Affine invariance of the `k`-AP count.**  For any unit `c` and shift `t`, the `k`-AP
count of the affine image `c·A + t` equals that of `A`.  The common generalisation of
`kAPCount_count_translate` (`c = 1`) and `kAPCount_count_dilate` (`t = 0`, and `c = -1`
recovers `kAPCount_count_neg`): chain the two via `affine_image_eq`. -/
theorem kAPCount_count_affine {N : ℕ} [NeZero N] {k : ℕ} (A : Finset (ZMod N))
    (c : (ZMod N)ˣ) (t : ZMod N) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => (c : ZMod N) * a + t))).card
      = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          ∀ i : Fin k, p.1 + i.val • p.2 ∈ A)).card := by
  rw [affine_image_eq, kAPCount_count_translate, kAPCount_count_dilate]

/-- **Affine invariance of the nondegenerate `k`-AP count.**  The `d ≠ 0` restriction of
`kAPCount_count_affine`: an affine map `x ↦ c·x + t` (`c` a unit) fixes the common difference
up to the unit `c`, preserving `d ≠ 0`, so the genuine (nondiagonal) count Roth controls is
affine-invariant.  Chains `kAPCount_nondeg_translate` and `kAPCount_nondeg_dilate`. -/
theorem kAPCount_nondeg_affine {N : ℕ} [NeZero N] {k : ℕ} (A : Finset (ZMod N))
    (c : (ZMod N)ˣ) (t : ZMod N) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A.image (fun a => (c : ZMod N) * a + t)) ∧ p.2 ≠ 0)).card
      = (Finset.univ.filter (fun p : ZMod N × ZMod N =>
          (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card := by
  rw [affine_image_eq, kAPCount_nondeg_translate, kAPCount_nondeg_dilate]

/-- **Analytic affine invariance.**  The normalized `k`-AP operator on an indicator is unchanged
by any affine map of the set: `Λ_k(1_{c·A+t}) = Λ_k(1_A)`.  The common generalisation of
`kAPCount_indicator_translate` and `kAPCount_indicator_dilate`. -/
theorem kAPCount_indicator_affine {N : ℕ} [NeZero N] (k : ℕ) (A : Finset (ZMod N))
    (c : (ZMod N)ˣ) (t : ZMod N) :
    kAPCount k (fun _ : Fin k => indicatorZMod (A.image (fun a => (c : ZMod N) * a + t)))
      = kAPCount k (fun _ : Fin k => indicatorZMod A) := by
  rw [affine_image_eq, kAPCount_indicator_translate, kAPCount_indicator_dilate]

-- ============================================================
-- Analytic boundedness and the sup-norm generalized von Neumann bound
--
-- Every identity above is *algebraic* (multilinearity, symmetry, affine
-- invariance).  The generalized von Neumann argument also needs an
-- *analytic* estimate: the operator `Λ_k` is bounded by the product of the
-- sup-norms of its slots.  This is the trivial (`L^∞`) version of the
-- generalized von Neumann inequality; the sharp version replaces one
-- slot's sup-norm by its Gowers `U^{k-1}` norm and is the one genuinely
-- hard step that remains open.
-- ============================================================

/-- **Boundedness of the k-AP counting operator.**  If every slot function
    is uniformly bounded, `‖f i x‖ ≤ M i`, then the normalized average is
    bounded by the product of the bounds:
    `‖Λ_k(f₀,…,f_{k-1})‖ ≤ ∏ᵢ Mᵢ`.
    Proof: the triangle inequality passes the norm through the double
    average `E_{x,d}` and the length-`k` product (`norm_sum_le`, `norm_prod`,
    `Finset.prod_le_prod`); the `N²` terms of the average cancel the `(N⁻¹)²`
    normalization.  This is the first analytic estimate on `Λ_k` and the
    trivial (`L^∞`) form of the generalized von Neumann bound. -/
theorem kAPCount_norm_le {N : ℕ} [NeZero N] (k : ℕ) (f : Fin k → ZMod N → ℂ)
    (M : Fin k → ℝ) (hM : ∀ i x, ‖f i x‖ ≤ M i) :
    ‖kAPCount k f‖ ≤ ∏ i : Fin k, M i := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold kAPCount
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ x : ZMod N, ∑ d : ZMod N, ∏ i : Fin k, f i (x + i.val • d)‖
      ≤ (N : ℝ) ^ 2 * ∏ i : Fin k, M i := by
    calc ‖∑ x : ZMod N, ∑ d : ZMod N, ∏ i : Fin k, f i (x + i.val • d)‖
        ≤ ∑ x : ZMod N, ‖∑ d : ZMod N, ∏ i : Fin k, f i (x + i.val • d)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ x : ZMod N, ∑ d : ZMod N, ‖∏ i : Fin k, f i (x + i.val • d)‖ :=
          Finset.sum_le_sum (fun x _ => norm_sum_le _ _)
      _ ≤ ∑ x : ZMod N, ∑ d : ZMod N, ∏ i : Fin k, M i := by
          apply Finset.sum_le_sum; intro x _
          apply Finset.sum_le_sum; intro d _
          rw [norm_prod]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hM i _)
      _ = (N : ℝ) ^ 2 * ∏ i : Fin k, M i := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          ring
  calc ((N : ℝ)⁻¹) ^ 2
          * ‖∑ x : ZMod N, ∑ d : ZMod N, ∏ i : Fin k, f i (x + i.val • d)‖
      ≤ ((N : ℝ)⁻¹) ^ 2 * ((N : ℝ) ^ 2 * ∏ i : Fin k, M i) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ∏ i : Fin k, M i := by
        rw [inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 2 hN)]

/-- Each value of the complex indicator `1_A` has norm at most `1`. -/
theorem indicatorZMod_norm_le_one {N : ℕ} (A : Finset (ZMod N)) (x : ZMod N) :
    ‖indicatorZMod A x‖ ≤ 1 := by
  unfold indicatorZMod; split <;> simp

/-- **The normalized k-AP density is bounded by `1`.**  Feeding the indicator
    `1_A` into every slot, `‖Λ_k(1_A,…,1_A)‖ ≤ 1` — the analytic counterpart of
    `kAPCount_indicator_eq_count` (`Λ_k(1_A) = (N⁻¹)²·#{k-APs in A} ∈ [0,1]`),
    i.e. the number of length-`k` progressions inside `A` never exceeds `N²`. -/
theorem kAPCount_indicator_norm_le_one {N : ℕ} [NeZero N] (k : ℕ)
    (A : Finset (ZMod N)) :
    ‖kAPCount k (fun _ : Fin k => indicatorZMod A)‖ ≤ 1 := by
  have h := kAPCount_norm_le k (fun _ => indicatorZMod A) (fun _ => 1)
    (fun _ x => indicatorZMod_norm_le_one A x)
  simpa using h

/-- A slot-indexed product of a value `β ∈ [0,1]` (on a nonempty index set `S`)
    and `1` (elsewhere) is at most `β`.  Because `∏ = β^{|S|}` and `β ≤ 1` with
    `|S| ≥ 1`.  This is the elementary factor bound behind the remainder
    estimate below. -/
theorem prod_ite_le_self {k : ℕ} (S : Finset (Fin k)) (hSne : S.Nonempty)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∏ i : Fin k, (if i ∈ S then β else (1 : ℝ)) ≤ β := by
  obtain ⟨j, hj⟩ := hSne
  rw [← Finset.mul_prod_erase Finset.univ
        (fun i => if i ∈ S then β else (1 : ℝ)) (Finset.mem_univ j)]
  rw [if_pos hj]
  have hrest : ∏ i ∈ Finset.univ.erase j, (if i ∈ S then β else (1 : ℝ)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _; split <;> [exact hβ0; exact zero_le_one]
    · intro i _; split <;> [exact hβ1; exact le_refl 1]
  calc β * ∏ i ∈ Finset.univ.erase j, (if i ∈ S then β else (1 : ℝ))
      ≤ β * 1 := mul_le_mul_of_nonneg_left hrest hβ0
    _ = β := mul_one β

/-- **Sup-norm generalized von Neumann bound (the trivial `L^∞` form).**
    Write `1_A = δ·1 + b` with balanced part `b = g − δ·1`.  The multilinear
    expansion `kAPCount_diag_eq_major_add_remainder` splits the diagonal count
    into the major term `δ^k` plus `2^k − 1` remainder terms, each carrying at
    least one balanced slot.  If the balanced function is uniformly small,
    `‖b x‖ ≤ β`, and `‖δ‖ ≤ 1`, `β ≤ 1`, then every remainder term is `≤ β`
    (via `kAPCount_norm_le` and `prod_ite_le_self`), so

      `‖Λ_k(g,…,g) − δ^k‖ ≤ 2^k · β`.

    Thus the normalized `k`-AP count of `g` equals the "expected" `δ^k` up to
    an error linear in the balanced function's sup-norm.  This is precisely the
    skeleton of the generalized von Neumann argument; the sharp inequality
    replaces the sup-norm `β = ‖b‖_∞` by the (typically far smaller) Gowers
    `U^{k-1}` norm of `b`, which is the one genuinely hard step still open. -/
theorem kAPCount_diag_sub_major_norm_le {N : ℕ} [NeZero N] (k : ℕ)
    (g : ZMod N → ℂ) (δ : ℂ) (β : ℝ) (hδ1 : ‖δ‖ ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβx : ∀ x, ‖(g - δ • (1 : ZMod N → ℂ)) x‖ ≤ β) :
    ‖kAPCount k (fun _ : Fin k => g) - δ ^ k‖ ≤ (2 : ℝ) ^ k * β := by
  have hdiff : kAPCount k (fun _ : Fin k => g) - δ ^ k
      = ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin k))),
          δ ^ (k - S.card)
            * kAPCount k (fun i => if i ∈ S then (g - δ • (1 : ZMod N → ℂ)) else 1) := by
    rw [kAPCount_diag_eq_major_add_remainder k g δ]; ring
  rw [hdiff]
  refine (norm_sum_le _ _).trans ?_
  -- each remainder term has norm ≤ β
  have hterm : ∀ S ∈ (Finset.univ.erase (∅ : Finset (Fin k))),
      ‖δ ^ (k - S.card)
          * kAPCount k (fun i => if i ∈ S then (g - δ • (1 : ZMod N → ℂ)) else 1)‖ ≤ β := by
    intro S hS
    have hSne : S ≠ ∅ := (Finset.mem_erase.mp hS).1
    have hSpos : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
    rw [norm_mul, norm_pow]
    have hδk : ‖δ‖ ^ (k - S.card) ≤ 1 := pow_le_one₀ (norm_nonneg _) hδ1
    have hslot :
        ‖kAPCount k (fun i => if i ∈ S then (g - δ • (1 : ZMod N → ℂ)) else 1)‖ ≤ β := by
      refine (kAPCount_norm_le k _ (fun i => if i ∈ S then β else 1) ?_).trans
        (prod_ite_le_self S hSpos β hβ0 hβ1)
      intro i x
      dsimp only
      by_cases hi : i ∈ S
      · rw [if_pos hi, if_pos hi]; exact hβx x
      · rw [if_neg hi, if_neg hi]; simp
    calc ‖δ‖ ^ (k - S.card)
            * ‖kAPCount k (fun i => if i ∈ S then (g - δ • (1 : ZMod N → ℂ)) else 1)‖
        ≤ 1 * β := mul_le_mul hδk hslot (norm_nonneg _) zero_le_one
      _ = β := one_mul β
  -- sum the constant bound: at most 2^k terms
  calc ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin k))),
          ‖δ ^ (k - S.card)
            * kAPCount k (fun i => if i ∈ S then (g - δ • (1 : ZMod N → ℂ)) else 1)‖
      ≤ ∑ _S ∈ (Finset.univ.erase (∅ : Finset (Fin k))), β := Finset.sum_le_sum hterm
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Finset (Fin k))), β :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun S _ _ => hβ0)
    _ = (2 : ℝ) ^ k * β := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]
        push_cast
        ring

-- ============================================================
-- Reversal (reflection) symmetry of the k-AP count
--
-- A length-`k` progression `x, x+d, …, x+(k-1)d` reversed reads
-- `x+(k-1)d, x+(k-2)d, …, x` — the *same* `k` points listed backwards,
-- i.e. the progression starting at `x+(k-1)d` with common difference `-d`.
-- For `k = 3` this is the classical `(x, d) ↦ (x+2d, -d)` reversal that
-- underlies the "reflection" symmetry of 3-AP counts. Below we make this
-- precise: reversal `kAPReflect` is an involution of `ZMod N × ZMod N`, it
-- preserves the (total and nondegenerate) `k`-AP count conditions, and hence
-- fixes the count set as a set (`image (kAPReflect k) = id` on it).
--
-- NOTE (why this does *not* prove the count is even): the involution has fixed
-- points — any pair with `(k-1)d = 0` and `2d = 0` (e.g. `d = 0`, or `d` of
-- additive order `2` when `k` is odd) is its own reversal — so the orbit-count
-- argument that would force an even cardinality does not apply. The symmetry is
-- genuine but weaker than fixed-point-freeness.
-- ============================================================

/-- **Reversal (reflection) of an arithmetic progression.**  Sends the pair `(x, d)` — the
    length-`k` progression `x, x+d, …, x+(k-1)d` — to `(x + (k-1)·d, -d)`, whose progression
    `x+(k-1)d, x+(k-2)d, …, x` runs through the *same* `k` points in reverse.  For `k = 3`
    this is the classical `(x, d) ↦ (x+2d, -d)` reversal of a 3-term progression. -/
def kAPReflect {N : ℕ} (k : ℕ) (p : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (p.1 + (k - 1) • p.2, -p.2)

/-- **Reversal is an involution.**  Reversing twice returns the original pair:
    `(x, d) ↦ (x+(k-1)d, -d) ↦ ((x+(k-1)d) + (k-1)(-d), -(-d)) = (x, d)`.  In particular
    `kAPReflect k` is a bijection of `ZMod N × ZMod N`. -/
theorem kAPReflect_involutive {N : ℕ} (k : ℕ) :
    Function.Involutive (kAPReflect (N := N) k) := by
  intro p
  obtain ⟨x, d⟩ := p
  simp only [kAPReflect, smul_neg, neg_neg, add_neg_cancel_right]

/-- **The `k`-AP count set is closed under reversal.**  For `k ≥ 1`, if the length-`k`
    progression of `(x, d)` lies entirely in `A`, so does that of its reversal
    `kAPReflect k (x, d)`: the reversed progression runs through the same points
    `x + j·d` with `j = k-1-i` (a reindexing of `Fin k`). -/
theorem kAPCount_count_reflect_mem {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    {A : Finset (ZMod N)} {p : ZMod N × ZMod N}
    (hp : p ∈ Finset.univ.filter (fun q : ZMod N × ZMod N =>
        ∀ i : Fin k, q.1 + i.val • q.2 ∈ A)) :
    kAPReflect k p ∈ Finset.univ.filter (fun q : ZMod N × ZMod N =>
        ∀ i : Fin k, q.1 + i.val • q.2 ∈ A) := by
  classical
  rw [Finset.mem_filter] at hp ⊢
  obtain ⟨x, d⟩ := p
  obtain ⟨-, hall⟩ := hp
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i
  have hi : i.val < k := i.isLt
  -- Split `(k-1)•d = (k-1-i)•d + i•d` (valid since `i ≤ k-1`).
  have hsub : (k - 1) • d = (k - 1 - i.val) • d + i.val • d := by
    rw [← add_nsmul]; congr 1; omega
  -- The reflected `i`-th term equals the original `(k-1-i)`-th term.
  have hterm : (kAPReflect k (x, d)).1 + i.val • (kAPReflect k (x, d)).2
      = x + (k - 1 - i.val) • d := by
    simp only [kAPReflect, smul_neg]
    rw [hsub]; abel
  rw [hterm]
  simpa using hall ⟨k - 1 - i.val, by omega⟩

/-- **The nondegenerate `k`-AP count set is closed under reversal.**  Reversal preserves the
    nondegeneracy condition `d ≠ 0` (it maps `d ↦ -d`), so on top of the term-membership
    closure `kAPCount_count_reflect_mem` it also fixes the `d ≠ 0` count set. -/
theorem kAPCount_nondeg_reflect_mem {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    {A : Finset (ZMod N)} {p : ZMod N × ZMod N}
    (hp : p ∈ Finset.univ.filter (fun q : ZMod N × ZMod N =>
        (∀ i : Fin k, q.1 + i.val • q.2 ∈ A) ∧ q.2 ≠ 0)) :
    kAPReflect k p ∈ Finset.univ.filter (fun q : ZMod N × ZMod N =>
        (∀ i : Fin k, q.1 + i.val • q.2 ∈ A) ∧ q.2 ≠ 0) := by
  classical
  rw [Finset.mem_filter] at hp ⊢
  obtain ⟨-, hall, hd⟩ := hp
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · -- term membership: reuse the total-count reflection lemma
    have hmem : kAPReflect k p ∈ Finset.univ.filter (fun q : ZMod N × ZMod N =>
        ∀ i : Fin k, q.1 + i.val • q.2 ∈ A) :=
      kAPCount_count_reflect_mem hk (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hall⟩)
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  · -- nondegeneracy: the reflected difference is `-d ≠ 0`
    simp only [kAPReflect, ne_eq, neg_eq_zero]
    exact hd

/-- **Reflection symmetry of the total `k`-AP count.**  For `k ≥ 1` the set of pairs whose
    length-`k` progression lies in `A` is invariant under reversal — `kAPReflect k` maps it
    bijectively onto itself, so `image (kAPReflect k) = id` there.  Combined with
    `kAPReflect_involutive`, reversal is an involutive symmetry of the count set.  (It is *not*
    fixed-point-free — pairs with `(k-1)d = 0` and `2d = 0` are self-reversing — so this does
    **not** force the count to be even.) -/
theorem kAPCount_count_reflect_image {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    Finset.image (kAPReflect k) (Finset.univ.filter (fun q : ZMod N × ZMod N =>
        ∀ i : Fin k, q.1 + i.val • q.2 ∈ A))
      = Finset.univ.filter (fun q : ZMod N × ZMod N =>
        ∀ i : Fin k, q.1 + i.val • q.2 ∈ A) := by
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_iff.mpr (fun p hp => kAPCount_count_reflect_mem hk hp)
  · intro q hq
    exact Finset.mem_image.mpr ⟨kAPReflect k q, kAPCount_count_reflect_mem hk hq,
      kAPReflect_involutive k q⟩

/-- **Reflection symmetry of the nondegenerate `k`-AP count.**  The `d ≠ 0` count set is
    likewise invariant under reversal.  This is the `d ≠ 0` companion of
    `kAPCount_count_reflect_image`, and the general-`k` form of the "reversal involution on
    nondegenerate 3-AP pairs" — a genuine symmetry of the count Roth's theorem controls, though
    (having fixed points) not one that yields an evenness/parity conclusion. -/
theorem kAPCount_nondeg_reflect_image {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k)
    (A : Finset (ZMod N)) :
    Finset.image (kAPReflect k) (Finset.univ.filter (fun q : ZMod N × ZMod N =>
        (∀ i : Fin k, q.1 + i.val • q.2 ∈ A) ∧ q.2 ≠ 0))
      = Finset.univ.filter (fun q : ZMod N × ZMod N =>
        (∀ i : Fin k, q.1 + i.val • q.2 ∈ A) ∧ q.2 ≠ 0) := by
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_iff.mpr (fun p hp => kAPCount_nondeg_reflect_mem hk hp)
  · intro q hq
    exact Finset.mem_image.mpr ⟨kAPReflect k q, kAPCount_nondeg_reflect_mem hk hq,
      kAPReflect_involutive k q⟩

/-- **No nondegenerate progression in a set of size `≤ 1`.**  For `k ≥ 2`, any set `A` with
    `A.card ≤ 1` has nondegenerate (`d ≠ 0`) `k`-AP count `0`.  This is the common generalization
    of `kAPCount_nondeg_empty` (`A = ∅`) and `kAPCount_nondeg_singleton` (`A = {a}`): the `i = 0`
    and `i = 1` terms of any counted progression both lie in `A`, and a set with at most one element
    forces them equal (`Finset.card_le_one`), hence `d = 0`, contradicting `d ≠ 0`. -/
theorem kAPCount_nondeg_card_le_one {N : ℕ} [NeZero N] {k : ℕ} (hk : 2 ≤ k)
    {A : Finset (ZMod N)} (hA : A.card ≤ 1) :
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p -
  rintro ⟨hall, hd⟩
  -- `i = 0` and `i = 1` terms both lie in `A`
  have h0 : p.1 ∈ A := by simpa using hall ⟨0, by omega⟩
  have h1 : p.1 + p.2 ∈ A := by simpa using hall ⟨1, by omega⟩
  -- `A.card ≤ 1` forces the two members to coincide, so `d = 0`
  have heq : p.1 + p.2 = p.1 := Finset.card_le_one.mp hA _ h1 _ h0
  refine hd (add_left_cancel (a := p.1) ?_)
  rw [add_zero]
  exact heq

/-- **A nondegenerate progression forces at least two points.**  For `k ≥ 2`, if the
    nondegenerate (`d ≠ 0`) `k`-AP count of `A` is positive then `2 ≤ A.card`.  The contrapositive
    of `kAPCount_nondeg_card_le_one`, and the trivial necessary condition underlying Roth's
    theorem: a set carrying *any* genuine (non-constant) progression must have at least two
    elements.  Roth's theorem sharpens "`≥ 2`" to the density threshold that forces nondegenerate
    mass; this lemma is its `card`-level floor. -/
theorem kAPCount_nondeg_pos_imp_two_le_card {N : ℕ} [NeZero N] {k : ℕ} (hk : 2 ≤ k)
    {A : Finset (ZMod N)}
    (hpos : 0 < (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        (∀ i : Fin k, p.1 + i.val • p.2 ∈ A) ∧ p.2 ≠ 0)).card) :
    2 ≤ A.card := by
  by_contra h
  have hle : A.card ≤ 1 := by omega
  rw [kAPCount_nondeg_card_le_one hk hle] at hpos
  exact lt_irrefl 0 hpos

end RothTheoremOQ03OQ01
