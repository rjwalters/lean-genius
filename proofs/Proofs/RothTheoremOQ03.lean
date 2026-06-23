/-
  Roth Theorem OQ-03: Density Increment Generalization to k-APs

  The density increment strategy for Roth's theorem (k=3, Fourier-based)
  generalizes to k-APs via Gowers uniformity norms. For k=3, the Fourier
  transform (U² norm) suffices. For k≥4, the U^{k-1} norm controls k-AP
  counts via the generalized von Neumann theorem.

  Key mathematical framework:
  - Gowers U^s norms: ||f||_{U^s} measures s-th order uniformity
  - Generalized von Neumann: k-AP count controlled by U^{k-1} norm
  - Inverse theorem: low U^s norm implies structured approximation
  - Density increment: structured approximation → density increase on subprogression

  gowersNorm and kAPCount defined constructively (not axiomatized).
  density_increment_k3_explicit proved from RothTheorem.lean infrastructure.

  References:
  - Gowers, "A new proof of Szemerédi's theorem" (2001)
  - Gowers, "A new proof of Szemerédi's theorem for k=4" (1998)
  - Green-Tao, "The primes contain arbitrarily long APs" (2008)
  - Tao, "Higher order Fourier analysis" (2012)
-/

import Mathlib
import Proofs.RothTheorem
import Proofs.SzemerediTheorem

namespace RothTheoremOQ03

open Finset BigOperators

-- ============================================================
-- PART I: k-AP-Free Sets in ZMod N
-- ============================================================

/-- A finset A in ZMod N is k-AP-free if it contains no non-trivial
    arithmetic progression of length k: no a, d with d ≠ 0 such that
    {a, a+d, a+2d, ..., a+(k-1)d} ⊆ A. -/
def IsKAPFreeZMod {N : ℕ} (A : Finset (ZMod N)) (k : ℕ) : Prop :=
  ∀ (a d : ZMod N), d ≠ 0 → (∀ i : Fin k, (a + i.val • d) ∈ A) → False

/-- For k=3, IsKAPFreeZMod implies Szemeredi.Roth.APFree. -/
theorem apFree_of_isKAPFreeZMod_three {N : ℕ} {A : Finset (ZMod N)}
    (h : IsKAPFreeZMod A 3) : Szemeredi.Roth.APFree A := by
  intro a d hd ha had hadd
  exact h a d hd fun i => by
    fin_cases i
    · rw [show (0 : Fin 3).val = 0 from rfl, zero_nsmul, add_zero]; exact ha
    · rw [show (1 : Fin 3).val = 1 from rfl, one_nsmul]; exact had
    · rw [show (2 : Fin 3).val = 2 from rfl, two_nsmul, ← two_mul]; exact hadd

/-- Converse: Szemeredi.Roth.APFree implies IsKAPFreeZMod for k=3. -/
theorem isKAPFreeZMod_three_of_apFree {N : ℕ} {A : Finset (ZMod N)}
    (h : Szemeredi.Roth.APFree A) : IsKAPFreeZMod A 3 := by
  intro a d hd hAP
  have ha : a ∈ A := by
    have := hAP ⟨0, by omega⟩; rwa [show (0 : Fin 3).val = 0 from rfl, zero_nsmul, add_zero] at this
  have had : a + d ∈ A := by
    have := hAP ⟨1, by omega⟩; rwa [show (1 : Fin 3).val = 1 from rfl, one_nsmul] at this
  have hadd : a + 2 * d ∈ A := by
    have := hAP ⟨2, by omega⟩; rwa [show (2 : Fin 3).val = 2 from rfl, two_nsmul, ← two_mul] at this
  exact h a d hd ha had hadd

-- ============================================================
-- PART I.5: Structural Lemmas for IsKAPFreeZMod
-- ============================================================

/-
Routine structural facts that mirror the k=3 lemmas in
`Szemeredi.Roth` (apFree_empty / apFree_subset etc.). These are
useful for combining or restricting AP-free witnesses across
the density-increment recursion.
-/

/-- The empty set is k-AP-free for any k ≥ 1.
    For k = 0 the predicate is non-trivially false on any ZMod N
    with N ≥ 2 (the implication has vacuous AP hypothesis but a
    non-vacuous d ≠ 0), so we require k ≥ 1. -/
theorem isKAPFreeZMod_empty {N k : ℕ} (hk : 0 < k) :
    IsKAPFreeZMod (∅ : Finset (ZMod N)) k := by
  intro a d _ hAP
  exact (Finset.notMem_empty _) (hAP ⟨0, hk⟩)

/-- Monotonicity in the set: subsets of k-AP-free sets are k-AP-free. -/
theorem isKAPFreeZMod_subset {N k : ℕ} {A B : Finset (ZMod N)}
    (hAB : B ⊆ A) (hA : IsKAPFreeZMod A k) : IsKAPFreeZMod B k :=
  fun a d hd hAP => hA a d hd (fun i => hAB (hAP i))

/-- Monotonicity in k: if A is k-AP-free then A is (k+1)-AP-free.
    Reason: any (k+1)-AP {a, a+d, …, a+kd} contains the k-AP
    {a, a+d, …, a+(k-1)d} as its initial segment. -/
theorem isKAPFreeZMod_succ {N k : ℕ} {A : Finset (ZMod N)}
    (h : IsKAPFreeZMod A k) : IsKAPFreeZMod A (k + 1) :=
  fun a d hd hAP => h a d hd (fun i => hAP i.castSucc)

/-- A singleton is k-AP-free for any k ≥ 2.
    Reason: the positions 0 and 1 in a putative AP would give
    a = x and a + d = x, forcing d = 0. -/
theorem isKAPFreeZMod_singleton {N : ℕ} (x : ZMod N) {k : ℕ} (hk : 2 ≤ k) :
    IsKAPFreeZMod ({x} : Finset (ZMod N)) k := by
  intro a d hd hAP
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  have ha : a ∈ ({x} : Finset (ZMod N)) := by
    have := hAP ⟨0, h0⟩
    rwa [show (⟨0, h0⟩ : Fin k).val = 0 from rfl, zero_nsmul, add_zero] at this
  have had : a + d ∈ ({x} : Finset (ZMod N)) := by
    have := hAP ⟨1, h1⟩
    rwa [show (⟨1, h1⟩ : Fin k).val = 1 from rfl, one_nsmul] at this
  rw [Finset.mem_singleton] at ha had
  apply hd
  -- a = x and a + d = x ⟹ d = 0
  have hcancel : a + d = a + 0 := by rw [add_zero, had, ← ha]
  exact add_left_cancel hcancel

/-- Convenience: if A is 3-AP-free in our sense, then `Szemeredi.Roth.APFree`
    holds and conversely. Bundles the two bridge directions for k = 3. -/
theorem isKAPFreeZMod_three_iff_apFree {N : ℕ} {A : Finset (ZMod N)} :
    IsKAPFreeZMod A 3 ↔ Szemeredi.Roth.APFree A :=
  ⟨apFree_of_isKAPFreeZMod_three, isKAPFreeZMod_three_of_apFree⟩

-- ============================================================
-- PART II: Gowers Uniformity Norms
-- ============================================================

/-
The Gowers U^s norm measures s-th order uniformity of a function
f : ZMod N → ℂ. It generalizes the Fourier L^4 norm:
- ||f||_{U^1} = |E[f]|              (mean)
- ||f||_{U^2} = (E[|f̂|^4])^{1/4}   (Fourier L^4)
- ||f||_{U^s} involves 2^s-point correlations

Formally:
  ||f||_{U^s}^{2^s} = E_{x, h₁,...,hₛ} ∏_{ω ∈ {0,1}^s} C^{|ω|} f(x + ω·h)

where C is complex conjugation, |ω| = Σ ωᵢ, and ω·h = Σ ωᵢhᵢ.
-/

/-- The shift determined by hypercube vertex ω and shift vectors h.
    ω · h = Σᵢ (if ωᵢ then hᵢ else 0) -/
noncomputable def hypercubeShift {N s : ℕ} (h : Fin s → ZMod N)
    (ω : Fin s → Bool) : ZMod N :=
  ∑ i : Fin s, if ω i then h i else 0

/-- Conjugation factor: conjugate when the Hamming weight of ω is odd.
    C^{|ω|}(z) = z if |ω| even, conj(z) if |ω| odd. -/
noncomputable def conjugateByWeight {s : ℕ} (ω : Fin s → Bool) (z : ℂ) : ℂ :=
  if (Finset.univ.filter (fun i => ω i = true)).card % 2 = 0
  then z else starRingEnd ℂ z

/-- The Gowers U^s norm of f : ZMod N → ℂ, raised to the power 2^s.
    ||f||_{U^s}^{2^s} = |E_{x, h₁,...,hₛ} ∏_{ω ∈ {0,1}^s} C^{|ω|} f(x + ω·h)|
    Defined constructively as a finite sum over ZMod N. -/
noncomputable def gowersNorm (N s : ℕ) [NeZero N] (f : ZMod N → ℂ) : ℝ :=
  Complex.abs (
    ((N : ℂ)⁻¹) ^ (s + 1) *
    ∑ x : ZMod N, ∑ h : Fin s → ZMod N,
      ∏ ω : Fin s → Bool,
        conjugateByWeight ω (f (x + hypercubeShift h ω)))

-- ============================================================
-- PART III: k-AP Counting Operator
-- ============================================================

/-
The k-AP counting operator Λ_k(f₁,...,fₖ):
  Λ_k(f₁,...,fₖ) = E_{x,d} f₁(x) f₂(x+d) ··· fₖ(x+(k-1)d)

For indicator functions of A, this counts k-APs in A.
For the deviation function 1_A - δ, this measures the k-AP
count relative to what random density δ would produce.
-/

/-- The k-AP counting operator, defined constructively as a finite sum.
    Λ_k(f₁,...,fₖ) = E_{x,d ∈ ZMod N} ∏_{i=0}^{k-1} fᵢ(x + i·d) -/
noncomputable def kAPCount {N : ℕ} [NeZero N] (k : ℕ)
    (f : Fin k → ZMod N → ℂ) : ℂ :=
  ((N : ℂ)⁻¹) ^ 2 * ∑ x : ZMod N, ∑ d : ZMod N,
    ∏ i : Fin k, f i (x + i.val • d)

-- ============================================================
-- PART IV: Generalized von Neumann Theorem
-- ============================================================

/-
The generalized von Neumann theorem controls the k-AP count
by the Gowers U^{k-1} norm. Specifically:

  |Λ_k(f₁,...,fₖ) - E[f₁]···E[fₖ]| ≤ min_i ||fᵢ||_{U^{k-1}}

For the 1_A - δ function, this gives:
the k-AP count deviates from expected iff some ||1_A - δ||_{U^{k-1}} is large.

Proof requires the Gowers-Cauchy-Schwarz inequality (iterated
Cauchy-Schwarz over the hypercube), which is beyond current scope.
-/

/-- Generalized von Neumann: the k-AP count is controlled by U^{k-1}. -/

-- ============================================================
-- PART V: The Inverse Theorem
-- ============================================================

/-
The inverse theorem for Gowers norms states:
  If ||f||_{U^s} ≥ δ (f is not U^s-uniform),
  then f correlates with a structured function (nilsequence).

For s = 2 (Roth's theorem):
  ||f||_{U^2} ≥ δ ⟹ f correlates with a linear phase e(αx)
  (This is the "large Fourier coefficient" step in the k=3 proof.)

For s = 3 (k=4):
  ||f||_{U^3} ≥ δ ⟹ f correlates with a quadratic phase e(αx² + βx)
  (Gowers 1998, Green-Tao 2008)

For general s:
  ||f||_{U^s} ≥ δ ⟹ f correlates with a degree-(s-1) nilsequence
  (Green-Tao-Ziegler 2012)

Not axiomatized: a meaningful statement requires nilmanifold
infrastructure that is not yet available in Mathlib.
-/

-- ============================================================
-- PART VI: Density Increment for k-APs
-- ============================================================

/-
The density increment argument for k-APs:

1. Let A ⊂ [N] have density δ with no k-AP.
2. By generalized von Neumann, ||1_A - δ||_{U^{k-1}} ≥ c(δ).
3. By the inverse theorem, 1_A correlates with a structured function.
4. This structured function provides a subprogression where A has
   density ≥ δ + g(δ) for some g(δ) > 0.
5. Iterate: density cannot exceed 1, so A must eventually contain a k-AP.

For k=3: g(δ) = δ²/100 (explicit, from Fourier analysis).
For k≥4: g(δ) = c(δ, k) (non-explicit, depends on inverse theorem bounds).
-/

/-- Density increment for k-APs: if A has no k-AP, density increases
    on a subprogression, and the restriction remains k-AP-free.

    The AP-free condition on A' is essential for iteration: A' is
    the restriction of A to an arithmetic progression, so inherits
    the k-AP-free property. Without this, the density increment
    cannot be iterated to prove Szemerédi's theorem. -/
axiom density_increment_kAP (N k : ℕ) [NeZero N] (hk : k ≥ 3) (hN : N ≥ 2)
    (A : Finset (ZMod N)) (δ : ℝ)
    (hδ : δ = A.card / N)
    (hδ_pos : 0 < δ)
    (hno_kAP : IsKAPFreeZMod A k) :
    ∃ (M : ℕ) (_ : 0 < M) (_ : M < N),
      ∃ (A' : Finset (ZMod M)) (δ' : ℝ),
        δ' = A'.card / M ∧ δ' > δ ∧ IsKAPFreeZMod A' k

-- ============================================================
-- PART VII: Connection to Szemerédi's Theorem
-- ============================================================

/-- Szemerédi's theorem follows from density increment by iteration.
    The density is bounded by 1, so the process must terminate,
    producing a k-AP.

    With the AP-free condition now in `density_increment_kAP`, the
    remaining blocker is a quantitative lower bound on the density
    increase: δ' ≥ δ + g(δ,k) for some g with g(δ) > 0 on (0, 1].
    Without this, the density might increase by amounts converging to 0,
    and N might reach 1 before density exceeds 1.

    For k=3, g(δ) = δ²/100 (proved in `density_increment_k3_explicit`).
    For k≥4, the bound involves tower functions (Gowers 2001).

    Proof: rather than iterate `density_increment_kAP` (which would also
    require a quantitative lower bound `δ' ≥ δ + g(δ,k)`), we directly
    transfer `Szemeredi.szemeredi_theorem` from `Finset ℕ` (subset of
    `Finset.range N`) to `Finset (ZMod N)` via `ZMod.val`. The image
    `A.image ZMod.val` is a subset of `Finset.range N` of the same
    cardinality (since `ZMod.val` is injective for `N ≥ 1`), so the
    density assumption transfers. The k-AP `(a, a+d, …, a+(k-1)d)` in
    `ℕ` then lifts back to a k-AP in `ZMod N`: since
    `a + (k-1)·d < N`, every term `a + i·d` lies in `[0, N)` and so its
    image under `Nat.cast : ℕ → ZMod N` has the same val. This shows
    membership of the lifted AP in `A` and gives `(d : ZMod N) ≠ 0`
    from `0 < d < N`. -/
theorem szemeredi_from_density_increment (k : ℕ) (hk : k ≥ 3) :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ A : Finset (ZMod N), A.card ≥ δ * N →
        ¬IsKAPFreeZMod A k := by
  intro δ hδ
  -- Apply the assembled Szemerédi theorem (k=1,2 trivial; k=3 Roth via
  -- Mathlib's corner theorem; k≥4 axiomatized in `Szemeredi.szemeredi_k_ge_4`).
  obtain ⟨N₀, hN₀⟩ :=
    Szemeredi.szemeredi_theorem k δ (by omega) hδ
  -- Inflate the threshold so that `N ≥ 1` is automatic. (Even when
  -- `N₀ = 0`, the case `N = 0` is vacuously handled by density: any
  -- `A : Finset (ZMod 0)` has `δ * 0 = 0` and the conclusion follows
  -- directly, but lifting to `Finset.range 0 = ∅` requires `N ≥ 1`.)
  refine ⟨max N₀ 1, ?_⟩
  intro N hN A hA_card hAPFree
  have hN_ge : N ≥ N₀ := le_of_max_le_left hN
  have hN_pos : 0 < N := by
    have h1 : 1 ≤ max N₀ 1 := le_max_right _ _
    omega
  haveI : NeZero N := ⟨by omega⟩
  -- Lift A : Finset (ZMod N) to S := A.image ZMod.val ⊆ Finset.range N.
  have hS_sub : A.image (fun x : ZMod N => x.val) ⊆ Finset.range N := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, _, rfl⟩
    exact Finset.mem_range.mpr (ZMod.val_lt y)
  have hS_card :
      (A.image (fun x : ZMod N => x.val)).card = A.card :=
    Finset.card_image_of_injective _ (ZMod.val_injective N)
  have hS_density :
      ((A.image (fun x : ZMod N => x.val)).card : ℝ) ≥ δ * N := by
    rw [hS_card]; exact hA_card
  -- Apply the Szemerédi conclusion in ℕ to get a k-AP `(a, a+d, …, a+(k-1)d)`
  -- inside `A.image ZMod.val`.
  obtain ⟨a, d, hd_pos, hAP_in_S⟩ :=
    hN₀ N hN_ge (A.image (fun x : ZMod N => x.val)) hS_sub hS_density
  -- The last term `a + (k-1)·d` lies in `Finset.range N`, hence < N.
  have hk_pos : 0 < k := by omega
  have h_km1_lt_k : k - 1 < k := Nat.sub_lt hk_pos Nat.one_pos
  have h_last_in_S : a + (k - 1) * d ∈ A.image (fun x : ZMod N => x.val) :=
    hAP_in_S (k - 1) h_km1_lt_k
  have h_last_lt_N : a + (k - 1) * d < N :=
    Finset.mem_range.mp (hS_sub h_last_in_S)
  -- d < N: since k ≥ 3 ⇒ k - 1 ≥ 2 ≥ 1, we have `d ≤ (k-1)·d ≤ a + (k-1)·d < N`.
  have h_one_le_km1 : 1 ≤ k - 1 := by omega
  have h_d_le : d ≤ (k - 1) * d := Nat.le_mul_of_pos_left d h_one_le_km1
  have h_d_lt_N : d < N := by omega
  -- Therefore `(d : ZMod N) ≠ 0`: if it were zero then `N ∣ d`, but
  -- `0 < d < N` rules this out.
  have h_d_ne_zero : (d : ZMod N) ≠ 0 := by
    intro h0
    have hdvd : (N : ℕ) ∣ d := (ZMod.natCast_zmod_eq_zero_iff_dvd d N).mp h0
    have := Nat.le_of_dvd hd_pos hdvd
    omega
  -- Lift the AP back to ZMod N. For each `i : Fin k`, the i-th term
  -- `a + i·d < N` (since `i ≤ k-1`), and its `Nat.cast` matches the
  -- ZMod expression `↑a + i.val • ↑d`.
  refine hAPFree (a : ZMod N) (d : ZMod N) h_d_ne_zero (fun i => ?_)
  have h_i_lt_k : (i : ℕ) < k := i.isLt
  have h_i_le_km1 : (i : ℕ) ≤ k - 1 := by omega
  have h_id_le : (i : ℕ) * d ≤ (k - 1) * d := Nat.mul_le_mul_right d h_i_le_km1
  have h_term_lt_N : a + (i : ℕ) * d < N := by omega
  have h_term_in_S :
      a + (i : ℕ) * d ∈ A.image (fun x : ZMod N => x.val) :=
    hAP_in_S i.val h_i_lt_k
  rcases Finset.mem_image.mp h_term_in_S with ⟨y, hy_in_A, hy_val⟩
  -- Show y = (a : ZMod N) + i.val • (d : ZMod N).
  have h_cast :
      ((a + (i : ℕ) * d : ℕ) : ZMod N) = (a : ZMod N) + (i : ℕ) • (d : ZMod N) := by
    rw [nsmul_eq_mul]; push_cast; ring
  have h_y_val_target :
      y.val = (((a : ZMod N) + (i : ℕ) • (d : ZMod N)) : ZMod N).val := by
    rw [hy_val, ← h_cast, ZMod.val_natCast_of_lt h_term_lt_N]
  have h_y_eq : y = (a : ZMod N) + (i : ℕ) • (d : ZMod N) :=
    ZMod.val_injective N h_y_val_target
  rw [← h_y_eq]
  exact hy_in_A

-- ============================================================
-- PART VIII: k=3 Case (Proved from RothTheorem.lean)
-- ============================================================

/-- For k=3, the density increment is explicit: δ' ≥ δ + δ²/100,
    and the restriction is still 3-AP-free.
    Proved using the Fourier-analytic density increment in RothTheorem.lean,
    which provides APFree on the subprogression. -/
theorem density_increment_k3_explicit (N : ℕ) (hN : N ≥ 2)
    (A : Finset (ZMod N)) (δ : ℝ)
    (hδ : δ = A.card / N) (hδ_pos : 0 < δ)
    (hno_3AP : IsKAPFreeZMod A 3) :
    ∃ (M : ℕ) (_ : 0 < M) (_ : M < N),
      ∃ (A' : Finset (ZMod M)) (δ' : ℝ),
        δ' = A'.card / M ∧ δ' ≥ δ + δ ^ 2 / 100 ∧ IsKAPFreeZMod A' 3 := by
  haveI : NeZero N := ⟨by omega⟩
  have hAPFree := apFree_of_isKAPFreeZMod_three hno_3AP
  have hN' : 1 < N := by omega
  have hdensity : (A.card : ℝ) ≥ δ * N := by
    have h : δ * ↑N = ↑A.card := by rw [hδ]; field_simp
    linarith
  obtain ⟨M, B, hM_pos, hM_lt, hB_APFree, hB_dense⟩ :=
    Szemeredi.Roth.density_increment_lemma hN' A hAPFree δ hδ_pos hdensity
  exact ⟨M, hM_pos, hM_lt, B, (B.card : ℝ) / ↑M, rfl,
    (le_div_iff₀ (Nat.cast_pos.mpr hM_pos)).mpr hB_dense,
    isKAPFreeZMod_three_of_apFree hB_APFree⟩

-- ============================================================
-- PART IX: Comparison: k=3 (Fourier) vs k≥4 (Gowers)
-- ============================================================

/-
## Key Differences Between k=3 and k≥4

| Feature | k=3 (Roth) | k≥4 (Szemerédi) |
|---------|-----------|-----------------|
| Norm | U² = Fourier L⁴ | U^{k-1} (Gowers) |
| Inverse | Large Fourier coeff | Nilsequence correlation |
| Increment | δ²/100 (explicit) | c(δ,k) (tower-type) |
| Bound | N exp(-c√(log N)) | Tower(k, 1/δ) |
| Proof Length | ~1400 lines (proved) | ~5000+ lines (estimated) |

The k=3 case is special because:
1. U² norm = Fourier L⁴ norm (direct Fourier analysis)
2. The inverse theorem for U² is Parseval's identity (trivial)
3. The density increment is explicit (δ²/100)
4. No regularity lemma needed

For k≥4, the inverse theorem for U^{k-1} is a deep result requiring
ergodic theory (Host-Kra), combinatorics (Green-Tao-Ziegler), or
algebraic methods (hypergraph regularity, Gowers 2001).
-/

end RothTheoremOQ03
