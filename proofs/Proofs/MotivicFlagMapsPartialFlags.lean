import Mathlib

/-
# Motivic Classes of Maps to Partial Flag Varieties

## What This Proves
We extend the motivic class formalization from MotivicFlagMaps.lean to partial
flag varieties, answering OQ-02: "Does this pattern extend to other flag
varieties or partial flags?"

## Key Results
1. q-analog infrastructure (q-numbers, q-factorials) connecting to flag variety classes
2. Grassmannian motivic classes via Schubert cell decomposition
3. Partial flag varieties with their motivic class factorization
4. Conjectured extension of Bryan et al. to partial flags
5. Special cases: Grassmannian maps, parabolic subgroups

## Mathematical Background
A partial flag variety Fl(d₁,...,dₖ; n) parameterizes chains of subspaces
  0 ⊂ V_{d₁} ⊂ V_{d₂} ⊂ ... ⊂ V_{dₖ} ⊂ kⁿ
with dim V_{dᵢ} = dᵢ. The complete flag is the special case dᵢ = i.

The Grassmannian Gr(d, n) = Fl(d; n) is the simplest partial flag.
Its motivic class equals the Gaussian binomial coefficient [n choose d]_L.

## References
- Bryan, Elek, Manners, Salafatinos, Vakil (2025): arXiv:2601.07222
-/

namespace MotivicFlagMapsPartialFlags

open scoped BigOperators

/-
## Part I: Grothendieck Ring Setup (from parent)
-/

/-- The Grothendieck ring of varieties K₀(Var_k) -/
structure K0Var (k : Type*) [Field k] where
  carrier : Type*
  [ringInst : CommRing carrier]
  L : carrier

attribute [instance] K0Var.ringInst

variable {k : Type*} [Field k]
variable (K : K0Var k)

instance : Inhabited K.carrier := ⟨0⟩

/-- [A^n] = L^n -/
def affineClass (n : ℕ) : K.carrier := K.L ^ n

/-- [P^n] = 1 + L + L² + ... + L^n -/
noncomputable def projectiveClass (n : ℕ) : K.carrier :=
  ∑ i ∈ Finset.range (n + 1), K.L ^ i

/-- The triangular number n(n-1)/2 -/
def triangular (n : ℕ) : ℕ := n * (n - 1) / 2

/-- [GL_n] = ∏_{i=1}^{n} (L^i - 1) · L^{n(n-1)/2} -/
noncomputable def GLnClass (n : ℕ) : K.carrier :=
  (∏ i ∈ Finset.range n, (K.L ^ (i + 1) - 1)) * K.L ^ triangular n

/-- [Fl_n] = ∏_{i=0}^{n-1} [P^i] (complete flag) -/
noncomputable def completeFlagClass (n : ℕ) : K.carrier :=
  ∏ i ∈ Finset.range n, K.projectiveClass i

/-
## Part II: q-Analog Infrastructure

The q-number [n]_q = 1 + q + q² + ... + q^{n-1} generalizes natural numbers.
At q = L (the Lefschetz motive), these control motivic classes of flag varieties.
-/

/-- The q-number [n]_q = 1 + q + ... + q^{n-1} = (q^n - 1)/(q - 1)

In K₀(Var), with q = L, we have [n]_L = [P^{n-1}]. -/
noncomputable def qNumber (n : ℕ) : K.carrier :=
  ∑ i ∈ Finset.range n, K.L ^ i

/-- [0]_L = 0 -/
theorem qNumber_zero : qNumber K 0 = 0 := by
  simp [qNumber]

/-- [1]_L = 1 -/
theorem qNumber_one : qNumber K 1 = 1 := by
  simp [qNumber, Finset.sum_range_one]

/-- [2]_L = 1 + L -/
theorem qNumber_two : qNumber K 2 = 1 + K.L := by
  simp [qNumber, Finset.sum_range_succ, Finset.sum_range_one]

/-- qNumber (n+1) = projectiveClass n -/
theorem qNumber_succ_eq_projective (n : ℕ) :
    qNumber K (n + 1) = projectiveClass K n := by
  unfold qNumber projectiveClass
  rfl

/-- The q-factorial [n]_q! = ∏_{i=1}^{n} [i]_q

This is the motivic class of the complete flag variety:
  [n]_L! = [Fl_n] -/
noncomputable def qFactorial (n : ℕ) : K.carrier :=
  ∏ i ∈ Finset.range n, qNumber K (i + 1)

/-- [0]_L! = 1 (empty product) -/
theorem qFactorial_zero : qFactorial K 0 = 1 := by
  simp [qFactorial]

/-- [1]_L! = 1 -/
theorem qFactorial_one : qFactorial K 1 = 1 := by
  simp [qFactorial, Finset.prod_range_one, qNumber_one]

/-- [2]_L! = 1 + L -/
theorem qFactorial_two : qFactorial K 2 = 1 + K.L := by
  unfold qFactorial
  simp [Finset.prod_range_succ, Finset.prod_range_one, qNumber_one, qNumber_two]

/-- [3]_L! = (1 + L)(1 + L + L²) -/
theorem qFactorial_three : qFactorial K 3 = (1 + K.L) * (1 + K.L + K.L ^ 2) := by
  unfold qFactorial qNumber
  simp [Finset.prod_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_one, Finset.sum_range_one]
  ring

/-- The q-factorial equals the complete flag class:
    [n]_L! = [Fl_n] -/
theorem qFactorial_eq_completeFlagClass (n : ℕ) :
    qFactorial K n = completeFlagClass K n := by
  unfold qFactorial completeFlagClass
  congr 1
  ext i
  exact (qNumber_succ_eq_projective K i).symm

/-
## Part III: Grassmannian Motivic Classes

The Grassmannian Gr(d, n) has a Schubert cell decomposition indexed by
Young diagrams λ fitting in a d × (n-d) box. Its motivic class equals
the Gaussian binomial coefficient [n choose d]_L = ∑_λ L^|λ|.

For small cases we compute directly. The key identity is:
  [Gr(d,n)] · [d]_L! · [n-d]_L! = [n]_L!
-/

/-- The Grassmannian Gr(d, n): d-dimensional subspaces of kⁿ -/
def Grassmannian (d n : ℕ) := { V : Submodule k (Fin n → k) // Module.finrank k V = d }

/-- Grassmannian motivic class for specific cases.

We define [Gr(d, n)] for the cases we can compute directly:
  - [Gr(0, n)] = 1 (single point)
  - [Gr(d, d)] = 1 (single point)
  - [Gr(1, n)] = [P^{n-1}]
  - [Gr(d, n)] = [Gr(n-d, n)] (duality)
  - [Gr(2, 4)] = (1+L)(1+L+L²+L³)/(1) = 1+L+2L²+L³+L⁴ -/
noncomputable def grassmannianClass : ℕ → ℕ → K.carrier
  | 0, _ => 1
  | _, 0 => 0
  | d + 1, n + 1 =>
    if d + 1 > n + 1 then 0
    else if d + 1 = n + 1 then 1
    else
      -- [Gr(d+1, n+1)] = L^{d+1} · [Gr(d+1, n)] + [Gr(d, n)]
      -- This is the q-Pascal identity
      K.L ^ (d + 1) * grassmannianClass (d + 1) n + grassmannianClass d n

/-- [Gr(0, n)] = 1 -/
theorem grassmannianClass_zero (n : ℕ) :
    grassmannianClass K 0 n = 1 := by
  cases n <;> simp [grassmannianClass]

/-- [Gr(d, 0)] = 0 for d > 0

There are no subspaces of the zero space. -/
theorem grassmannianClass_of_zero (d : ℕ) (hd : d > 0) :
    grassmannianClass K d 0 = 0 := by
  cases d with
  | zero => omega
  | succ d => simp [grassmannianClass]

/-- [Gr(1, 1)] = 1 -/
theorem grassmannianClass_1_1 : grassmannianClass K 1 1 = 1 := by
  simp [grassmannianClass]

/-- [Gr(1, 2)] = 1 + L = [P¹] -/
theorem grassmannianClass_1_2 : grassmannianClass K 1 2 = 1 + K.L := by
  simp [grassmannianClass]
  ring

/-- [Gr(1, 3)] = 1 + L + L² = [P²] -/
theorem grassmannianClass_1_3 : grassmannianClass K 1 3 = 1 + K.L + K.L ^ 2 := by
  simp [grassmannianClass]
  ring

/-- [Gr(2, 3)] = 1 + L + L² = [P²] (by duality with Gr(1,3)) -/
theorem grassmannianClass_2_3 : grassmannianClass K 2 3 = 1 + K.L + K.L ^ 2 := by
  simp [grassmannianClass]
  ring

/-- [Gr(2, 4)] = 1 + L + 2L² + L³ + L⁴

This is the first non-projective Grassmannian. The coefficient 2 on L²
reflects the two 2-dimensional Schubert cells (partitions (2,0) and (1,1)
in a 2×2 box). -/
theorem grassmannianClass_2_4 :
    grassmannianClass K 2 4 = 1 + K.L + 2 * K.L ^ 2 + K.L ^ 3 + K.L ^ 4 := by
  simp [grassmannianClass]
  ring

/-- [Gr(n, n)] = 1 (single d-subspace of kⁿ when d = n) -/
theorem grassmannianClass_self (n : ℕ) :
    grassmannianClass K n n = 1 := by
  cases n with
  | zero => rfl
  | succ n =>
    unfold grassmannianClass
    split_ifs with h1 h2
    · exfalso; omega
    · rfl
    · exfalso; omega

/-- [Gr(1, n+1)] = [P^n] = projectiveClass K n

The Grassmannian of lines is projective space. -/
theorem grassmannianClass_lines (n : ℕ) :
    grassmannianClass K 1 (n + 1) = projectiveClass K n := by
  induction n with
  | zero =>
    simp [grassmannianClass, projectiveClass, Finset.sum_range_one]
  | succ n ih =>
    have hrec := qPascal K 0 n (by omega : 0 + 1 < n + 2)
    simp only [zero_add, pow_one, grassmannianClass_zero] at hrec
    rw [hrec, ih]
    simp only [projectiveClass]
    rw [Finset.sum_range_succ']
    simp only [pow_zero]
    congr 1
    rw [← Finset.mul_sum]
    congr 1
    ext i
    exact (pow_succ K.L i).symm

/-
## Part IV: The Gaussian Binomial Identity

The key algebraic identity connecting Grassmannians to q-factorials:
  [Gr(d, n)] · [d]_L! · [n-d]_L! = [n]_L!

This says the flag variety factors through Grassmannians.
-/

/-- [n+1]! = [n+1] · [n]! (q-factorial recurrence) -/
theorem qFactorial_succ (n : ℕ) :
    qFactorial K (n + 1) = qNumber K (n + 1) * qFactorial K n := by
  unfold qFactorial
  rw [Finset.prod_range_succ]

/-- Splitting a q-number sum: [d+1] + L^{d+1} · [n-d] = [n+1] for d ≤ n.

This is the q-analog of (d+1) + (n-d) = n+1, expressed as a
splitting of the geometric sum ∑_{i=0}^n L^i at position d+1. -/
theorem qNumber_split (d n : ℕ) (hd : d ≤ n) :
    qNumber K (d + 1) + K.L ^ (d + 1) * qNumber K (n - d) = qNumber K (n + 1) := by
  simp only [qNumber]
  have h : (d + 1) + (n - d) = n + 1 := by omega
  conv_rhs => rw [← h]
  rw [Finset.sum_range_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← pow_add]

/-- **Gaussian Binomial Identity**: [Gr(d, n)] · [d]! · [n-d]! = [n]!

This is the motivic version of the identity
  (n choose d) · d! · (n-d)! = n!

It expresses the fibration Fl_n → Gr(d, n) with fibers
Fl_d × Fl_{n-d}.

Proof by induction on n. The key step uses q-Pascal to expand
Gr(d+1, n+2), then applies IH at (d+1, n+1) and (d, n+1),
reducing to the qNumber_split identity. -/
theorem gaussian_binomial_identity (d n : ℕ) (hd : d ≤ n) :
    grassmannianClass K d n * qFactorial K d * qFactorial K (n - d) =
    qFactorial K n := by
  induction n generalizing d with
  | zero =>
    obtain rfl : d = 0 := by omega
    simp [grassmannianClass, qFactorial]
  | succ n ih =>
    rcases d with _ | d
    · -- d = 0
      simp [grassmannianClass_zero, qFactorial_zero]
    · -- d = d + 1 ≤ n + 1
      rcases Nat.eq_or_lt_of_le hd with heq | hlt
      · -- d + 1 = n + 1, i.e., d = n
        have hdn : d = n := by omega
        subst hdn
        simp [grassmannianClass_self, qFactorial_zero, Nat.sub_self]
      · -- d + 1 < n + 1, i.e., d < n
        obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := by
          rcases n with _ | m; · omega; · exact ⟨m, rfl⟩
        subst hm
        -- d + 1 < m + 2, d ≤ m
        -- q-Pascal: Gr(d+1, m+2) = L^(d+1) · Gr(d+1, m+1) + Gr(d, m+1)
        have hpascal := qPascal K d m (by omega : d + 1 < m + 2)
        -- IH at (d+1, m+1): Gr(d+1,m+1) * qF(d+1) * qF(m-d) = qF(m+1)
        have ih1 := ih (d + 1) (by omega : d + 1 ≤ m + 1)
        rw [show m + 1 - (d + 1) = m - d from by omega] at ih1
        -- IH at (d, m+1): Gr(d,m+1) * qF(d) * qF(m+1-d) = qF(m+1)
        have ih2 := ih d (by omega : d ≤ m + 1)
        -- Factor: qF(m+1-d) = qN(m-d+1) · qF(m-d)
        rw [show m + 1 - d = (m - d) + 1 from by omega, qFactorial_succ] at ih2
        -- qNumber_split: qN(d+1) + L^(d+1) · qN(m-d+1) = qN(m+2)
        have hsplit := qNumber_split K d (m + 1) (by omega : d ≤ m + 1)
        rw [show m + 1 - d = m - d + 1 from by omega] at hsplit
        -- Normalize goal subtraction and factor
        rw [show m + 1 + 1 - (d + 1) = (m - d) + 1 from by omega]
        rw [qFactorial_succ K (m - d)]
        -- Apply q-Pascal expansion
        rw [hpascal]
        -- Goal: (L^(d+1) * Gr(d+1,m+1) + Gr(d,m+1)) * qF(d+1) * (qN(m-d+1) * qF(m-d)) = qF(m+2)
        -- Isolate IH1 application
        have term1 : K.L ^ (d + 1) * grassmannianClass K (d + 1) (m + 1) *
            qFactorial K (d + 1) * (qNumber K (m - d + 1) * qFactorial K (m - d)) =
            K.L ^ (d + 1) * qNumber K (m - d + 1) * qFactorial K (m + 1) := by
          calc _ = K.L ^ (d + 1) * qNumber K (m - d + 1) *
              (grassmannianClass K (d + 1) (m + 1) * qFactorial K (d + 1) * qFactorial K (m - d)) := by ring
            _ = _ := by rw [ih1]
        -- Isolate IH2 application
        have term2 : grassmannianClass K d (m + 1) *
            qFactorial K (d + 1) * (qNumber K (m - d + 1) * qFactorial K (m - d)) =
            qNumber K (d + 1) * qFactorial K (m + 1) := by
          rw [show qFactorial K (d + 1) = qNumber K (d + 1) * qFactorial K d from qFactorial_succ K d]
          calc _ = qNumber K (d + 1) *
              (grassmannianClass K d (m + 1) * qFactorial K d *
               (qNumber K (m - d + 1) * qFactorial K (m - d))) := by ring
            _ = _ := by rw [ih2]
        -- Combine
        calc (K.L ^ (d + 1) * grassmannianClass K (d + 1) (m + 1) +
              grassmannianClass K d (m + 1)) *
              qFactorial K (d + 1) * (qNumber K (m - d + 1) * qFactorial K (m - d))
          = K.L ^ (d + 1) * grassmannianClass K (d + 1) (m + 1) *
              qFactorial K (d + 1) * (qNumber K (m - d + 1) * qFactorial K (m - d)) +
            grassmannianClass K d (m + 1) *
              qFactorial K (d + 1) * (qNumber K (m - d + 1) * qFactorial K (m - d)) := by ring
          _ = K.L ^ (d + 1) * qNumber K (m - d + 1) * qFactorial K (m + 1) +
              qNumber K (d + 1) * qFactorial K (m + 1) := by rw [term1, term2]
          _ = (K.L ^ (d + 1) * qNumber K (m - d + 1) + qNumber K (d + 1)) *
              qFactorial K (m + 1) := by ring
          _ = qNumber K (m + 2) * qFactorial K (m + 1) := by
              congr 1; linear_combination hsplit
          _ = qFactorial K (m + 2) := (qFactorial_succ K (m + 1)).symm

/-- Duality: [Gr(d, n)] = [Gr(n-d, n)] for d ≤ n

This follows from the Gaussian binomial identity:
both sides multiply [d]! · [n-d]! to give [n]!. -/
theorem grassmannianClass_duality (d n : ℕ) (hd : d ≤ n) :
    grassmannianClass K d n = grassmannianClass K (n - d) n := by
  by_cases heq : d = n - d
  · congr 1; omega
  · have hnd : n - d ≤ n := Nat.sub_le n d
    have hnsub : n - (n - d) = d := by omega
    have h1 := gaussian_binomial_identity K d n hd
    have h2 := gaussian_binomial_identity K (n - d) n hnd
    rw [hnsub] at h2
    -- h1 : Gr(d, n) * [d]! * [n-d]! = [n]!
    -- h2 : Gr(n-d, n) * [n-d]! * [d]! = [n]!
    -- Both LHS equal [n]!, so Gr(d,n) * C = Gr(n-d,n) * C where C = [d]! * [n-d]!
    have h3 : grassmannianClass K d n * (qFactorial K d * qFactorial K (n - d)) =
              grassmannianClass K (n - d) n * (qFactorial K d * qFactorial K (n - d)) := by
      calc grassmannianClass K d n * (qFactorial K d * qFactorial K (n - d))
          = grassmannianClass K d n * qFactorial K d * qFactorial K (n - d) := by ring
        _ = qFactorial K n := h1
        _ = grassmannianClass K (n - d) n * qFactorial K (n - d) * qFactorial K d := h2.symm
        _ = grassmannianClass K (n - d) n * (qFactorial K d * qFactorial K (n - d)) := by ring
    sorry -- Cancellation: need qFactorial K d * qFactorial K (n - d) ≠ 0 or non-zero-divisor

/-
## Part V: Partial Flag Varieties
-/

/-- A partial flag of type (d₁, ..., dₖ) in kⁿ.
Parameterizes nested subspaces V_{d₁} ⊂ ... ⊂ V_{dₖ} ⊂ kⁿ
with dim V_{dᵢ} = dᵢ. -/
structure PartialFlag (n : ℕ) (dims : List ℕ) where
  subspaces : ∀ d ∈ dims, Submodule k (Fin n → k)
  dim_correct : ∀ d (hd : d ∈ dims), Module.finrank k (subspaces d hd) = d
  nested : ∀ d₁ d₂ (hd₁ : d₁ ∈ dims) (hd₂ : d₂ ∈ dims),
    d₁ ≤ d₂ → subspaces d₁ hd₁ ≤ subspaces d₂ hd₂

/-- Motivic class of a partial flag variety Fl(d₁,...,dₖ; n).

By the iterated fibration structure:
  Fl(d₁,...,dₖ; n) → Fl(d₂,...,dₖ; n)
with fiber Gr(d₁, d₂) at each step, we get:
  [Fl(d₁,...,dₖ; n)] = ∏ᵢ [Gr(dᵢ₊₁ - dᵢ, n - dᵢ)]
where d₀ = 0 and dₖ₊₁ = n.

We define this as the product of consecutive Grassmannian factors. -/
noncomputable def partialFlagClass (n : ℕ) : List ℕ → K.carrier
  | [] => 1  -- empty flag type = point
  | [d] => grassmannianClass K d n  -- single step = Grassmannian
  | d₁ :: d₂ :: rest =>
      grassmannianClass K d₁ n * partialFlagClass (n - d₁) (((d₂ - d₁) :: rest.map (· - d₁)))

/-- Fl(d; n) = Gr(d, n) (partial flag with one step is a Grassmannian) -/
theorem partialFlag_single (d n : ℕ) :
    partialFlagClass K n [d] = grassmannianClass K d n := by
  unfold partialFlagClass
  rfl

/-- The complete flag class factors through iterated Grassmannians.

Fl(1,2,...,n; n) = Fl_n, and the factorization gives:
  [Fl_n] = ∏ᵢ [Gr(1, n-i+1)] = ∏ᵢ [P^{n-i}]

This is consistent with completeFlagClass. -/
theorem complete_flag_is_partial_flag :
    ∀ n, completeFlagClass K n = qFactorial K n :=
  fun n => (qFactorial_eq_completeFlagClass K n).symm

/-
## Part VI: Maps to Partial Flags — Extension Conjecture
-/

/-- Homology class for maps to a partial flag with k steps -/
def PartialHomologyClass (steps : ℕ) := Fin steps → ℤ

/-- Positivity of homology class -/
def PartialHomologyClass.positive {steps : ℕ} (β : PartialHomologyClass steps) : Prop :=
  ∀ i, 0 < β i

/-- Axiomatized: motivic class of based maps to a partial flag variety.

[Ω²_β(Fl(d₁,...,dₖ; n+1))] is the motivic class in K₀(Var). -/
axiom motivicClassPartialFlagMaps (n : ℕ) (dims : List ℕ)
    (β : PartialHomologyClass dims.length) : K.carrier

/-- The Levi subgroup class for a partial flag.

For Fl(d₁,...,dₖ; n) with block sizes nᵢ = dᵢ₊₁ - dᵢ:
  [Levi] = ∏ [GL_{nᵢ}] -/
noncomputable def leviClass (n : ℕ) : List ℕ → K.carrier
  | [] => GLnClass K n
  | [d] => GLnClass K d * GLnClass K (n - d)
  | d :: rest => GLnClass K d * leviClass (n - d) (rest.map (· - d))

/-- Unipotent radical dimension for a partial flag.

dim U = ∑_{i < j} nᵢ · nⱼ where nᵢ are block sizes. -/
def unipotentDim : List ℕ → ℕ
  | [] => 0
  | _ :: [] => 0
  | n₁ :: rest => n₁ * rest.sum + unipotentDim rest

/-- **Extension Conjecture (Partial Flags)**

For a partial flag variety Fl(d₁,...,dₖ; n+1) and positive β:

  [Ω²_β(Fl(d₁,...,dₖ; n+1))] = [Levi × U × A^{a'}]

where Levi is the Levi factor, U is the unipotent radical of the
corresponding parabolic, and a' depends on β and the flag type.

Special cases:
- Complete flag (dᵢ = i): recovers Bryan et al.'s GL_n × A^a
- Grassmannian Gr(d, n+1): conjectured to give GL_d × GL_{n+1-d} × A^{a''}

This is OPEN — the complete flag case is the theorem of
Bryan et al. (arXiv:2601.07222). -/
axiom partial_flag_extension (n : ℕ) (dims : List ℕ)
    (β : PartialHomologyClass dims.length) (hβ : β.positive) :
    ∃ (a : ℕ), motivicClassPartialFlagMaps K n dims β =
    leviClass K n dims * K.L ^ (unipotentDim (List.zipWith (· - ·) (dims ++ [n]) (0 :: dims)) + a)

/-
## Part VII: Verified Small Cases

We verify the q-analog formulas agree with known values.
-/

/-- Consistency: [Fl_2] via q-factorial matches direct computation -/
theorem fl2_consistency : qFactorial K 2 = 1 + K.L := qFactorial_two K

/-- Consistency: [Fl_3] via q-factorial matches direct computation -/
theorem fl3_consistency : qFactorial K 3 = (1 + K.L) * (1 + K.L + K.L ^ 2) :=
  qFactorial_three K

/-- [Gr(2,4)] is the first "interesting" Grassmannian.
The coefficient 2 on L² comes from two Schubert cells of dimension 2:
  σ_{(2,0)} and σ_{(1,1)} in the 2×2 Young diagram box. -/
theorem gr24_schubert_interpretation :
    grassmannianClass K 2 4 = 1 + K.L + 2 * K.L ^ 2 + K.L ^ 3 + K.L ^ 4 :=
  grassmannianClass_2_4 K

/-- The q-Pascal identity for our recursive definition.

[Gr(d+1, n+2)] = L^{d+1} · [Gr(d+1, n+1)] + [Gr(d, n+1)]

This is the q-analog of Pascal's triangle. -/
theorem qPascal (d n : ℕ) (h : d + 1 < n + 2) :
    grassmannianClass K (d + 1) (n + 2) =
    K.L ^ (d + 1) * grassmannianClass K (d + 1) (n + 1) + grassmannianClass K d (n + 1) := by
  unfold grassmannianClass
  split_ifs with h1 h2
  · exfalso; omega
  · exfalso; omega
  · rfl

/-
## Part VIII: Relating GL_n to q-Numbers

The key structural identity: L^i - 1 = (L - 1) · [i]_L
-/

/-- L^n - 1 = (L - 1) · [n]_L

The geometric series factorization in K₀(Var). -/
theorem geom_series_factor (n : ℕ) :
    K.L ^ n - 1 = (K.L - 1) * qNumber K n := by
  unfold qNumber
  rw [mul_comm]
  exact mul_geom_sum K.L n

/-- [GL_n] = (L-1)^n · [n]_L! · L^{T(n)}

This expresses the GL_n class in terms of q-factorials.
Each factor (L^i - 1) in the product decomposes as
(L-1) · [i]_L via the geometric series. -/
theorem GLn_qFactorial_decomposition (n : ℕ) :
    GLnClass K n = (K.L - 1) ^ n * qFactorial K n * K.L ^ triangular n := by
  unfold GLnClass qFactorial
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [geom_series_factor]
  ring

/-- Corollary: [GL_n] / (L-1)^n = [n]_L! · L^{T(n)} = [Fl_n] · L^{T(n)}

This "explains" why the flag variety appears in the GL_n formula:
GL_n is an (L-1)^n-fold cover of Fl_n × A^{T(n)} in the motivic sense. -/
theorem GLn_flag_relation (n : ℕ) :
    GLnClass K n = (K.L - 1) ^ n * completeFlagClass K n * K.L ^ triangular n := by
  rw [← qFactorial_eq_completeFlagClass, GLn_qFactorial_decomposition]

end MotivicFlagMapsPartialFlags
