/-
  Erdős Problem #1000: Generalized Totients and Diophantine Approximation

  Source: https://erdosproblems.com/1000
  Status: SOLVED (by Haight)

  Statement:
  For an infinite sequence A = {n₁ < n₂ < ⋯} of positive integers, define
  φ_A(k) as the count of 1 ≤ m ≤ n_k such that m/n_k in lowest form has
  denominator different from all previous n_j.

  Question: Does there exist A such that
    lim_{N→∞} (1/N) Σ_{k≤N} φ_A(k)/n_k = 0?

  Answer: YES (Haight), contrary to Erdős' expectation.

  Key Results:
  - Cassels (1950): liminf of Cesàro average can be 0
  - Erdős (1964): φ_A(k)/n_k cannot converge to 0; dichotomy: liminf=0 ⟹ limsup=1
  - Haight: Cesàro average CAN vanish, resolving the problem

  Axiom count: 2 (erdos_dichotomy, haight_resolution)
  Proved: erdos_no_zero_limit (from erdos_dichotomy — convergence to 0 contradicts dichotomy)
  Proved: cassels_liminf_zero (from haight_resolution via Filter.Eventually.frequently)
  Proved: naturalSeq_phiA_eq_totient (filter condition ↔ coprimality + Icc/range bridge)
  Proved: phiA_ge_totient (φ_A(k) ≥ φ(n_k) — coprime elements always pass the filter)
  Proved: densityRatio_ge_totient_ratio (ρ_A(k) ≥ φ(n_k)/n_k)
  Proved: phiA_decomposition (φ_A(k) = Σ_{e|n_k, e unused} φ(e) — exact divisor decomposition)

  Tags: number-theory, diophantine-approximation, totient-function, cesaro-averages
-/

import Mathlib
import Proofs.EulerTotientOQ04

namespace Erdos1000

open Finset Filter Topology

/- ## Part I: Core Definitions -/

/-- An increasing sequence of positive integers. -/
structure IncreasingSeq where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  pos : ∀ n, 0 < seq n

/-- The reduced denominator of m/n: when m/n is written in lowest terms,
    the denominator is n / gcd(m, n). -/
def reducedDenom (m n : ℕ) : ℕ := n / Nat.gcd m n

/-- The generalized totient φ_A(k): count of 1 ≤ m ≤ n_k such that the
    reduced denominator of m/n_k differs from all previous terms n_j (j < k). -/
noncomputable def phiA (A : IncreasingSeq) (k : ℕ) : ℕ :=
  ((Icc 1 (A.seq k)).filter (fun m =>
    ∀ j : ℕ, j < k → reducedDenom m (A.seq k) ≠ A.seq j)).card

/- ## Part II: Basic Properties -/

/-- φ_A(k) ≤ n_k: counting a subset of {1, ..., n_k}. -/
theorem phiA_le (A : IncreasingSeq) (k : ℕ) : phiA A k ≤ A.seq k := by
  unfold phiA
  calc ((Icc 1 (A.seq k)).filter _).card
      ≤ (Icc 1 (A.seq k)).card := card_filter_le _ _
    _ = _ := by rw [Nat.card_Icc]; omega

/-- φ_A(0) = n_0: no previous terms means no exclusions. -/
theorem phiA_zero (A : IncreasingSeq) : phiA A 0 = A.seq 0 := by
  unfold phiA
  have h : (Icc 1 (A.seq 0)).filter (fun m =>
      ∀ j : ℕ, j < 0 → reducedDenom m (A.seq 0) ≠ A.seq j) = Icc 1 (A.seq 0) := by
    apply filter_true_of_mem
    intro m _
    intro j hj
    omega
  rw [h, Nat.card_Icc]
  omega

/-- The density ratio ρ_A(k) = φ_A(k) / n_k ∈ ℝ. -/
noncomputable def densityRatio (A : IncreasingSeq) (k : ℕ) : ℝ :=
  (phiA A k : ℝ) / (A.seq k : ℝ)

/-- ρ_A(k) ≥ 0. -/
theorem densityRatio_nonneg (A : IncreasingSeq) (k : ℕ) :
    0 ≤ densityRatio A k :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- ρ_A(k) ≤ 1. -/
theorem densityRatio_le_one (A : IncreasingSeq) (k : ℕ) :
    densityRatio A k ≤ 1 := by
  unfold densityRatio
  rw [div_le_one (by exact_mod_cast A.pos k : (0 : ℝ) < ↑(A.seq k))]
  exact_mod_cast phiA_le A k

/-- ρ_A(0) = 1: the first density ratio is always 1. -/
theorem densityRatio_zero (A : IncreasingSeq) :
    densityRatio A 0 = 1 := by
  unfold densityRatio
  rw [phiA_zero]
  exact div_self (by exact_mod_cast (A.pos 0).ne' : (↑(A.seq 0) : ℝ) ≠ 0)

/- ## Part III: Cesàro Average -/

/-- The Cesàro average C_A(N) = (1/N) Σ_{k<N} ρ_A(k). -/
noncomputable def cesaroAvg (A : IncreasingSeq) (N : ℕ) : ℝ :=
  (∑ k ∈ range N, densityRatio A k) / N

/-- C_A(N) ≥ 0 for all N. -/
theorem cesaroAvg_nonneg (A : IncreasingSeq) (N : ℕ) :
    0 ≤ cesaroAvg A N :=
  div_nonneg (sum_nonneg fun k _ => densityRatio_nonneg A k) (Nat.cast_nonneg _)

/-- C_A(N) ≤ 1 for N > 0. -/
theorem cesaroAvg_le_one (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    cesaroAvg A N ≤ 1 := by
  unfold cesaroAvg
  rw [div_le_one (by exact_mod_cast hN : (0 : ℝ) < ↑N)]
  calc ∑ k ∈ range N, densityRatio A k
      ≤ ∑ _ ∈ range N, (1 : ℝ) := sum_le_sum fun k _ => densityRatio_le_one A k
    _ = N := by simp

/- ## Part IV: The Natural Sequence -/

/-- The natural sequence A = {1, 2, 3, ...} (0-indexed: seq(k) = k+1). -/
def naturalSeq : IncreasingSeq where
  seq := fun n => n + 1
  strictMono := fun {a b} hab => Nat.add_lt_add_right hab 1
  pos := fun _ => by omega

/-- For A = ℕ, φ_A(k) equals Euler's totient φ(k+1).
    The reduced denominator of m/(k+1) is (k+1)/gcd(m, k+1).
    This is in {1,...,k} iff gcd(m, k+1) > 1 (i.e., m not coprime to k+1).
    So φ_A(k) = #{m ≤ k+1 : gcd(m, k+1) = 1} = φ(k+1).

    Proof: For k=0, phiA = 1 = totient(1) by phiA_zero.
    For k≥1 with n=k+2≥2: the filter condition "n/gcd(m,n) ∉ {1,...,n-1}"
    is equivalent to gcd(m,n)=1 (since n/gcd is a divisor of n in [1,n],
    and it equals n iff gcd=1). Then we bridge (Icc 1 n).filter to
    (range n).filter by showing 0 and n are both non-coprime to n≥2. -/
theorem naturalSeq_phiA_eq_totient (k : ℕ) :
    phiA naturalSeq k = Nat.totient (k + 1) := by
  rcases k with _ | k
  · -- k = 0: phiA naturalSeq 0 = 1 = totient 1
    rw [phiA_zero]; native_decide
  · -- k ≥ 1: n = k + 2 ≥ 2
    unfold phiA reducedDenom
    dsimp [naturalSeq]
    -- Step 1: The filter condition "n/gcd(m,n) ≠ j+1 for all j < k+1"
    -- is equivalent to gcd(m, n) = 1
    have hfilt : ∀ m ∈ Icc 1 (k + 2),
        (∀ j : ℕ, j < k + 1 → (k + 2) / Nat.gcd m (k + 2) ≠ j + 1) ↔
        Nat.gcd m (k + 2) = 1 := by
      intro m _
      constructor
      · -- Forward: if n/gcd avoids {1,...,n-1}, then gcd = 1
        intro h
        by_contra hne
        -- gcd ≠ 0 (since n > 0) and gcd ≠ 1, so gcd ≥ 2
        have hg_ne : Nat.gcd m (k + 2) ≠ 0 := by
          intro heq; exact absurd (Nat.gcd_eq_zero_iff.mp heq).2 (by omega)
        -- n/gcd < n (since gcd > 1) and n/gcd ≥ 1 (since gcd divides n)
        have hdiv_lt : (k + 2) / Nat.gcd m (k + 2) < k + 2 :=
          Nat.div_lt_self (by omega) (by omega)
        have hdiv_pos : 0 < (k + 2) / Nat.gcd m (k + 2) :=
          Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right m (k + 2))) (by omega)
        -- So n/gcd ∈ {1,...,k+1}, contradicting h with j = n/gcd - 1
        exact h ((k + 2) / Nat.gcd m (k + 2) - 1) (by omega) (by omega)
      · -- Backward: if gcd = 1, then n/gcd = n = k+2 > j+1 for all j < k+1
        intro hg j hj
        rw [hg, Nat.div_one]; omega
    rw [filter_congr hfilt]
    -- Step 2: Bridge (Icc 1 n).filter (gcd · n = 1) to (range n).filter (gcd n · = 1)
    -- For n ≥ 2: gcd(n,n) = n ≠ 1 and gcd(n,0) = n ≠ 1, so 0 and n are excluded
    -- from both filters, and the coprime elements in {1,...,n-1} are the same.
    suffices h : (Icc 1 (k + 2)).filter (fun m => Nat.gcd m (k + 2) = 1) =
                 (Finset.range (k + 2)).filter (fun m => Nat.gcd (k + 2) m = 1) by
      rw [h]; rfl
    ext m
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · -- Icc → range: m ≤ n ∧ gcd(m,n)=1 → m < n (since gcd(n,n)=n≠1)
      rintro ⟨⟨hm1, hmn⟩, hg⟩
      refine ⟨?_, by rwa [Nat.gcd_comm]⟩
      rcases eq_or_lt_of_le hmn with rfl | h
      · rw [Nat.gcd_self] at hg; omega
      · exact h
    · -- range → Icc: m < n ∧ gcd(n,m)=1 → 1 ≤ m (since gcd(n,0)=n≠1)
      rintro ⟨hmn, hg⟩
      rw [Nat.gcd_comm] at hg
      refine ⟨⟨?_, le_of_lt hmn⟩, hg⟩
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp [Nat.gcd_zero_left] at hg
      · exact h

/- ## Part IV-B: Structural Lower Bound -/

/-- For n ≥ 2 and m coprime to n, m is in {1,...,n} and the reduced denominator
    n/gcd(m,n) = n exceeds all previous sequence terms. So coprime elements
    in range(n) are a subset of the phiA filter set. -/
private lemma coprime_range_subset_phiA_filter (A : IncreasingSeq) (k : ℕ)
    (hn : 2 ≤ A.seq (k + 1)) :
    (Finset.range (A.seq (k + 1))).filter (Nat.Coprime (A.seq (k + 1))) ⊆
    (Icc 1 (A.seq (k + 1))).filter (fun m =>
      ∀ j : ℕ, j < k + 1 → reducedDenom m (A.seq (k + 1)) ≠ A.seq j) := by
  intro m hm
  simp only [mem_filter, mem_range] at hm
  obtain ⟨hm_lt, hm_cop⟩ := hm
  simp only [mem_filter, mem_Icc]
  refine ⟨⟨?_, le_of_lt hm_lt⟩, ?_⟩
  · -- 1 ≤ m: since Coprime n m and n ≥ 2, m ≠ 0
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp [Nat.Coprime] at hm_cop; omega
    · exact hpos
  · -- ∀ j < k+1, reducedDenom m n ≠ A.seq j
    intro j hj
    unfold reducedDenom
    -- gcd(m, n) = 1 since Coprime n m means gcd(n, m) = 1
    have hgcd : Nat.gcd m (A.seq (k + 1)) = 1 := by rwa [Nat.gcd_comm]
    rw [hgcd, Nat.div_one]
    -- A.seq (k+1) > A.seq j since j < k+1
    exact Nat.ne_of_gt (A.strictMono (by omega))

/-- Key structural lemma: φ_A(k) ≥ φ(n_k) for any increasing sequence A.
    Every m coprime to n_k has reduced denominator n_k, which exceeds all
    previous terms n_j (j < k). So coprime elements always pass the filter.
    This lower bound is the foundation for Erdős' no-zero-limit theorem. -/
theorem phiA_ge_totient (A : IncreasingSeq) (k : ℕ) :
    Nat.totient (A.seq k) ≤ phiA A k := by
  rcases k with _ | k
  · -- k = 0: phiA = n₀ ≥ totient(n₀)
    rw [phiA_zero]
    exact Nat.totient_le _
  · -- k ≥ 1: n = A.seq (k+1) ≥ 2
    unfold phiA
    have hn : 2 ≤ A.seq (k + 1) := by
      have h0 : 0 < A.seq 0 := A.pos 0
      have h1 : A.seq 0 < A.seq (k + 1) := A.strictMono (by omega)
      omega
    -- totient n = card of (range n).filter(Coprime n) by definition
    -- This is ⊆ the phiA filter set, so card inequality follows
    exact Finset.card_le_card (coprime_range_subset_phiA_filter A k hn)

/-- The density ratio ρ_A(k) is bounded below by φ(n_k)/n_k.
    Real-valued corollary of phiA_ge_totient. -/
theorem densityRatio_ge_totient_ratio (A : IncreasingSeq) (k : ℕ) :
    (Nat.totient (A.seq k) : ℝ) / (A.seq k : ℝ) ≤ densityRatio A k := by
  unfold densityRatio
  apply div_le_div_of_nonneg_right
  · exact_mod_cast phiA_ge_totient A k
  · exact Nat.cast_nonneg _

/- ## Part IV-C: Exact Divisor Decomposition -/

/-- The reduced denominator n/gcd(m,n) equals e iff gcd(m,n) = n/e,
    when e divides n and both are positive. -/
private lemma reducedDenom_eq_iff_gcd {m n e : ℕ} (hn : 0 < n) (he : 0 < e)
    (hd : e ∣ n) : reducedDenom m n = e ↔ Nat.gcd m n = n / e := by
  unfold reducedDenom
  constructor
  · intro h
    have hg_dvd := Nat.gcd_dvd_right m n
    have hne : Nat.gcd m n * e = n := by
      have h1 := Nat.div_mul_cancel hg_dvd
      rw [h] at h1
      linarith [mul_comm (Nat.gcd m n) e]
    have h1 := Nat.mul_div_cancel (Nat.gcd m n) he -- gcd * e / e = gcd
    have h2 : Nat.gcd m n * e / e = n / e := by rw [hne]
    linarith
  · intro h
    rw [h]
    -- Goal: n / (n / e) = e
    have hde := Nat.div_mul_cancel hd -- n / e * e = n
    have hd_pos : 0 < n / e := Nat.div_pos (Nat.le_of_dvd hn hd) he
    calc n / (n / e) = n / e * e / (n / e) := by congr 1; exact hde.symm
      _ = e := Nat.mul_div_cancel_left e hd_pos

/-- The reduced denominator of any m divides n (when n > 0). -/
private lemma reducedDenom_dvd (m n : ℕ) : reducedDenom m n ∣ n :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m n)

/-- For e ≥ 2 with e | n: the Icc-based gcd filter equals the range-based gcdClass.
    Both exclude 0 and n (which have gcd = n ≠ n/e when e ≥ 2). -/
private lemma Icc_filter_gcd_eq_gcdClass (n e : ℕ) (hn : 0 < n)
    (hd : e ∣ n) (he2 : 2 ≤ e) :
    (Icc 1 n).filter (fun m => Nat.gcd m n = n / e) =
    EulerTotientOQ04.gcdClass n (n / e) := by
  have hd_lt : n / e < n := Nat.div_lt_self hn (by omega)
  ext m; simp only [mem_filter, mem_Icc, EulerTotientOQ04.mem_gcdClass]
  constructor
  · rintro ⟨⟨_, hmn⟩, hg⟩
    exact ⟨by rcases eq_or_lt_of_le hmn with rfl | h
              · rw [Nat.gcd_self] at hg; omega
              · exact h, hg⟩
  · rintro ⟨hm_lt, hg⟩
    refine ⟨⟨?_, le_of_lt hm_lt⟩, hg⟩
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp [Nat.gcd_zero_left] at hg; omega
    · exact h

/-- Cardinality of the reduced-denominator class:
    |{m ∈ Icc 1 n : reducedDenom m n = e}| = φ(e) for e | n.
    For e ≥ 2, bridges to gcdClass via EulerTotientOQ04.
    For e = 1, the class is {n} with cardinality 1 = φ(1). -/
private lemma card_Icc_filter_reducedDenom_eq (n e : ℕ) (hn : 0 < n) (he : 0 < e)
    (hd : e ∣ n) :
    ((Icc 1 n).filter (fun m => reducedDenom m n = e)).card = Nat.totient e := by
  have hfilt : ∀ m ∈ Icc 1 n, (reducedDenom m n = e ↔ Nat.gcd m n = n / e) :=
    fun m _ => reducedDenom_eq_iff_gcd hn he hd
  rw [Finset.filter_congr hfilt]
  rcases le_or_gt 2 e with he2 | he_lt
  · -- e ≥ 2: bridge to gcdClass
    have hd_pos : 0 < n / e := Nat.div_pos (Nat.le_of_dvd hn hd) he
    have hd_dvd : (n / e) ∣ n := Nat.div_dvd_of_dvd hd
    rw [Icc_filter_gcd_eq_gcdClass n e hn hd he2,
        EulerTotientOQ04.card_gcdClass_eq_totient n (n / e) hn hd_pos hd_dvd]
    -- Goal: Nat.totient (n / (n / e)) = Nat.totient e
    -- Need: n / (n / e) = e
    have hde := Nat.div_mul_cancel hd
    congr 1
    calc n / (n / e) = n / e * e / (n / e) := by congr 1; exact hde.symm
      _ = e := Nat.mul_div_cancel_left e hd_pos
  · -- e = 1 (since 0 < e and e < 2)
    have he1 : e = 1 := by omega
    subst he1
    -- gcd(m, n) = n/1 = n iff m = n in Icc 1 n
    have : (Icc 1 n).filter (fun m => Nat.gcd m n = n / 1) = {n} := by
      rw [Nat.div_one]; ext m; simp only [mem_filter, mem_Icc, mem_singleton]
      constructor
      · rintro ⟨⟨_, hmn⟩, hg⟩
        exact Nat.le_antisymm hmn (Nat.le_of_dvd (by omega) (hg ▸ Nat.gcd_dvd_left m n))
      · rintro rfl; exact ⟨⟨by omega, le_refl _⟩, Nat.gcd_self _⟩
    rw [this, card_singleton]
    native_decide -- Nat.totient 1 = 1

/-- **Exact Divisor Decomposition of φ_A**:

    φ_A(k) = Σ_{e | n_k, e unused} φ(e)

    The generalized totient equals the sum of Euler's totient over divisors
    of n_k that don't appear as earlier terms in the sequence.

    Proof: partition Icc 1 n_k by reduced-denominator value. Each class for
    divisor e has φ(e) elements (via the bijection m ↦ m/(n_k/e)). The phiA
    filter keeps exactly those classes whose divisor e is "unused" — not
    equal to any previous sequence term.

    This structural theorem enables analysis of all four axioms:
    - erdos_no_zero_limit via bounding the unused-divisor sum
    - erdos_dichotomy via Euler product for φ(e)/e
    - cassels_liminf_zero/haight_resolution via explicit constructions. -/
theorem phiA_decomposition (A : IncreasingSeq) (k : ℕ) :
    phiA A k = ((A.seq k).divisors.filter
      (fun e => ∀ j : ℕ, j < k → e ≠ A.seq j)).sum Nat.totient := by
  unfold phiA
  set n := A.seq k with hn_def
  set F := fun m => ∀ j : ℕ, j < k → reducedDenom m n ≠ A.seq j
  set P := fun e => ∀ j : ℕ, j < k → e ≠ A.seq j
  have hn : 0 < n := A.pos k
  -- Step 1: phiA filter = disjoint union of RD-classes over unused divisors
  have hbiUnion : (Icc 1 n).filter F =
      (n.divisors.filter P).biUnion
        (fun e => (Icc 1 n).filter (fun m => reducedDenom m n = e)) := by
    ext m; simp only [mem_filter, mem_biUnion, Nat.mem_divisors]
    constructor
    · intro ⟨hm, hF⟩
      exact ⟨reducedDenom m n, ⟨⟨reducedDenom_dvd m n, hn.ne'⟩, hF⟩, hm, rfl⟩
    · rintro ⟨e, ⟨_, hP⟩, hm, hrd⟩
      exact ⟨hm, fun j hj => hrd ▸ hP j hj⟩
  rw [hbiUnion]
  -- Step 2: card of disjoint union = sum of cards
  rw [card_biUnion (fun e₁ _ e₂ _ hne => by
    simp only [Finset.disjoint_filter]
    intro m _ h1 h2; exact absurd (h1.symm.trans h2) hne)]
  -- Step 3: each card = φ(e)
  apply Finset.sum_congr rfl
  intro e he
  simp only [mem_filter, Nat.mem_divisors] at he
  have he_pos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at he
    · exact h
  exact card_Icc_filter_reducedDenom_eq n e hn he_pos he.1.1

/-- The decomposition specializes correctly at k=0: all divisors are unused,
    recovering the identity Σ_{e | n₀} φ(e) = n₀ = phiA(A, 0). -/
theorem phiA_decomposition_zero (A : IncreasingSeq) :
    ((A.seq 0).divisors.filter
      (fun e => ∀ j : ℕ, j < 0 → e ≠ A.seq j)).sum Nat.totient = A.seq 0 := by
  have : (A.seq 0).divisors.filter (fun e => ∀ j : ℕ, j < 0 → e ≠ A.seq j) =
         (A.seq 0).divisors := by
    apply filter_true_of_mem; intro _ _; intro j hj; omega
  rw [this, Nat.sum_totient]

/-- Corollary: phiA_ge_totient follows from the decomposition, since
    n_k is always an unused divisor (strictly greater than all previous terms). -/
theorem phiA_ge_totient' (A : IncreasingSeq) (k : ℕ) :
    Nat.totient (A.seq k) ≤ phiA A k := by
  rw [phiA_decomposition]
  apply Finset.single_le_sum (fun e _ => Nat.zero_le _)
  simp only [mem_filter, Nat.mem_divisors]
  exact ⟨⟨dvd_refl _, (A.pos k).ne'⟩,
    fun j hj => Nat.ne_of_gt (A.strictMono (by omega))⟩

/- ## Part IV-D: Complement Formula and Used-Divisor Bounds -/

/-- The sum of totients over "used" divisors of n_k —
    those that appear as a previous term A.seq j for some j < k. -/
noncomputable def usedSum (A : IncreasingSeq) (k : ℕ) : ℕ :=
  ((A.seq k).divisors.filter
    (fun e => ∃ j : ℕ, j < k ∧ e = A.seq j)).sum Nat.totient

/-- Complement formula: φ_A(k) + usedSum(k) = n_k.
    The unused and used divisors partition all divisors of n_k,
    and ∑_{e | n} φ(e) = n (Gauss' identity). -/
theorem phiA_add_usedSum (A : IncreasingSeq) (k : ℕ) :
    phiA A k + usedSum A k = A.seq k := by
  rw [phiA_decomposition]
  unfold usedSum
  -- The unused and used filters partition the divisors
  have hpart : (A.seq k).divisors.filter (fun e => ∀ j, j < k → e ≠ A.seq j)
             ∪ (A.seq k).divisors.filter (fun e => ∃ j, j < k ∧ e = A.seq j)
             = (A.seq k).divisors := by
    ext e; simp only [mem_union, mem_filter, Nat.mem_divisors]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hex : ∃ j, j < k ∧ e = A.seq j
      · right; exact ⟨h, hex⟩
      · left; push_neg at hex; exact ⟨h, hex⟩
  have hdisj : Disjoint
    ((A.seq k).divisors.filter (fun e => ∀ j, j < k → e ≠ A.seq j))
    ((A.seq k).divisors.filter (fun e => ∃ j, j < k ∧ e = A.seq j)) := by
    rw [Finset.disjoint_filter]
    intro e _ h1 ⟨j, hj, heq⟩
    exact h1 j hj heq
  rw [← Finset.sum_union hdisj, hpart, Nat.sum_totient]

/-- usedSum(k) ≤ n_k - φ_A(k). Direct from the complement formula. -/
theorem usedSum_le (A : IncreasingSeq) (k : ℕ) :
    usedSum A k ≤ A.seq k - phiA A k :=
  Nat.le_sub_of_add_le (by linarith [phiA_add_usedSum A k])

/-- φ_A(k) ≥ 1 for all k: n_k is always an unused divisor with φ(n_k) ≥ 1. -/
theorem phiA_pos (A : IncreasingSeq) (k : ℕ) :
    1 ≤ phiA A k := by
  have := phiA_ge_totient A k
  have := Nat.totient_pos (A.pos k)
  omega

/-- ρ_A(k) > 0 for all k. -/
theorem densityRatio_pos (A : IncreasingSeq) (k : ℕ) :
    0 < densityRatio A k := by
  unfold densityRatio
  apply div_pos
  · exact Nat.cast_pos.mpr (phiA_pos A k)
  · exact Nat.cast_pos.mpr (A.pos k)

/-- The density ratio via the complement formula:
    ρ_A(k) = 1 - usedSum(k) / n_k. -/
theorem densityRatio_complement (A : IncreasingSeq) (k : ℕ) :
    densityRatio A k = 1 - (usedSum A k : ℝ) / (A.seq k : ℝ) := by
  unfold densityRatio
  have hn : (A.seq k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (A.pos k).ne'
  rw [eq_sub_iff_add_eq, div_add_div_same, ← Nat.cast_add, phiA_add_usedSum]
  exact div_self hn

/-- At most k divisors of n_k can be "used" — each maps to a unique j < k
    via the injectivity of the sequence A. -/
theorem usedDivisors_card_le (A : IncreasingSeq) (k : ℕ) :
    ((A.seq k).divisors.filter (fun e => ∃ j, j < k ∧ e = A.seq j)).card ≤ k := by
  -- Each used divisor maps to some j < k, and different divisors map to different j's
  -- because A is injective (strictly monotone)
  let f : ℕ → ℕ := fun e =>
    if h : ∃ j, j < k ∧ e = A.seq j then h.choose else 0
  have hf : ∀ e ∈ (A.seq k).divisors.filter (fun e => ∃ j, j < k ∧ e = A.seq j),
      f e ∈ Finset.range k := by
    intro e he
    simp only [mem_filter] at he
    simp only [f, dif_pos he.2, Finset.mem_range]
    exact he.2.choose_spec.1
  have hinj : Set.InjOn f ↑((A.seq k).divisors.filter (fun e => ∃ j, j < k ∧ e = A.seq j)) := by
    intro e₁ he₁ e₂ he₂ heq
    simp only [Finset.coe_filter, Set.mem_sep_iff] at he₁ he₂
    simp only [f, dif_pos he₁.2, dif_pos he₂.2] at heq
    have h1 := he₁.2.choose_spec.2
    have h2 := he₂.2.choose_spec.2
    rw [h1, h2, heq]
  calc ((A.seq k).divisors.filter _).card
      ≤ (Finset.range k).card := Finset.card_le_card_of_injOn f hf hinj
    _ = k := Finset.card_range k

/-- When n_k is prime, ρ_A(k) ≥ 1/2.
    A prime p has only divisors {1, p}. Since p = n_k > n_j for j < k,
    p is unused. At worst 1 is used, giving φ_A(k) ≥ φ(p) = p-1,
    so ρ ≥ (p-1)/p ≥ 1/2. -/
theorem densityRatio_ge_of_prime (A : IncreasingSeq) (k : ℕ)
    (hp : Nat.Prime (A.seq k)) :
    1 / 2 ≤ densityRatio A k := by
  have hge := densityRatio_ge_totient_ratio A k
  have htot : Nat.totient (A.seq k) = A.seq k - 1 := Nat.totient_prime hp
  rw [htot] at hge
  have hn_pos : (0 : ℝ) < A.seq k := Nat.cast_pos.mpr (A.pos k)
  have hn_ge2 : (2 : ℝ) ≤ A.seq k := by exact_mod_cast hp.two_le
  have hcast : (↑(A.seq k - 1) : ℝ) = ↑(A.seq k) - 1 := by
    have h1 : 1 ≤ A.seq k := by have := hp.pos; omega
    rw [Nat.cast_sub h1]; norm_num
  calc (1 : ℝ) / 2 ≤ (↑(A.seq k) - 1) / ↑(A.seq k) := by
        rw [div_le_div_iff₀ (by norm_num) hn_pos]; nlinarith
    _ ≤ densityRatio A k := by rwa [← hcast]

/- ## Part V: Main Predicates -/

/-- A sequence has vanishing Cesàro average if C_A(N) → 0. -/
def VanishingAverage (A : IncreasingSeq) : Prop :=
  Tendsto (cesaroAvg A) atTop (𝓝 0)

/-- A sequence has density tending to zero if ρ_A(k) → 0. -/
def DensityToZero (A : IncreasingSeq) : Prop :=
  Tendsto (densityRatio A) atTop (𝓝 0)

/- ## Part V-B: Special Cases of No-Zero-Limit -/

/-- If a sequence contains infinitely many prime terms (∀ k, ∃ k' > k with n_{k'} prime),
    then the density ratio cannot converge to 0.
    Proof: at prime indices, ρ ≥ 1/2 (from densityRatio_ge_of_prime), so ρ → 0
    would require ρ < 1/2 eventually, a contradiction. -/
theorem not_density_zero_of_infinitely_many_primes (A : IncreasingSeq)
    (h_primes : ∀ k, ∃ k', k < k' ∧ Nat.Prime (A.seq k')) :
    ¬ DensityToZero A := by
  intro h
  -- DensityToZero means ρ → 0, so eventually ρ < 1/2
  have h12 := (tendsto_order.mp h).2 (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨K, hK⟩ := eventually_atTop.mp h12
  -- Find a prime index k' > K
  obtain ⟨k', hk'K, hk'_prime⟩ := h_primes K
  -- densityRatio ≥ 1/2 at prime index
  have hge := densityRatio_ge_of_prime A k' hk'_prime
  -- densityRatio < 1/2 at the same index (since k' > K ≥ K)
  have hlt := hK k' (le_of_lt hk'K)
  linarith

/-- The natural sequence (1, 2, 3, ...) does not have density → 0.
    Contains infinitely many primes, so not_density_zero_of_infinitely_many_primes applies. -/
theorem naturalSeq_not_density_zero : ¬ DensityToZero naturalSeq :=
  not_density_zero_of_infinitely_many_primes naturalSeq (fun k => by
    obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (k + 2)
    exact ⟨p - 1, by omega, by simp [naturalSeq]; omega⟩)

/- ## Part V-C: Complement and DensityToZero Infrastructure -/

/-- The complement of the density ratio equals the used fraction:
    1 - ρ_A(k) = usedSum(k) / n_k. -/
theorem one_sub_densityRatio (A : IncreasingSeq) (k : ℕ) :
    1 - densityRatio A k = (usedSum A k : ℝ) / (A.seq k : ℝ) := by
  rw [densityRatio_complement]; ring

/-- DensityToZero implies VanishingAverage (Cesàro mean of a convergent
    sequence converges to the same limit). Uses Mathlib's `Tendsto.cesaro`. -/
theorem densityToZero_implies_vanishing (A : IncreasingSeq) (hD : DensityToZero A) :
    VanishingAverage A := by
  show Tendsto (cesaroAvg A) atTop (𝓝 0)
  have h := hD.cesaro
  -- h : Tendsto (fun n => (↑n)⁻¹ * ∑ i ∈ range n, densityRatio A i) atTop (𝓝 0)
  -- cesaroAvg A N = (∑ k ∈ range N, densityRatio A k) / ↑N = ↑N⁻¹ * ∑ ...
  exact h.congr fun N => by unfold cesaroAvg; rw [div_eq_inv_mul]

/- ## Part VI: Erdős' Results (1964) -/

/-- Erdős' Dichotomy: If the density ratio gets arbitrarily close to 0,
    then it also gets arbitrarily close to 1.
    Proof uses the Euler product formula for φ(n)/n and smooth numbers. -/
axiom erdos_dichotomy (A : IncreasingSeq) :
    (∀ ε > 0, ∃ᶠ k in atTop, densityRatio A k < ε) →
    (∀ ε > 0, ∃ᶠ k in atTop, 1 - ε < densityRatio A k)

/-- Erdős' No-Zero-Limit Theorem: The density ratio ρ_A(k) = φ_A(k)/n_k
    cannot converge to 0 for any sequence A. This is stronger than
    not_density_zero_of_infinitely_many_primes: it works even for
    sequences with no prime terms (e.g., composite numbers only).

    Proof: If ρ → 0, then ρ < ε for all ε > 0 eventually, hence frequently.
    By erdos_dichotomy, ρ > 1 - ε frequently. Taking ε = 1/2 gives
    ρ < 1/2 eventually but ρ > 1/2 frequently — contradiction. -/
theorem erdos_no_zero_limit (A : IncreasingSeq) : ¬ DensityToZero A := by
  intro hDZ
  -- ρ → 0 gives ρ < ε frequently (eventually implies frequently)
  have h_freq : ∀ ε > 0, ∃ᶠ k in atTop, densityRatio A k < ε :=
    fun ε hε => (hDZ (Iio_mem_nhds hε)).frequently
  -- Dichotomy: frequently near 0 ⟹ frequently near 1
  have h1 := erdos_dichotomy A h_freq (1/2) (by norm_num)
  -- But ρ → 0 gives eventually ρ < 1/2
  have h2 : ∀ᶠ k in atTop, densityRatio A k < 1/2 :=
    hDZ (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  -- Contradiction: frequently(ρ > 1/2) vs eventually(ρ < 1/2)
  exact h1 (h2.mono fun k hk hge => by linarith)

/- ## Part VII: Cassels' Result (1950) -/

/- ## Part VIII: Haight's Resolution -/

/-- Haight's Theorem (resolves Erdős' Problem #1000):
    There exists a sequence A such that the Cesàro average converges to 0.
    Construction uses rapidly growing highly composite numbers to force
    the average to zero while individual terms oscillate.
    This contradicts Erdős' conjecture that no such sequence exists. -/
axiom haight_resolution : ∃ A : IncreasingSeq, VanishingAverage A

/-- Cassels' theorem: There exists a sequence A such that
    the liminf of the Cesàro average is 0.
    Proved as a corollary of Haight's stronger result: if the average
    converges to 0 (VanishingAverage), then it visits near 0 frequently.
    Uses Filter.Eventually.frequently with atTop.NeBot. -/
theorem cassels_liminf_zero :
    ∃ A : IncreasingSeq, ∀ ε > 0, ∃ᶠ N in atTop, cesaroAvg A N < ε := by
  obtain ⟨A, hA⟩ := haight_resolution
  exact ⟨A, fun ε hε => (hA (Iio_mem_nhds hε)).frequently⟩

/- ## Part IX: Corollaries -/

/-- If the Cesàro average vanishes, the density ratio visits near 0 frequently.
    Contrapositive: if ρ ≥ ε eventually, the Cesàro average converges to
    a value ≥ ε, contradicting convergence to 0.
    The formal argument splits the sum at the threshold index K
    and uses the lower bound ε·(N−K)/N → ε. -/
theorem vanishing_avg_visits_zero (A : IncreasingSeq) (hV : VanishingAverage A)
    (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in atTop, densityRatio A k < ε := by
  by_contra h
  rw [Filter.not_frequently] at h
  -- h : ∀ᶠ k in atTop, ¬ (densityRatio A k < ε)
  have hev : ∀ᶠ k in atTop, ε ≤ densityRatio A k := h.mono fun k hk => le_of_not_gt hk
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  -- VanishingAverage: eventually C_A(N) < ε/2
  have hV2 : ∀ᶠ N in atTop, cesaroAvg A N < ε / 2 := by
    have hmem : Set.Iio (ε / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (half_pos hε)
    have hpre := hV hmem
    -- hpre : cesaroAvg A ⁻¹' Iio (ε/2) ∈ atTop
    exact hpre
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hV2
  -- Take N large enough
  have hN_bound : 2 * K + 1 ≤ max (2 * K + 1) N₀ := le_max_left _ _
  have hN0_bound : N₀ ≤ max (2 * K + 1) N₀ := le_max_right _ _
  set N := max (2 * K + 1) N₀ with hN_def
  have hNK : K < N := by omega
  have hKleN : K ≤ N := Nat.le_of_lt hNK
  have hNpos : (0 : ℕ) < N := by omega
  -- C_A(N) < ε/2
  have h1 : cesaroAvg A N < ε / 2 := hN₀ N hN0_bound
  -- C_A(N) ≥ ε/2 (from the lower bound on the sum)
  have h2 : ε / 2 ≤ cesaroAvg A N := by
    have hNR : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hNpos
    -- Σ_{k<N} ρ(k) ≥ Σ_{K≤k<N} ε = (N-K)·ε ≥ N/2·ε = ε/2·N
    have hsum : ε / 2 * ↑N ≤ ∑ k ∈ range N, densityRatio A k := by
      calc ε / 2 * ↑N ≤ ↑(N - K) * ε := by
              have : (K : ℝ) ≤ (N : ℝ) / 2 := by
                have h2K : (2 * (K : ℝ) + 1 ≤ ↑N) := by exact_mod_cast hN_bound
                linarith
              rw [Nat.cast_sub hKleN]; nlinarith
        _ = ∑ _i ∈ Ico K N, ε := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ ∑ i ∈ Ico K N, densityRatio A i :=
              sum_le_sum fun i hi => hK i (mem_Ico.mp hi).1
        _ ≤ ∑ i ∈ range N, densityRatio A i := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro x hx; exact mem_range.mpr (mem_Ico.mp hx).2
              · intro i _ _; exact densityRatio_nonneg A i
    -- ε/2 ≤ Σ/N from ε/2 * N ≤ Σ and N > 0
    show ε / 2 ≤ cesaroAvg A N
    unfold cesaroAvg
    have hNne : (↑N : ℝ) ≠ 0 := hNR.ne'
    have key : ε / 2 * ↑N / ↑N ≤ (∑ k ∈ range N, densityRatio A k) / ↑N :=
      div_le_div_of_nonneg_right hsum hNR.le
    rwa [mul_div_cancel_right₀ _ hNne] at key
  linarith

/-- Haight oscillation: the sequence achieving vanishing Cesàro average
    must have its density ratio oscillate between near 0 and near 1.
    Combines haight_resolution with erdos_dichotomy. -/
theorem haight_oscillation :
    ∃ A : IncreasingSeq, VanishingAverage A ∧
      ∀ ε > 0, (∃ᶠ k in atTop, densityRatio A k < ε) ∧
               (∃ᶠ k in atTop, 1 - ε < densityRatio A k) := by
  obtain ⟨A, hA⟩ := haight_resolution
  exact ⟨A, hA, fun ε hε =>
    ⟨vanishing_avg_visits_zero A hA ε hε,
     erdos_dichotomy A (fun ε' hε' => vanishing_avg_visits_zero A hA ε' hε') ε hε⟩⟩

/-- No sequence has density → 0: a direct consequence of Erdős' theorem.
    This holds regardless of the Cesàro average's behavior. -/
theorem no_density_zero (A : IncreasingSeq) : ¬ DensityToZero A :=
  erdos_no_zero_limit A

/-- Haight's sequence provides a concrete separation between
    pointwise and Cesàro convergence: ρ_A(k) ↛ 0 yet C_A(N) → 0. -/
theorem pointwise_cesaro_gap :
    ∃ A : IncreasingSeq, VanishingAverage A ∧ ¬ DensityToZero A := by
  obtain ⟨A, hA⟩ := haight_resolution
  exact ⟨A, hA, erdos_no_zero_limit A⟩

/- ## Part X: Infrastructure Toward Proving erdos_no_zero_limit -/

/-- Helper: if ρ_A(k) ≥ c for infinitely many k (some c > 0), then ρ doesn't → 0.
    This is the standard filter-level bridge for disproving convergence. -/
theorem not_densityToZero_of_frequently_ge (A : IncreasingSeq) {c : ℝ} (hc : 0 < c)
    (hfreq : ∃ᶠ k in atTop, c ≤ densityRatio A k) : ¬ DensityToZero A := by
  intro hDZ
  have hev : ∀ᶠ k in atTop, densityRatio A k < c := hDZ (Iio_mem_nhds hc)
  exact hfreq (hev.mono fun k hk hge => absurd hge (not_le.mpr hk))

/-- Sequences with infinitely many prime terms can't have ρ → 0.
    At every prime n_k, the density ratio is ≥ 1/2 (from densityRatio_ge_of_prime). -/
theorem not_densityToZero_of_frequently_prime (A : IncreasingSeq)
    (hprime : ∃ᶠ k in atTop, Nat.Prime (A.seq k)) : ¬ DensityToZero A :=
  not_densityToZero_of_frequently_ge A (by norm_num : (0 : ℝ) < 1 / 2)
    (hprime.mono fun k hk => densityRatio_ge_of_prime A k hk)

/-- The used sum at k = 0 is 0 — there are no previous terms to use. -/
theorem usedSum_zero (A : IncreasingSeq) : usedSum A 0 = 0 := by
  classical
  unfold usedSum
  suffices h : ((A.seq 0).divisors.filter (fun e => ∃ j, j < 0 ∧ e = A.seq j)) = ∅ by
    simp [h]
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro e
  simp only [Finset.mem_filter, Nat.mem_divisors, not_and]
  intro _
  rintro ⟨j, hj, _⟩
  omega

/-- ρ_A(k) ≥ 1/n_k for all k — an absolute lower bound.
    Since φ_A(k) ≥ 1 (from phiA_pos), the ratio is at least 1/n_k. -/
theorem densityRatio_ge_inv (A : IncreasingSeq) (k : ℕ) :
    1 / (A.seq k : ℝ) ≤ densityRatio A k := by
  unfold densityRatio
  rw [div_le_div_right₀ (Nat.cast_pos.mpr (A.pos k))]
  exact_mod_cast phiA_pos A k

/-- The Cesàro average is bounded below by the average totient ratio:
    C_A(N) ≥ (1/N) Σ_{k<N} φ(n_k)/n_k.
    Consequence of the pointwise bound ρ_A(k) ≥ φ(n_k)/n_k. -/
theorem cesaroAvg_ge_totient_avg (A : IncreasingSeq) (N : ℕ) :
    (∑ k ∈ range N, (Nat.totient (A.seq k) : ℝ) / (A.seq k : ℝ)) / N
    ≤ cesaroAvg A N := by
  unfold cesaroAvg
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_div_right₀ (Nat.cast_pos.mpr hN)]
    exact Finset.sum_le_sum fun k _ => densityRatio_ge_totient_ratio A k

/-- Any subset of unused divisors of n_k gives a lower bound on φ_A(k).
    If S ⊆ divisors(n_k) and every e ∈ S is unused (≠ n_j for all j < k),
    then S.sum φ ≤ φ_A(k). Direct from phiA_decomposition. -/
theorem phiA_ge_unused_subset (A : IncreasingSeq) (k : ℕ)
    (S : Finset ℕ)
    (hS_div : S ⊆ (A.seq k).divisors)
    (hS_unused : ∀ e ∈ S, ∀ j : ℕ, j < k → e ≠ A.seq j) :
    S.sum Nat.totient ≤ phiA A k := by
  rw [phiA_decomposition]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    exact Finset.mem_filter.mpr ⟨hS_div he, hS_unused e he⟩
  · intro _ _ _; exact Nat.zero_le _

/-- Any divisor of n_k that exceeds n_{k-1} is automatically unused —
    it cannot equal any earlier term n_j (since n_j ≤ n_{k-1} for j < k).
    Together with the decomposition, this means "large" divisors
    always contribute to φ_A(k). -/
theorem divisor_gt_prev_unused (A : IncreasingSeq) (k : ℕ) (hk : 0 < k)
    (d : ℕ) (hd_dvd : d ∣ A.seq k)
    (hd_large : A.seq (k - 1) < d) :
    ∀ j : ℕ, j < k → d ≠ A.seq j := by
  intro j hj
  have : j ≤ k - 1 := by omega
  have hle : A.seq j ≤ A.seq (k - 1) := by
    rcases eq_or_lt_of_le this with rfl | h
    · exact le_refl _
    · exact le_of_lt (A.strictMono h)
  omega

/-- **Large-divisor lower bound**: φ_A(k) is at least the totient sum of
    divisors of n_k that exceed n_{k-1}. These are automatically unused
    since they're larger than all previous terms. -/
theorem phiA_ge_large_divisor_sum (A : IncreasingSeq) (k : ℕ) (hk : 0 < k) :
    ((A.seq k).divisors.filter (fun d => A.seq (k - 1) < d)).sum Nat.totient
    ≤ phiA A k := by
  rw [phiA_decomposition]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    exact ⟨hd.1, divisor_gt_prev_unused A k hk d hd.1.1 hd.2⟩
  · intro _ _ _; exact Nat.zero_le _

/-- For sequences with p-fold gaps (n_k ≥ p·n_{k-1} + 1 where p | n_k),
    both n_k and n_k/p are unused divisors, giving a combined lower bound.
    The gap condition ensures n_k/p > n_{k-1}, making n_k/p "too large"
    to be any previous sequence term. -/
theorem phiA_ge_self_and_quotient (A : IncreasingSeq) (k : ℕ) (hk : 0 < k)
    (p : ℕ) (hp : Nat.Prime p) (hp_dvd : p ∣ A.seq k)
    (hgap : A.seq (k - 1) * p < A.seq k) :
    Nat.totient (A.seq k) + Nat.totient (A.seq k / p) ≤ phiA A k := by
  -- n_k and n_k/p are distinct
  have h_ne : A.seq k ≠ A.seq k / p := by
    intro h; have := Nat.div_lt_self (A.pos k) hp.one_lt; omega
  -- Both are large (exceed n_{k-1})
  have h_nk_large : A.seq (k - 1) < A.seq k := A.strictMono (by omega)
  have h_div_large : A.seq (k - 1) < A.seq k / p := by
    have := Nat.div_mul_cancel hp_dvd
    omega
  -- Both are unused
  have h_nk_unused := divisor_gt_prev_unused A k hk (A.seq k) (dvd_refl _) h_nk_large
  have h_div_unused := divisor_gt_prev_unused A k hk (A.seq k / p)
    (Nat.div_dvd_of_dvd hp_dvd) h_div_large
  -- Apply phiA_ge_unused_subset with S = {n_k, n_k/p}
  have hsub : ({A.seq k, A.seq k / p} : Finset ℕ) ⊆ (A.seq k).divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨dvd_refl _, (A.pos k).ne'⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hp_dvd, (A.pos k).ne'⟩
  have hunused : ∀ e ∈ ({A.seq k, A.seq k / p} : Finset ℕ), ∀ j, j < k → e ≠ A.seq j := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact h_nk_unused
    · exact h_div_unused
  calc Nat.totient (A.seq k) + Nat.totient (A.seq k / p)
      = ({A.seq k, A.seq k / p} : Finset ℕ).sum Nat.totient := by
        rw [Finset.sum_pair h_ne]
    _ ≤ phiA A k := phiA_ge_unused_subset A k _ hsub hunused

/-- **Deficit-sum identity in ℝ**: The total deficit from ρ=1 equals
    the sum of usedSum(k)/n_k.
    Σ_{k<N} (1 - ρ_A(k)) = Σ_{k<N} usedSum(k) / n_k. -/
theorem sum_deficit_eq_sum_used_ratio (A : IncreasingSeq) (N : ℕ) :
    ∑ k ∈ range N, (1 - densityRatio A k) =
    ∑ k ∈ range N, (usedSum A k : ℝ) / (A.seq k : ℝ) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [densityRatio_complement]
  ring

/-- **Deficit-sum upper bound**: The total deficit is less than N.
    Since ρ_A(k) > 0, each term 1 - ρ < 1, so the sum < N.
    This means the "average deficit" is strictly less than 1. -/
theorem sum_deficit_lt (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range N, (1 - densityRatio A k) < N := by
  calc ∑ k ∈ range N, (1 - densityRatio A k)
      < ∑ _ ∈ range N, (1 : ℝ) := by
        apply Finset.sum_lt_sum
        · intro k _
          linarith [densityRatio_nonneg A k]
        · exact ⟨0, Finset.mem_range.mpr hN, by linarith [densityRatio_pos A 0]⟩
    _ = N := by simp [Finset.sum_const, Finset.card_range]

/-- **Cesàro average strictly positive**: C_A(N) > 0 for N > 0.
    The density ratio is strictly positive at every step. -/
theorem cesaroAvg_pos (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    0 < cesaroAvg A N := by
  unfold cesaroAvg
  apply div_pos
  · have h0 : (0 : ℝ) < densityRatio A 0 := densityRatio_pos A 0
    calc (0 : ℝ) < densityRatio A 0 := h0
      _ ≤ ∑ k ∈ range N, densityRatio A k := by
          apply Finset.single_le_sum
          · intro k _; exact densityRatio_nonneg A k
          · exact Finset.mem_range.mpr hN
  · exact Nat.cast_pos.mpr hN

/- ## Part XI: Growth Bound and Density Floor -/

/-- **Used-sum growth bound**: usedSum(k) ≤ k · n_{k-1} for k ≥ 1.
    Each used divisor e of n_k equals some n_j with j < k, so e ≤ n_{k-1}.
    Since φ(e) ≤ e, each term contributes at most n_{k-1}, and there
    are at most k used divisors (by usedDivisors_card_le). -/
theorem usedSum_le_card_mul (A : IncreasingSeq) (k : ℕ) (hk : 0 < k) :
    usedSum A k ≤ k * A.seq (k - 1) := by
  unfold usedSum
  -- Each φ(e) ≤ n_{k-1} for used divisors e
  have hle : ∀ e ∈ (A.seq k).divisors.filter
      (fun e => ∃ j, j < k ∧ e = A.seq j),
      Nat.totient e ≤ A.seq (k - 1) := by
    intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨_, j, hj, rfl⟩ := he
    calc Nat.totient (A.seq j) ≤ A.seq j := Nat.totient_le _
      _ ≤ A.seq (k - 1) := by
          have : j ≤ k - 1 := by omega
          rcases eq_or_lt_of_le this with rfl | h
          · exact le_refl _
          · exact le_of_lt (A.strictMono h)
  calc ((A.seq k).divisors.filter _).sum Nat.totient
      ≤ ((A.seq k).divisors.filter _).card • A.seq (k - 1) :=
        Finset.sum_le_card_nsmul _ _ _ hle
    _ = ((A.seq k).divisors.filter _).card * A.seq (k - 1) := by
        rw [smul_eq_mul]
    _ ≤ k * A.seq (k - 1) :=
        Nat.mul_le_mul_right _ (usedDivisors_card_le A k)

/-- **Density ratio growth floor**: ρ_A(k) ≥ 1 - k·n_{k-1}/n_k.
    From the complement formula and the growth bound:
    ρ = 1 - usedSum/n_k ≥ 1 - k·n_{k-1}/n_k.
    This shows that if the sequence grows faster than k·n_{k-1},
    the density ratio is bounded away from 0. -/
theorem densityRatio_ge_one_sub_growth (A : IncreasingSeq) (k : ℕ) (hk : 0 < k) :
    1 - (k : ℝ) * (A.seq (k - 1) : ℝ) / (A.seq k : ℝ) ≤ densityRatio A k := by
  rw [densityRatio_complement]
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast usedSum_le_card_mul A k hk

/-- **Fast-growth density floor**: If n_k > 2k · n_{k-1} then ρ_A(k) > 1/2.
    When the growth ratio exceeds 2k, the used divisors can capture at most
    half the totient weight, so the density ratio stays above 1/2. -/
theorem densityRatio_gt_half_of_fast_growth (A : IncreasingSeq) (k : ℕ) (hk : 0 < k)
    (hgrow : 2 * k * A.seq (k - 1) < A.seq k) :
    1 / 2 < densityRatio A k := by
  have hge := densityRatio_ge_one_sub_growth A k hk
  have hn_pos : (0 : ℝ) < A.seq k := Nat.cast_pos.mpr (A.pos k)
  have hkn : (k : ℝ) * (A.seq (k - 1) : ℝ) / (A.seq k : ℝ) < 1 / 2 := by
    rw [div_lt_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 2)]
    have hgrow_r : (↑(2 * k * A.seq (k - 1)) : ℝ) < ↑(A.seq k) :=
      Nat.cast_lt.mpr hgrow
    push_cast at hgrow_r
    linarith
  linarith

/-- **No density-to-zero for fast-growing sequences**: If the growth ratio
    n_k / (k · n_{k-1}) exceeds 2 for infinitely many k, then ρ_A(k)
    cannot converge to 0 — in fact ρ ≥ 1/2 frequently. -/
theorem not_densityToZero_of_fast_growth (A : IncreasingSeq)
    (hgrow : ∃ᶠ k in atTop, 2 * k * A.seq (k - 1) < A.seq k) :
    ¬ DensityToZero A :=
  not_densityToZero_of_frequently_ge A (by norm_num : (0 : ℝ) < 1 / 2)
    (hgrow.mono fun k hk => by
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · -- k = 0: ρ_A(0) = 1 ≥ 1/2
        linarith [densityRatio_zero A]
      · exact le_of_lt (densityRatio_gt_half_of_fast_growth A k hk_pos hk))

/-- **φ_A floor from growth**: φ_A(k) ≥ n_k - k·n_{k-1} for k ≥ 1.
    Direct from the complement formula and the growth bound. -/
theorem phiA_ge_seq_sub_growth (A : IncreasingSeq) (k : ℕ) (hk : 0 < k) :
    A.seq k - k * A.seq (k - 1) ≤ phiA A k := by
  have h1 := phiA_add_usedSum A k  -- φ_A(k) + usedSum(k) = n_k
  have h2 := usedSum_le_card_mul A k hk  -- usedSum(k) ≤ k · n_{k-1}
  omega

/- ## Part XII: Sum-Switching Identity for Double-Counting -/

/-- The set of divisibility pairs: indices (j, k) with j < k < N and n_j | n_k. -/
def divPairs (A : IncreasingSeq) (N : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter (fun p => p.1 < p.2 ∧ A.seq p.1 ∣ A.seq p.2)

/-- The fiber over k: indices j < k with n_j | n_k. This is exactly
    the set of "used divisor sources" for position k. -/
def divPairs_fiber_k (A : IncreasingSeq) (N k : ℕ) : Finset ℕ :=
  (range N).filter (fun j => j < k ∧ A.seq j ∣ A.seq k)

/-- The fiber over j: indices k > j with n_j | n_k, k < N.
    These are the later positions where n_j appears as a used divisor. -/
def divPairs_fiber_j (A : IncreasingSeq) (N j : ℕ) : Finset ℕ :=
  (range N).filter (fun k => j < k ∧ A.seq j ∣ A.seq k)

/-- **Multiplicity bound**: The number of multiples of n_j in the sequence
    up to index N is at most n_{N-1}/n_j.
    Each such n_k = q·n_j for distinct q ≥ 2, and n_k ≤ n_{N-1},
    so q ≤ n_{N-1}/n_j. The injective map k ↦ n_k/n_j into Ico 1 (M+1)
    (which has card M) establishes the bound. -/
theorem divPairs_fiber_j_card_le (A : IncreasingSeq) (N j : ℕ) (hj : j < N)
    (hN : 0 < N) :
    (divPairs_fiber_j A N j).card ≤ A.seq (N - 1) / A.seq j := by
  unfold divPairs_fiber_j
  set M := A.seq (N - 1) / A.seq j with hM_def
  -- Inject via k ↦ A.seq k / A.seq j into Ico 1 (M + 1) which has card M
  calc ((range N).filter (fun k => j < k ∧ A.seq j ∣ A.seq k)).card
      ≤ (Finset.Ico 1 (M + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun k => A.seq k / A.seq j)
        · -- Maps into Ico 1 (M+1)
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_range] at hk
          obtain ⟨hkN, _, hdvd⟩ := hk
          rw [Finset.mem_Ico]
          constructor
          · -- quotient ≥ 1 (from divisibility and positivity)
            exact Nat.div_pos (Nat.le_of_dvd (A.pos k) hdvd) (A.pos j)
          · -- quotient ≤ M, hence < M + 1
            apply Nat.lt_succ_of_le
            apply Nat.div_le_div_right
            have hk_le_N : k ≤ N - 1 := by omega
            rcases eq_or_lt_of_le hk_le_N with rfl | h
            · exact le_refl _
            · exact le_of_lt (A.strictMono h)
        · -- Injective on the fiber
          intro k₁ hk₁ k₂ hk₂ heq
          simp only [Finset.coe_filter, Set.mem_sep_iff, Finset.mem_coe,
                     Finset.mem_range] at hk₁ hk₂
          have hd₁ : A.seq j ∣ A.seq k₁ := hk₁.2.2
          have hd₂ : A.seq j ∣ A.seq k₂ := hk₂.2.2
          have h1 := Nat.div_mul_cancel hd₁
          have h2 := Nat.div_mul_cancel hd₂
          have : A.seq k₁ = A.seq k₂ :=
            calc A.seq k₁ = A.seq k₁ / A.seq j * A.seq j := h1.symm
              _ = A.seq k₂ / A.seq j * A.seq j := congr_arg (· * A.seq j) heq
              _ = A.seq k₂ := h2
          exact A.strictMono.injective this
    _ = M := by rw [Nat.card_Ico]; omega

/- ## Part XIII: Growth Constraints from Low Density -/

/-- **Low density implies slow growth**: If ρ_A(k) < ε at index k ≥ 1,
    then the sequence growth is constrained: (1-ε) · n_k ≤ k · n_{k-1}.
    This follows from the complement formula: ρ < ε means usedSum > (1-ε)n_k,
    and usedSum ≤ k · n_{k-1} (growth bound).
    Key consequence: during periods of low density, the sequence must
    grow slowly, which eventually forces density recovery. -/
theorem low_density_growth_constraint (A : IncreasingSeq) (k : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 < ε) (hρ : densityRatio A k < ε) :
    (1 - ε) * (A.seq k : ℝ) < (k : ℝ) * (A.seq (k - 1) : ℝ) := by
  have hge := densityRatio_ge_one_sub_growth A k hk
  -- hge : 1 - k * n_{k-1} / n_k ≤ ρ
  -- hρ : ρ < ε
  -- So 1 - k * n_{k-1} / n_k < ε
  -- Hence (1 - ε) < k * n_{k-1} / n_k
  -- Hence (1 - ε) * n_k < k * n_{k-1}
  have hn_pos : (0 : ℝ) < A.seq k := Nat.cast_pos.mpr (A.pos k)
  have h1 : 1 - (k : ℝ) * (A.seq (k - 1) : ℝ) / (A.seq k : ℝ) < ε := lt_of_le_of_lt hge hρ
  -- Multiply both sides by n_k
  have h2 : (1 - ε) * (A.seq k : ℝ) < (k : ℝ) * (A.seq (k - 1) : ℝ) := by
    rw [sub_div] at h1
    have h3 : 1 - (↑k * ↑(A.seq (k - 1))) / ↑(A.seq k) < ε := h1
    have h4 : 1 - ε < (↑k * ↑(A.seq (k - 1))) / ↑(A.seq k) := by linarith
    rwa [lt_div_iff₀ hn_pos] at h4
  exact h2

/-- **Consecutive low density implies bounded growth ratio**: If ρ < ε for
    two consecutive indices k and k+1 (with k ≥ 1), then:
    n_{k+1} / n_k < (k+1) / (1-ε).
    This constrains the growth when density is persistently low. -/
theorem consecutive_low_density_ratio (A : IncreasingSeq) (k : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρ : densityRatio A (k + 1) < ε) :
    (A.seq (k + 1) : ℝ) / (A.seq k : ℝ) < (k + 1 : ℝ) / (1 - ε) := by
  have hn_pos : (0 : ℝ) < A.seq k := Nat.cast_pos.mpr (A.pos k)
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have hgrow := low_density_growth_constraint A (k + 1) (by omega) ε hε hρ
  -- hgrow : (1-ε) * n_{k+1} < (k+1) * n_k
  simp only [Nat.add_sub_cancel] at hgrow
  rw [div_lt_div_iff₀ hn_pos h1ε]
  linarith

/-- **Average density from deficit**: The Cesàro average equals 1 minus
    the average deficit. Combined with deficit bounds, this gives tight
    estimates on the Cesàro average.
    C_A(N) = 1 - (1/N) Σ (1 - ρ_A(k)). -/
theorem cesaroAvg_eq_one_sub_avg_deficit (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    cesaroAvg A N = 1 - (∑ k ∈ range N, (1 - densityRatio A k)) / N := by
  unfold cesaroAvg
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  have hdef : ∑ k ∈ range N, (1 - densityRatio A k) =
      ↑N - ∑ k ∈ range N, densityRatio A k := by
    rw [Finset.sum_sub_distrib]; simp [Finset.sum_const, Finset.card_range]
  rw [hdef]; field_simp; ring

/-- **Deficit proportion bound**: If ρ < ε for at least m indices in {0,...,N-1},
    then the sum of deficits is at least m · (1-ε).
    Together with sum_deficit_lt, this shows that the number of low-ρ indices
    is bounded: m < N/(1-ε). -/
theorem deficit_count_bound (A : IncreasingSeq) (N : ℕ)
    (S : Finset ℕ) (hS : S ⊆ range N)
    (ε : ℝ) (hε1 : ε < 1)
    (hρ : ∀ k ∈ S, densityRatio A k < ε) :
    (S.card : ℝ) * (1 - ε) ≤ ∑ k ∈ range N, (1 - densityRatio A k) := by
  calc (S.card : ℝ) * (1 - ε)
      = ∑ _ ∈ S, (1 - ε) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ S, (1 - densityRatio A k) := by
        apply sum_le_sum; intro k hk
        linarith [hρ k hk]
    _ ≤ ∑ k ∈ range N, (1 - densityRatio A k) := by
        apply sum_le_sum_of_subset_of_nonneg hS
        intro k _ _; linarith [densityRatio_le_one A k]

/-- **Density cannot be uniformly zero**: There is no ε = 0 case — the density
    ratio is strictly positive at every index. This is a direct corollary of
    densityRatio_pos, restated in a form useful for the dichotomy approach. -/
theorem density_somewhere_pos (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    0 < ∑ k ∈ range N, densityRatio A k :=
  calc (0 : ℝ) < densityRatio A 0 := densityRatio_pos A 0
    _ ≤ ∑ k ∈ range N, densityRatio A k := by
        apply Finset.single_le_sum (fun k _ => densityRatio_nonneg A k)
        exact Finset.mem_range.mpr hN

/- ## Part XIV: Euler-Totient Bridge for Dichotomy -/

/-- **Low density implies small Euler ratio**: If ρ_A(k) < ε, then
    the classical Euler ratio φ(n_k)/n_k < ε as well.
    This is the key bridge to the prime factorization: by the Euler product
    φ(n)/n = ∏_{p | n}(1 - 1/p), having φ(n)/n < ε forces n to be
    divisible by many small primes.
    Named corollary of densityRatio_ge_totient_ratio for use in dichotomy analysis. -/
theorem low_density_euler_bound (A : IncreasingSeq) (k : ℕ)
    (ε : ℝ) (hρ : densityRatio A k < ε) :
    (Nat.totient (A.seq k) : ℝ) / (A.seq k : ℝ) < ε :=
  lt_of_le_of_lt (densityRatio_ge_totient_ratio A k) hρ

/-- **Density recovery from fast growth**: If the sequence growth at index k+1
    satisfies n_{k+1} > C · n_k for some C > 0, then ρ_A(k+1) ≥ 1 - (k+1)/C.
    In particular, when C is much larger than k, the density is close to 1.
    This is the mechanism by which low-density periods (slow growth) are
    followed by density recovery (when growth resumes). -/
theorem densityRatio_recovery_from_growth (A : IncreasingSeq) (k : ℕ)
    (C : ℝ) (hC : 0 < C)
    (hgrow : C * (A.seq k : ℝ) < (A.seq (k + 1) : ℝ)) :
    1 - (k + 1 : ℝ) / C ≤ densityRatio A (k + 1) := by
  have hge := densityRatio_ge_one_sub_growth A (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hge
  calc 1 - (k + 1 : ℝ) / C
      ≤ 1 - (k + 1 : ℝ) * (A.seq k : ℝ) / (A.seq (k + 1) : ℝ) := by
        apply sub_le_sub_left
        have hn_pos : (0 : ℝ) < A.seq (k + 1) := Nat.cast_pos.mpr (A.pos (k + 1))
        rw [div_le_div_iff₀ hC hn_pos]
        nlinarith
    _ ≤ densityRatio A (k + 1) := hge

end Erdos1000
