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

  Axiom count: 4 (erdos_no_zero_limit, erdos_dichotomy,
    cassels_liminf_zero, haight_resolution)
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

/- ## Part V: Main Predicates -/

/-- A sequence has vanishing Cesàro average if C_A(N) → 0. -/
def VanishingAverage (A : IncreasingSeq) : Prop :=
  Tendsto (cesaroAvg A) atTop (𝓝 0)

/-- A sequence has density tending to zero if ρ_A(k) → 0. -/
def DensityToZero (A : IncreasingSeq) : Prop :=
  Tendsto (densityRatio A) atTop (𝓝 0)

/- ## Part VI: Erdős' Results (1964) -/

/-- Erdős' No-Zero-Limit Theorem: The density ratio ρ_A(k) = φ_A(k)/n_k
    cannot converge to 0 for any sequence A.
    Proof sketch: φ_A(k) ≥ φ(n_k) ≥ c·n_k/log log n_k → ∞ (Mertens). -/
axiom erdos_no_zero_limit (A : IncreasingSeq) : ¬ DensityToZero A

/-- Erdős' Dichotomy: If the density ratio gets arbitrarily close to 0,
    then it also gets arbitrarily close to 1.
    Proof uses the Euler product formula for φ(n)/n and smooth numbers. -/
axiom erdos_dichotomy (A : IncreasingSeq) :
    (∀ ε > 0, ∃ᶠ k in atTop, densityRatio A k < ε) →
    (∀ ε > 0, ∃ᶠ k in atTop, 1 - ε < densityRatio A k)

/- ## Part VII: Cassels' Result (1950) -/

/-- Cassels' theorem: There exists a sequence A such that
    the liminf of the Cesàro average is 0.
    Constructed via continued fraction convergents. -/
axiom cassels_liminf_zero :
    ∃ A : IncreasingSeq, ∀ ε > 0, ∃ᶠ N in atTop, cesaroAvg A N < ε

/- ## Part VIII: Haight's Resolution -/

/-- Haight's Theorem (resolves Erdős' Problem #1000):
    There exists a sequence A such that the Cesàro average converges to 0.
    Construction uses rapidly growing highly composite numbers to force
    the average to zero while individual terms oscillate.
    This contradicts Erdős' conjecture that no such sequence exists. -/
axiom haight_resolution : ∃ A : IncreasingSeq, VanishingAverage A

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

end Erdos1000
