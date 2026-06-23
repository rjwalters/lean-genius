/-
# Erdős Problem #153: Gap Variance in Sidon Sumsets

Let A be a finite Sidon set and A+A = {s₁ < ... < sₜ}. Is it true that
(1/t) · Σ (s_{i+1} - s_i)² → ∞ as |A| → ∞?

## Status: OPEN

## References
- Erdős–Sárközy–Sós, "On Sum Sets of Sidon Sets, I" (1994)

Results:
- sidon_sumset_card: fully proved via upper triangle cardinality lemma
- sidon_sumset_range: proved
- sidon_distinct_differences: B₂ distinct differences characterization
- sidon_density_bound: density bound n(n+1)/2 ≤ 2N+1
- average_gap_bounded: proved (trivially: C can depend on N)
Axioms: 1 (erdos_153_conjecture — the main open conjecture)
Sorries: 0
Derived: infinite_sidon_gap_from_finite (infinite case follows from finite)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Classical

/-
## Section I: Sidon Sets
-/

/-- A Sidon set (B₂ set): all pairwise sums are distinct.
a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-
## Section II: Sumset and Gap Structure
-/

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The sorted sumset as a list. -/
noncomputable def sortedSumset (A : Finset ℕ) : List ℕ :=
  (sumset A).sort (· ≤ ·)

/-- The sum of squared consecutive gaps in the sorted sumset.
Given A+A = {s₁ < ... < sₜ}, this computes Σ (s_{i+1} - s_i)². -/
noncomputable def gapSquaredSum (A : Finset ℕ) : ℕ :=
  let sorted := sortedSumset A
  (List.zip sorted sorted.tail).foldl
    (fun acc p => acc + (p.2 - p.1) ^ 2) 0

/-
## Section III: The Gap Variance
-/

/-- The mean squared gap: (1/t) · Σ (s_{i+1} - s_i)²
where t = |A+A| is the sumset cardinality. -/
noncomputable def meanGapSquared (A : Finset ℕ) : ℝ :=
  if (sumset A).card ≤ 1 then 0
  else (gapSquaredSum A : ℝ) / ((sumset A).card - 1 : ℝ)

/-- The minimum mean squared gap over all Sidon sets of size n. -/
noncomputable def minMeanGapSquared (n : ℕ) : ℝ :=
  ⨅ (A : Finset ℕ) (_ : A.card = n) (_ : IsSidon A), meanGapSquared A

/-
## Section IV: The Conjecture
-/

/-- **Erdős Problem #153**: Does the mean squared gap in the sumset
of a Sidon set tend to infinity as the set grows?

Formally: for every M > 0, there exists N₀ such that for every
Sidon set A with |A| ≥ N₀, the mean squared gap in A+A exceeds M. -/
def ErdosProblem153 : Prop :=
  ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ A : Finset ℕ, IsSidon A → A.card ≥ N₀ →
      meanGapSquared A > M

/-
## Section V: Upper Triangle Cardinality
-/

/-- The diagonal {(a,a) : a ∈ A} embeds into {(a,b) ∈ A×A : a ≤ b}. -/
private lemma diag_card_eq (A : Finset ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)).card = A.card := by
  convert Finset.card_image_of_injective A
    (fun a b (h : (a, a) = (b, b)) => (Prod.mk.inj h).1) using 1
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
  · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩

/-- Swap gives a bijection between {(a,b) : b < a} and {(a,b) : a < b} in A×A. -/
private lemma card_lt_swap (A : Finset ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)).card =
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
  apply Finset.card_nbij (fun p : ℕ × ℕ => (p.2, p.1))
  · intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
  · intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨⟨b, a⟩, by simp [Finset.mem_filter, Finset.mem_product, hp.1.2, hp.1.1, hp.2], rfl⟩

/-- Upper triangle cardinality: |{(a,b) ∈ A×A : a ≤ b}| = n(n+1)/2. -/
private lemma card_upper_triangle (A : Finset ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card =
    A.card * (A.card + 1) / 2 := by
  set n := A.card
  set U := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)
  set L := (A ×ˢ A).filter (fun p : ℕ × ℕ => ¬(p.1 ≤ p.2))
  -- U and L partition A ×ˢ A, so U.card + L.card = n²
  have hpart : U.card + L.card = n * n := by
    have := Finset.filter_card_add_filter_neg_card_eq_card (A ×ˢ A)
      (fun p : ℕ × ℕ => p.1 ≤ p.2)
    rwa [Finset.card_product] at this
  -- L = {(a,b) : ¬(a ≤ b)} = {(a,b) : b < a}
  have hL_eq : L = (A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1) := by
    ext ⟨a, b⟩; simp [L, Nat.not_le]
  -- U = {a < b} ∪ {a = b}, disjointly
  have hU_lt : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2) ⊆ U := by
    intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨hp.1, Nat.le_of_lt hp.2⟩
  have hU_eq : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2) ⊆ U := by
    intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨hp.1, le_of_eq hp.2⟩
  have hdisj : Disjoint ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2))
                        ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)) := by
    rw [Finset.disjoint_filter]
    intro ⟨a, b⟩ _ hlt heq; omega
  have hunion : U = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)) ∪
                    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, U]
    constructor
    · intro ⟨hmem, hle⟩
      rcases Nat.eq_or_lt_of_le hle with h | h
      · right; exact ⟨hmem, h.symm⟩
      · left; exact ⟨hmem, h⟩
    · rintro (⟨hmem, hlt⟩ | ⟨hmem, heq⟩)
      · exact ⟨hmem, Nat.le_of_lt hlt⟩
      · exact ⟨hmem, le_of_eq heq⟩
  have hUcard : U.card = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card + n := by
    rw [hunion, Finset.card_union_of_disjoint hdisj, diag_card_eq]
  -- By swap bijection: |{b < a}| = |{a < b}|
  have hswap := card_lt_swap A
  -- L.card = |{a < b}| (via hL_eq and hswap)
  have hLcard : L.card = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    rw [show L.card = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)).card from by
      congr 1; exact hL_eq]
    exact hswap
  -- Arithmetic: U.card = |{a<b}| + n, L.card = |{a<b}|, U.card + L.card = n²
  -- So 2*U.card - n = n², thus 2*U.card = n² + n = n*(n+1), U.card = n*(n+1)/2
  set lt_card := ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card
  -- From hUcard: U.card = lt_card + n
  -- From hLcard: L.card = lt_card
  -- From hpart: U.card + L.card = n * n
  -- So: (lt_card + n) + lt_card = n * n
  -- => 2 * lt_card + n = n * n
  -- And U.card = lt_card + n
  -- Goal: U.card = n * (n + 1) / 2
  -- i.e., lt_card + n = n * (n + 1) / 2
  -- From 2 * lt_card = n * n - n = n * (n - 1):
  --   lt_card = n * (n - 1) / 2
  --   U.card = n * (n - 1) / 2 + n = (n² - n + 2n) / 2 = n*(n+1)/2
  have h2lt : 2 * lt_card + n = n * n := by omega
  have hgoal : 2 * U.card = n * (n + 1) := by omega
  omega

/-
## Section V.5: General Sumset Cardinality Bound
-/

/-- The sumset A+A equals the image of the upper triangle {(a,b) : a ≤ b}
    under addition, since a+b = b+a. -/
private theorem sumset_eq_upper_image (A : Finset ℕ) :
    sumset A = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).image
      (fun p => p.1 + p.2) := by
  ext m
  simp only [sumset, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, hab⟩
    rcases le_total a b with h | h
    · exact ⟨a, b, ⟨⟨ha, hb⟩, h⟩, hab⟩
    · exact ⟨b, a, ⟨⟨hb, ha⟩, h⟩, by omega⟩
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, _⟩, hab⟩
    exact ⟨a, b, ⟨ha, hb⟩, hab⟩

/-- Upper bound on sumset cardinality: |A+A| ≤ n(n+1)/2 for any A with n = |A|.
    Since a+b = b+a, distinct sums come only from the upper triangle. -/
theorem sumset_card_le (A : Finset ℕ) :
    (sumset A).card ≤ A.card * (A.card + 1) / 2 := by
  rw [sumset_eq_upper_image]
  calc (((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).image
          (fun p => p.1 + p.2)).card
      ≤ ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card :=
        Finset.card_image_le
    _ = A.card * (A.card + 1) / 2 := card_upper_triangle A

/-
## Section VI: Sidon Set Sumset Properties
-/

/-- A Sidon set of size n has at least n(n+1)/2 distinct pairwise sums.
    Proof: the map (a,b) ↦ a+b is injective on {(a,b) ∈ A×A : a ≤ b}
    by the Sidon condition, and this set has n(n+1)/2 elements. -/
theorem sidon_sumset_card (A : Finset ℕ) (h : IsSidon A) :
    (sumset A).card ≥ A.card * (A.card + 1) / 2 := by
  -- Let S = {(a,b) ∈ A×A : a ≤ b}
  set S := (A ×ˢ A).filter (fun p => p.1 ≤ p.2) with hSdef
  -- The sum map is injective on S (Sidon condition)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) ↑S := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
               Finset.mem_product] at h₁ h₂
    have := h a₁ h₁.1.1 b₁ h₁.1.2 a₂ h₂.1.1 b₂ h₂.1.2 h₁.2 h₂.2 heq
    exact Prod.ext this.1 this.2
  -- The image of S under the sum map is contained in sumset A
  have hsub : S.image (fun p => p.1 + p.2) ⊆ sumset A := by
    intro s hs
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hs
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := hs
    exact Finset.mem_image.mpr ⟨⟨a, b⟩, Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  -- So |sumset A| ≥ |S| = n(n+1)/2
  have hge : (sumset A).card ≥ S.card :=
    (Finset.card_image_of_injOn hinj) ▸ Finset.card_le_card hsub
  calc A.card * (A.card + 1) / 2
      = S.card := (card_upper_triangle A).symm
    _ ≤ (sumset A).card := hge

/-- Exact sumset cardinality for Sidon sets: |A+A| = n(n+1)/2.
    Combines the lower bound (Sidon injectivity) with the general upper bound
    (commutativity of addition). -/
theorem sidon_sumset_card_eq (A : Finset ℕ) (h : IsSidon A) :
    (sumset A).card = A.card * (A.card + 1) / 2 :=
  le_antisymm (sumset_card_le A) (sidon_sumset_card A h)

/-- If A ⊆ {1,...,N} is Sidon, then A+A ⊆ {2,...,2N} so gaps can be
computed within a bounded range. -/
theorem sidon_sumset_range (A : Finset ℕ) (N : ℕ) (_h : IsSidon A)
    (hN : ∀ a ∈ A, a ≤ N) :
    ∀ s ∈ sumset A, s ≤ 2 * N := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hs
  linarith [hN a ha, hN b hb]

/-
## Section VI.5: Distinct Differences and Density
-/

/-- For a Sidon set, distinct ordered pairs yield distinct differences:
    if a < b and c < d are in A with b - a = d - c, then (a,b) = (c,d).
    This is the "B₂ ↔ distinct differences" characterization. -/
theorem sidon_distinct_differences (A : Finset ℕ) (h : IsSidon A)
    (a b c d : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a < b) (hcd : c < d) (heq : b - a = d - c) : a = c ∧ b = d := by
  -- Case split on relative orderings, apply IsSidon in each case
  rcases le_or_lt a d with had | had
  · rcases le_or_lt c b with hcb | hcb
    · -- a ≤ d, c ≤ b: IsSidon on pairs (a,d) and (c,b)
      have := h a ha d hd c hc b hb had hcb (by omega)
      exact ⟨this.1, this.2.symm⟩
    · -- a ≤ d, b < c: IsSidon on (a,d) and (b,c) gives a = b, contradiction
      obtain ⟨h1, _⟩ := h a ha d hd b hb c hc had (le_of_lt hcb) (by omega)
      omega
  · rcases le_or_lt c b with hcb | hcb
    · -- d < a, c ≤ b: IsSidon on (d,a) and (c,b) gives a = b, contradiction
      obtain ⟨_, h2⟩ := h d hd a ha c hc b hb (le_of_lt had) hcb (by omega)
      omega
    · -- d < a, b < c, a < b, c < d forms a cycle: impossible
      omega

/-- The density bound for Sidon sets: a Sidon set A ⊆ {0,...,N}
    satisfies n(n+1)/2 ≤ 2N + 1, i.e., |A| ≤ √(2N) + O(1). -/
theorem sidon_density_bound (A : Finset ℕ) (N : ℕ) (h : IsSidon A)
    (hN : ∀ a ∈ A, a ≤ N) :
    A.card * (A.card + 1) / 2 ≤ 2 * N + 1 := by
  have hrange : sumset A ⊆ Finset.range (2 * N + 1) := fun s hs =>
    Finset.mem_range.mpr (by have := sidon_sumset_range A N h hN s hs; omega)
  calc A.card * (A.card + 1) / 2
      ≤ (sumset A).card := sidon_sumset_card A h
    _ ≤ (Finset.range (2 * N + 1)).card := Finset.card_le_card hrange
    _ = 2 * N + 1 := Finset.card_range _

/-
## Section VII: Known Bounds
-/

/-- The sumset has size Θ(n²) while lying in an interval of length
Θ(n²) (since Sidon sets have size O(√N) in {1,...,N}).
The average gap is therefore Θ(1), but the variance could grow.
NOTE: This is trivially true since C is allowed to depend on N. -/
theorem average_gap_bounded (A : Finset ℕ) (N : ℕ) (_h : IsSidon A)
    (hN : ∀ a ∈ A, a ≤ N) (hn : A.card ≥ 2) :
    ∃ C : ℝ, C > 0 ∧
      (2 * N : ℝ) / (sumset A).card ≤ C := by
  -- The sumset is nonempty (A has ≥ 2 elements, so a+a ∈ sumset A)
  have hne : (sumset A).Nonempty := by
    have ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    exact ⟨a + a, Finset.mem_image.mpr ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩⟩
  have hcard_pos : (0 : ℝ) < (sumset A).card :=
    Nat.cast_pos.mpr (Finset.Nonempty.card_pos hne)
  -- C = 2N + 1 works: 2N / |A+A| ≤ 2N ≤ 2N + 1
  refine ⟨2 * N + 1, by positivity, ?_⟩
  have h1 : (1 : ℝ) ≤ (sumset A).card := by exact_mod_cast Finset.Nonempty.card_pos hne
  calc (2 * (N : ℝ)) / ((sumset A).card : ℝ)
      ≤ 2 * N / 1 := by apply div_le_div_of_nonneg_left (by positivity) one_pos h1
    _ = 2 * N := by ring
    _ ≤ 2 * N + 1 := by linarith

/-- For a sorted list of naturals with no duplicates, consecutive pairs
    in the zip-with-tail differ by ≥ 1, so the accumulated sum of squared
    gaps is at least the number of gaps. -/
private lemma foldl_sq_gap_ge (l : List ℕ) (hs : l.Pairwise (· ≤ ·)) (hd : l.Nodup) :
    ∀ acc : ℕ,
    (l.zip l.tail).foldl (fun a (p : ℕ × ℕ) => a + (p.2 - p.1) ^ 2) acc ≥
    acc + (l.zip l.tail).length := by
  induction l with
  | nil => intro acc; simp
  | cons a t ih =>
    intro acc
    cases t with
    | nil => simp
    | cons b u =>
      simp only [List.tail_cons, List.zip_cons_cons, List.foldl_cons, List.length_cons]
      have hpw := List.pairwise_cons.mp hs
      have hab : a ≤ b := hpw.1 b List.mem_cons_self
      have hne : a ≠ b := by
        intro heq; subst heq
        exact (List.nodup_cons.mp hd).1 List.mem_cons_self
      have hd' : (b :: u).Nodup := (List.nodup_cons.mp hd).2
      have ih_step := ih hpw.2 hd' (acc + (b - a) ^ 2)
      simp only [List.tail_cons] at ih_step
      have hgap : (b - a) ^ 2 ≥ 1 := by
        have h1 : 1 ≤ b - a := by omega
        rw [sq]; exact Nat.mul_le_mul h1 h1
      linarith

/-- The gap squared sum is at least (|A+A| - 1), since each consecutive
    pair in the sorted sumset contributes a squared gap ≥ 1. -/
private lemma gapSquaredSum_ge_card_sub_one (A : Finset ℕ) :
    gapSquaredSum A ≥ (sumset A).card - 1 := by
  unfold gapSquaredSum sortedSumset
  have hs := (sumset A).pairwise_sort (· ≤ ·)
  have hd := (sumset A).sort_nodup (· ≤ ·)
  have key := foldl_sq_gap_ge _ hs hd 0
  simp only [Nat.zero_add] at key
  have hzip_len : (((sumset A).sort (· ≤ ·)).zip ((sumset A).sort (· ≤ ·)).tail).length =
      (sumset A).card - 1 := by
    rw [List.length_zip, List.length_tail, (sumset A).length_sort]
    exact min_eq_right (Nat.sub_le _ _)
  linarith

/-- Erdős, Sárközy, and Sós (1994) studied the gap distribution
in sumsets of Sidon sets. The mean squared gap is at least 1,
since consecutive elements of a sorted set of naturals differ by ≥ 1.
(The ESS result is actually stronger, but c = 1 suffices here.) -/
theorem ess_1994_result :
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℕ, IsSidon A → A.card ≥ 4 →
      meanGapSquared A ≥ c := by
  refine ⟨1, one_pos, fun A hsidon hn => ?_⟩
  have hcard : (sumset A).card ≥ 10 := by
    have h := sidon_sumset_card A hsidon
    have : A.card * (A.card + 1) ≥ 20 := by nlinarith
    omega
  unfold meanGapSquared
  rw [if_neg (by omega : ¬(sumset A).card ≤ 1)]
  have hgs := gapSquaredSum_ge_card_sub_one A
  have hd_pos : (0 : ℝ) < ((sumset A).card : ℝ) - 1 := by
    have : (2 : ℕ) ≤ (sumset A).card := by omega
    have : (2 : ℝ) ≤ ↑(sumset A).card := by exact_mod_cast this
    linarith
  -- Cast the ℕ inequality to ℝ
  have hgs_real : (↑(sumset A).card : ℝ) - 1 ≤ ↑(gapSquaredSum A) := by
    have h_cast : (↑((sumset A).card - 1 : ℕ) : ℝ) ≤ ↑(gapSquaredSum A) :=
      Nat.cast_le.mpr hgs
    rwa [Nat.cast_sub (by omega : 1 ≤ (sumset A).card), Nat.cast_one] at h_cast
  -- 1 = d/d ≤ g/d by monotonicity (d ≤ g)
  calc (1 : ℝ) = (↑(sumset A).card - 1) / (↑(sumset A).card - 1) :=
          (div_self (ne_of_gt hd_pos)).symm
    _ ≤ ↑(gapSquaredSum A) / (↑(sumset A).card - 1) := by gcongr

/-
## Section VIII: The Main Conjecture (Axiomatized)
-/

/-- **Erdős Problem #153** (axiomatized): The mean squared gap in the sumset
of a Sidon set tends to infinity as the set grows. This is an open problem. -/
axiom erdos_153_conjecture : ErdosProblem153

/-
## Section IX: Infinite Sidon Sets (Derived from Finite Conjecture)

The infinite variant follows from the finite conjecture via three steps:
1. Finite restrictions of infinite Sidon sets inherit the Sidon property
2. Infinite subsets of ℕ have arbitrarily large finite restrictions
3. Combining these with the finite conjecture yields the infinite result
-/

/-- An infinite Sidon set: all pairwise sums from the set are distinct. -/
def IsInfiniteSidon (S : Set ℕ) : Prop :=
  S.Infinite ∧
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- Any finite restriction of an infinite Sidon set inherits the Sidon property. -/
lemma infinite_sidon_restriction (S : Set ℕ) (hS : IsInfiniteSidon S) (N : ℕ) :
    IsSidon ((Finset.range (N + 1)).filter (· ∈ S)) := by
  intro a ha b hb c hc d hd hle1 hle2 heq
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb hc hd
  exact hS.2 a ha.2 b hb.2 c hc.2 d hd.2 hle1 hle2 heq

/-- An infinite subset of ℕ has a finite subset of any given cardinality. -/
private lemma infinite_set_exists_finset (S : Set ℕ) (hS : S.Infinite) :
    ∀ k : ℕ, ∃ (u : Finset ℕ), (↑u : Set ℕ) ⊆ S ∧ u.card = k := by
  intro k
  induction k with
  | zero => exact ⟨∅, Set.empty_subset _, Finset.card_empty⟩
  | succ n ih =>
    obtain ⟨u, hu_sub, hu_card⟩ := ih
    have hS' : (S \ ↑u).Infinite := hS.diff u.finite_toSet
    obtain ⟨x, hx_diff⟩ := hS'.nonempty
    have hx_S : x ∈ S := hx_diff.1
    have hx_u : x ∉ u := fun h => hx_diff.2 (Finset.mem_coe.mpr h)
    exact ⟨u.cons x hx_u,
      fun y hy => by
        rw [Finset.mem_coe, Finset.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hx_S
        · exact hu_sub (Finset.mem_coe.mpr hy),
      by simp [hu_card]⟩

/-- For an infinite subset of ℕ, the restriction to {0,...,N}
    has cardinality growing without bound as N → ∞. -/
private lemma infinite_set_card_grows (S : Set ℕ) (hS : S.Infinite) :
    ∀ k : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((Finset.range (N + 1)).filter (· ∈ S)).card ≥ k := by
  intro k
  rcases k with _ | k
  · exact ⟨0, fun _ _ => Nat.zero_le _⟩
  · obtain ⟨u, hu_sub, hu_card⟩ := infinite_set_exists_finset S hS (k + 1)
    have hne : u.Nonempty := Finset.card_pos.mp (by omega)
    use u.max' hne
    intro N hN
    have : u ⊆ (Finset.range (N + 1)).filter (· ∈ S) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := Finset.le_max' u x hx; omega,
             hu_sub (Finset.mem_coe.mpr hx)⟩
    calc ((Finset.range (N + 1)).filter (· ∈ S)).card
        ≥ u.card := Finset.card_le_card this
      _ = k + 1 := hu_card

/-- The infinite Sidon gap conjecture follows from the finite one (Erdős #153).
    For any infinite Sidon set S, the mean squared gap in S ∩ {0,...,N}
    diverges as N → ∞. This reduces the infinite variant to a consequence
    of the finite conjecture.

    Proof: Given M > 0, the finite conjecture provides n₀ such that any
    Sidon set of size ≥ n₀ has mean gap² > M. Since S is infinite,
    the restriction to {0,...,N} eventually has ≥ n₀ elements, and it
    inherits the Sidon property from S. -/
theorem infinite_sidon_gap_from_finite :
    ∀ S : Set ℕ, IsInfiniteSidon S →
      ∀ M : ℝ, M > 0 →
        ∃ N₀ : ℕ, ∀ N ≥ N₀,
          let A := (Finset.range (N + 1)).filter (· ∈ S)
          A.card ≥ 2 → meanGapSquared A > M := by
  intro S hS M hM
  -- Get n₀ from the finite conjecture
  obtain ⟨n₀, hn₀⟩ := erdos_153_conjecture M hM
  -- Get N₁ such that the restriction has ≥ n₀ elements for all N ≥ N₁
  obtain ⟨N₁, hN₁⟩ := infinite_set_card_grows S hS.1 n₀
  -- For N ≥ N₁: the restriction is Sidon with ≥ n₀ elements → apply conjecture
  exact ⟨N₁, fun N hN _ => hn₀ _ (infinite_sidon_restriction S hS N) (hN₁ N hN)⟩

/-
## Section X: Sumset Extremes
-/

/-- The sumset A+A is nonempty whenever A is nonempty:
    if a ∈ A then a + a ∈ A+A. -/
theorem sumset_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (sumset A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a + a, Finset.mem_image.mpr ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩⟩

/-- The minimum element of A+A is 2·min(A): the diagonal pair achieves the minimum,
    and every sum a+b ≥ min(A)+min(A). -/
theorem sumset_min' (A : Finset ℕ) (hA : A.Nonempty) :
    (sumset A).min' (sumset_nonempty A hA) = 2 * A.min' hA := by
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨(A.min' hA, A.min' hA),
      Finset.mem_product.mpr ⟨Finset.min'_mem A hA, Finset.min'_mem A hA⟩, by ring⟩
  · apply Finset.le_min'
    intro x hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    linarith [Finset.min'_le A a ha, Finset.min'_le A b hb]

/-- The maximum element of A+A is 2·max(A): the diagonal pair achieves the maximum,
    and every sum a+b ≤ max(A)+max(A). -/
theorem sumset_max' (A : Finset ℕ) (hA : A.Nonempty) :
    (sumset A).max' (sumset_nonempty A hA) = 2 * A.max' hA := by
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    linarith [Finset.le_max' A a ha, Finset.le_max' A b hb]
  · apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨(A.max' hA, A.max' hA),
      Finset.mem_product.mpr ⟨Finset.max'_mem A hA, Finset.max'_mem A hA⟩, by ring⟩

/-- The span of A+A is twice the span of A:
    max(A+A) − min(A+A) = 2·(max(A) − min(A)). -/
theorem sumset_span (A : Finset ℕ) (hA : A.Nonempty) :
    (sumset A).max' (sumset_nonempty A hA) - (sumset A).min' (sumset_nonempty A hA) =
    2 * (A.max' hA - A.min' hA) := by
  rw [sumset_min' A hA, sumset_max' A hA]
  have hle : A.min' hA ≤ A.max' hA :=
    Finset.min'_le A (A.max' hA) (Finset.max'_mem A hA)
  omega
