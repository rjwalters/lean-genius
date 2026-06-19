/-
# Erdős Problem #1062 (OQ-04): k-Fold "No Element Divides k Others" Sets

The base problem (Erdős #1062) studies sets `A ⊆ {1,…,n}` in which no element
divides **two** distinct others, and asks for the growth of the extremal size
`f(n)` (Lebensold: `0.6725n ≤ f(n) ≤ 0.6736n`; the irrationality of `lim f(n)/n`
is OPEN).

This file formalizes the natural **k-fold generalization**: a set has the
property `NoDividesKOthers k` when no element divides `k` distinct other
elements (equivalently, every element has at most `k-1` proper multiples in the
set). This single parametrized family unifies several classical notions:

* `k = 1` ⟺ the set is **primitive** (no element divides any other);
* `k = 2` ⟺ the **Erdős #1062** condition (`NoDividesTwoOthers`).

We prove the structural backbone of the family — all results are elementary and
fully machine-checked (0 axioms, 0 sorries):

* monotonicity in the parameter `k` (predicate and extremal function);
* heredity (closed under taking subsets);
* the `k = 1` and `k = 2` identifications above;
* the size sandwich `n - ⌊n/2⌋ ≤ maxNDKOSize k n ≤ n` for `k ≥ 1`, via the
  primitive upper-half interval `{⌊n/2⌋+1, …, n}`.

The OPEN extremal/density questions (the analogue of Lebensold's bounds and the
irrationality of the limiting density for each `k`) are deliberately out of
scope: this file builds the verified definitional framework, not those bounds.

## Status: framework verified; underlying density questions OPEN

## References
- Guy (2004), Problem B24
- Lebensold (1976), bounds 0.6725n ≤ f(n) ≤ 0.6736n
-/

import Mathlib

/-
## Section I: The k-Fold Divisibility Condition

This file is self-contained (Mathlib only). The two classical predicates it
generalizes — `NoDividesTwoOthers` (the Erdős #1062 condition) and
`IsPrimitiveFinset` (primitive sets) — are reproduced verbatim below from the
gallery's Erdős #1062 entry so that the identifications in Section III are
stated against their exact definitions.
-/

/-- A set has the **Erdős #1062** property if no element divides two distinct
others (reproduced verbatim from the Erdős #1062 base entry). -/
def NoDividesTwoOthers (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ∣ b → a ∣ c → a ≠ b → a ≠ c → b ≠ c → False

/-- A **primitive** set has no element dividing any other (reproduced verbatim
from the Erdős #1062 base entry). -/
def IsPrimitiveFinset (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → ¬(a ∣ b)

/-- The proper multiples of `a` inside `A`: the elements `b ∈ A` with `a ∣ b`
and `b ≠ a`. Its cardinality counts how many *other* elements `a` divides. -/
def properMultiples (a : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun b => a ∣ b ∧ a ≠ b)

/-- A set `A` has the **k-fold** property when no element of `A` divides `k`
distinct other elements — equivalently, every element has at most `k-1` proper
multiples in `A`. This is the natural generalization of the Erdős #1062
condition (`k = 2`). -/
def NoDividesKOthers (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, (properMultiples a A).card < k

/-- The k-fold extremal function: the maximum size of a `NoDividesKOthers k`
subset of `{1,…,n}`. The filter predicate is written in its unfolded bounded-`∀`
form (definitionally `NoDividesKOthers k A`) so that decidability is synthesized
directly, keeping the function computable. -/
def maxNDKOSize (k n : ℕ) : ℕ :=
  Finset.sup
    ((Finset.Icc 1 n).powerset.filter
      (fun A => ∀ a ∈ A, (properMultiples a A).card < k))
    Finset.card

/-
## Section II: Elementary Structural Properties
-/

/-- The empty set vacuously has the k-fold property for every `k`. -/
theorem noDividesKOthers_empty (k : ℕ) : NoDividesKOthers k (∅ : Finset ℕ) := by
  intro a ha
  exact absurd ha (Finset.not_mem_empty a)

/-- `k = 0` is degenerate: only the empty set qualifies, since no nonempty set
can have every element divide fewer than `0` others. -/
theorem noDividesKOthers_zero_iff (A : Finset ℕ) :
    NoDividesKOthers 0 A ↔ A = ∅ := by
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro a ha
    exact Nat.not_lt_zero _ (h a ha)
  · rintro rfl
    exact noDividesKOthers_empty 0

/-- The k-fold property is monotone in `k`: a stronger (smaller `k`) bound
implies every weaker one. -/
theorem noDividesKOthers_mono_k {k k' : ℕ} (hkk : k ≤ k') {A : Finset ℕ}
    (h : NoDividesKOthers k A) : NoDividesKOthers k' A := by
  intro a ha
  exact lt_of_lt_of_le (h a ha) hkk

/-- Heredity: subsets of a `NoDividesKOthers k` set are again
`NoDividesKOthers k`, because removing elements only shrinks the proper-multiple
sets. -/
theorem noDividesKOthers_subset {k : ℕ} {A B : Finset ℕ} (hBA : B ⊆ A)
    (hA : NoDividesKOthers k A) : NoDividesKOthers k B := by
  intro a ha
  calc (properMultiples a B).card
      ≤ (properMultiples a A).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hBA)
    _ < k := hA a (hBA ha)

/-
## Section III: Identifying the Classical Cases (k = 1 and k = 2)
-/

/-- **`k = 1` is exactly primitivity.** A set is `NoDividesKOthers 1` iff it is
primitive (no element divides any distinct other), since the bound forces every
proper-multiple set to be empty. -/
theorem noDividesKOthers_one_iff_primitive (A : Finset ℕ) :
    NoDividesKOthers 1 A ↔ IsPrimitiveFinset A := by
  constructor
  · intro h a b ha hb hne hdvd
    have hcard : (properMultiples a A).card < 1 := h a ha
    have hmem : b ∈ properMultiples a A := by
      simp only [properMultiples, Finset.mem_filter]
      exact ⟨hb, hdvd, hne⟩
    rw [Nat.lt_one_iff, Finset.card_eq_zero] at hcard
    rw [hcard] at hmem
    exact Finset.not_mem_empty b hmem
  · intro h a ha
    rw [Nat.lt_one_iff, Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
    intro b hb
    simp only [properMultiples, Finset.mem_filter] at hb
    obtain ⟨hbA, hdvd, hne⟩ := hb
    exact h a b ha hbA hne hdvd

/-- **`k = 2` is exactly the Erdős #1062 condition.** A set is
`NoDividesKOthers 2` iff no element divides two distinct others
(`NoDividesTwoOthers`). -/
theorem noDividesKOthers_two_iff (A : Finset ℕ) :
    NoDividesKOthers 2 A ↔ NoDividesTwoOthers A := by
  constructor
  · intro h a b c ha hb hc hab hac hne_ab hne_ac hne_bc
    have hb' : b ∈ properMultiples a A := by
      simp only [properMultiples, Finset.mem_filter]; exact ⟨hb, hab, hne_ab⟩
    have hc' : c ∈ properMultiples a A := by
      simp only [properMultiples, Finset.mem_filter]; exact ⟨hc, hac, hne_ac⟩
    have hsub : ({b, c} : Finset ℕ) ⊆ properMultiples a A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb'
      · exact hc'
    have h2 : 2 ≤ (properMultiples a A).card := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hne_bc] at this
    exact absurd (h a ha) (Nat.not_lt.mpr h2)
  · intro h a ha
    by_contra hcon
    have hge : 1 < (properMultiples a A).card := by
      rw [Nat.not_lt] at hcon; omega
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp hge
    simp only [properMultiples, Finset.mem_filter] at hb hc
    obtain ⟨hbA, hab, hne_ab⟩ := hb
    obtain ⟨hcA, hac, hne_ac⟩ := hc
    exact h a b c ha hbA hcA hab hac hne_ab hne_ac hbc

/-
## Section IV: Strictly Climbing the Ladder
-/

/-- The ladder is strict: `{1, 2, 3}` is `NoDividesKOthers 3` but not
`NoDividesKOthers 2`, because `1` divides the two distinct others `2` and `3`.
Hence larger `k` is genuinely more permissive. -/
theorem ndko_three_not_two_example :
    NoDividesKOthers 3 ({1, 2, 3} : Finset ℕ) ∧
      ¬ NoDividesKOthers 2 ({1, 2, 3} : Finset ℕ) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    fin_cases ha <;> decide
  · intro h
    have h1 := h 1 (by decide)
    revert h1
    decide

/-
## Section V: The Extremal Function — Bounds
-/

/-- `maxNDKOSize k n ≤ n`: any subset of `{1,…,n}` has at most `n` elements. -/
theorem maxNDKOSize_le (k n : ℕ) : maxNDKOSize k n ≤ n := by
  unfold maxNDKOSize
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  have h := Finset.card_le_card hA.1
  rw [Nat.card_Icc] at h
  omega

/-- The extremal function is monotone in `n`. -/
theorem maxNDKOSize_mono_n {k m n : ℕ} (hmn : m ≤ n) :
    maxNDKOSize k m ≤ maxNDKOSize k n := by
  unfold maxNDKOSize
  apply Finset.sup_le
  intro A hA
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
  refine ⟨fun x hx => ?_, hA.2⟩
  have := hA.1 hx
  simp only [Finset.mem_Icc] at this ⊢
  omega

/-- The extremal function is monotone in `k`: more proper multiples are allowed,
so the optimum can only grow. -/
theorem maxNDKOSize_mono_k {k k' : ℕ} (hkk : k ≤ k') (n : ℕ) :
    maxNDKOSize k n ≤ maxNDKOSize k' n := by
  unfold maxNDKOSize
  apply Finset.sup_le
  intro A hA
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
  exact ⟨hA.1, noDividesKOthers_mono_k hkk hA.2⟩

/-- The upper-half interval `{⌊n/2⌋+1, …, n}` is primitive: no element has a
proper multiple `≤ n` (the smallest would be `2a > n`). Hence it satisfies
`NoDividesKOthers k` for every `k ≥ 1`. -/
private lemma noDivides_upper_half (k n : ℕ) (hk : 1 ≤ k) :
    NoDividesKOthers k (Finset.Icc (n / 2 + 1) n) := by
  intro a ha
  have hempty : properMultiples a (Finset.Icc (n / 2 + 1) n) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro b hb
    simp only [properMultiples, Finset.mem_filter, Finset.mem_Icc] at hb ha
    obtain ⟨⟨hb1, hb2⟩, hdvd, hne⟩ := hb
    obtain ⟨ha1, _⟩ := ha
    obtain ⟨j, rfl⟩ := hdvd
    have hj2 : 2 ≤ j := by
      by_contra h
      push_neg at h
      interval_cases j
      · simp only [Nat.mul_zero] at hb1; omega
      · simp only [Nat.mul_one] at hne; exact hne rfl
    have h1 : a * 2 ≤ a * j := Nat.mul_le_mul_left a hj2
    have h2 : (n / 2 + 1) * 2 ≤ a * 2 := Nat.mul_le_mul_right 2 ha1
    have hchain : (n / 2 + 1) * 2 ≤ n := le_trans (le_trans h2 h1) hb2
    omega
  rw [hempty, Finset.card_empty]
  omega

/-- **Lower bound.** For every `k ≥ 1`, `maxNDKOSize k n ≥ n - ⌊n/2⌋`, witnessed
by the primitive upper-half interval. Combined with `maxNDKOSize_le`, this
sandwiches the extremal function: `n - ⌊n/2⌋ ≤ maxNDKOSize k n ≤ n`. -/
theorem maxNDKOSize_ge_half (k n : ℕ) (hk : 1 ≤ k) :
    n - n / 2 ≤ maxNDKOSize k n := by
  have hcard : (Finset.Icc (n / 2 + 1) n).card ≤ maxNDKOSize k n := by
    apply Finset.le_sup
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun x hx => ?_, noDivides_upper_half k n hk⟩
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  rw [Nat.card_Icc] at hcard
  omega

/-- `maxNDKOSize k n ≥ 1` for `k ≥ 1` and `n ≥ 1`: the lower bound is at least
one (e.g. the singleton `{n}`). -/
theorem maxNDKOSize_ge_one (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    1 ≤ maxNDKOSize k n := by
  have := maxNDKOSize_ge_half k n hk
  omega

/-
## Section VI: The k-Dependent Lower Bound

The bound in Section V uses only the primitive upper-half interval and is
therefore `k`-independent. The sharper witness `{⌊n/(k+1)⌋+1,…,n}` exploits the
full `k`-fold allowance: each of its elements has at most `k-1` proper multiples
`≤ n`, yielding `maxNDKOSize k n ≥ n − ⌊n/(k+1)⌋`. For `k = 2` this is
`n − ⌊n/3⌋ ≈ 0.667n`, recovering the order of Lebensold's lower bound for the
base Erdős #1062 problem.
-/

/-- The interval `{⌊n/(k+1)⌋+1, …, n}` satisfies `NoDividesKOthers k`: every
element `a` there exceeds `n/(k+1)`, forcing `⌊n/a⌋ ≤ k`, so `a` has at most
`k-1` proper multiples `≤ n`. (The proper multiples of `a` that are `≤ n` are
`2a, 3a, …, ⌊n/a⌋·a`, i.e. `⌊n/a⌋-1` of them.) -/
private lemma noDivides_upper_kfold (k n : ℕ) (hk : 1 ≤ k) :
    NoDividesKOthers k (Finset.Icc (n / (k + 1) + 1) n) := by
  intro a ha
  simp only [Finset.mem_Icc] at ha
  obtain ⟨ha1, _⟩ := ha
  have ha0 : 0 < a := lt_of_lt_of_le (Nat.succ_pos _) ha1
  -- Key arithmetic: `n < a·(k+1)`, hence `⌊n/a⌋ ≤ k`.
  have hkey : n < a * (k + 1) := by
    have hmod : n % (k + 1) ≤ k := Nat.lt_succ_iff.mp (Nat.mod_lt n (by omega))
    have hdm := Nat.div_add_mod n (k + 1)
    have h2 : (n / (k + 1) + 1) * (k + 1) ≤ a * (k + 1) := Nat.mul_le_mul_right _ ha1
    have h3 : (n / (k + 1) + 1) * (k + 1)
        = (k + 1) * (n / (k + 1)) + (k + 1) := by ring
    omega
  have hnak : n / a ≤ k := by
    have h := (Nat.div_lt_iff_lt_mul ha0).mpr (by rw [Nat.mul_comm (k + 1) a]; exact hkey)
    omega
  -- Inject the proper multiples into `Icc 2 (⌊n/a⌋)` via `b ↦ b/a`.
  have hcard : (properMultiples a (Finset.Icc (n / (k + 1) + 1) n)).card
      ≤ (Finset.Icc 2 (n / a)).card := by
    apply Finset.card_le_card_of_injOn (f := fun b => b / a)
    · intro b hb
      have hbf := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      have hbIcc := Finset.mem_Icc.mp hbf.1
      obtain ⟨hb1, hb2⟩ := hbIcc
      obtain ⟨hdvd, hne⟩ := hbf.2
      obtain ⟨j, rfl⟩ := hdvd
      have hjval : a * j / a = j := Nat.mul_div_cancel_left j ha0
      have hmem : a * j / a ∈ Finset.Icc 2 (n / a) := by
        rw [Finset.mem_Icc, hjval]
        refine ⟨?_, ?_⟩
        · rcases Nat.lt_or_ge j 2 with hj | hj
          · interval_cases j
            · simp only [Nat.mul_zero] at hb1; omega
            · simp only [Nat.mul_one] at hne; exact absurd rfl hne
          · exact hj
        · rw [Nat.le_div_iff_mul_le ha0, Nat.mul_comm j a]; exact hb2
      simpa using hmem
    · intro b1 hb1 b2 hb2 heq
      have hdvd1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb1)).2.1
      have hdvd2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb2)).2.1
      have heq' : b1 / a = b2 / a := heq
      rw [← Nat.div_mul_cancel hdvd1, ← Nat.div_mul_cancel hdvd2, heq']
  rw [Nat.card_Icc] at hcard
  set q := n / a with hq
  omega

/-- **k-dependent lower bound.** For every `k ≥ 1`,
`maxNDKOSize k n ≥ n − ⌊n/(k+1)⌋`, witnessed by the interval
`{⌊n/(k+1)⌋+1, …, n}`. This strengthens `maxNDKOSize_ge_half` (the `k = 1`
case `n − ⌊n/2⌋`): for `k = 2` it gives `n − ⌊n/3⌋`, matching the order of
Lebensold's lower bound `0.6725n` for the Erdős #1062 extremal function. -/
theorem maxNDKOSize_ge_kfold (k n : ℕ) (hk : 1 ≤ k) :
    n - n / (k + 1) ≤ maxNDKOSize k n := by
  have hcard : (Finset.Icc (n / (k + 1) + 1) n).card ≤ maxNDKOSize k n := by
    apply Finset.le_sup
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun x hx => ?_, noDivides_upper_kfold k n hk⟩
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨le_trans (Nat.le_add_left 1 (n / (k + 1))) hx.1, hx.2⟩
  rw [Nat.card_Icc] at hcard
  set q := n / (k + 1) with hq
  omega
