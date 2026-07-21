/-
# Erdős Problem 46: Monochromatic Unit Fraction Representations

Does every finite colouring of the integers have a monochromatic solution to
`1 = ∑ 1/n_i` with `2 ≤ n₁ < n₂ < ⋯ < nₖ`?

Croot proved this in the affirmative, showing there are infinitely many
disjoint such monochromatic solutions. Erdős and Graham further asked whether
every positive rational `a/b` admits such a monochromatic representation.

*Reference:* [erdosproblems.com/46](https://www.erdosproblems.com/46)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

/- ## Unit fraction representations -/

/-- A finite set `S` of naturals (each ≥ 2) is a unit fraction representation
of `1` if `∑_{n ∈ S} 1/n = 1` as rationals. -/
def IsUnitFractionRepr (S : Finset ℕ) : Prop :=
    (∀ n ∈ S, 2 ≤ n) ∧ S.sum (fun n => (1 : ℚ) / n) = 1

/-- A set `S` is a unit fraction representation of a rational `q`. -/
def IsRatFractionRepr (S : Finset ℕ) (q : ℚ) : Prop :=
    (∀ n ∈ S, 2 ≤ n) ∧ S.sum (fun n => (1 : ℚ) / n) = q

/- ## Colourings -/

/-- A finite colouring of `ℕ` using `r` colours. -/
def FiniteColouring (r : ℕ) : Type :=
    ℕ → Fin r

/-- A set `S` is monochromatic under colouring `c` if all elements have the same colour. -/
def IsMonochromatic (c : FiniteColouring r) (S : Finset ℕ) : Prop :=
    ∃ col : Fin r, ∀ n ∈ S, c n = col

/- ## Main theorem (Croot) -/

/-- Erdős Problem 46 (proved by Croot): Every finite colouring of ℕ has a
monochromatic set `S ⊆ {n | 2 ≤ n}` with `∑_{n ∈ S} 1/n = 1`. -/
def ErdosProblem46 : Prop :=
    ∀ (r : ℕ) (hr : 0 < r) (c : FiniteColouring r),
      ∃ S : Finset ℕ, IsUnitFractionRepr S ∧ IsMonochromatic c S

/-- Stronger result: infinitely many disjoint monochromatic solutions exist. -/
def ErdosProblem46_infinitely_many : Prop :=
    ∀ (r : ℕ) (hr : 0 < r) (c : FiniteColouring r) (N : ℕ),
      ∃ S : Finset ℕ, IsUnitFractionRepr S ∧ IsMonochromatic c S ∧
        ∀ n ∈ S, N < n

/- ## Generalization to arbitrary rationals -/

/-- Erdős–Graham generalization: every finite colouring of ℕ has a monochromatic
representation of any positive rational `a/b`. -/
def ErdosGraham_rational : Prop :=
    ∀ (q : ℚ) (hq : 0 < q) (r : ℕ) (hr : 0 < r) (c : FiniteColouring r),
      ∃ S : Finset ℕ, IsRatFractionRepr S q ∧ IsMonochromatic c S

/-  The rational generalization follows from the infinitely-many version. -/
/- ## Basic properties -/

/-- The empty set is not a unit fraction representation (sum is 0 ≠ 1). -/
theorem not_unitFractionRepr_empty : ¬IsUnitFractionRepr ∅ := by
  intro ⟨_, hsum⟩
  simp at hsum

/-  A singleton {n} is a unit fraction representation iff n = 1, which contradicts n ≥ 2. -/
/-- Any monochromatic set under a 1-colouring is trivially monochromatic. -/
theorem mono_one_colour (c : FiniteColouring 1) (S : Finset ℕ) :
    IsMonochromatic c S := by
  exact ⟨0, fun n _ => Fin.eq_zero (c n)⟩

/-- If `S` is monochromatic and `T ⊆ S`, then `T` is monochromatic. -/
theorem mono_subset {r : ℕ} {c : FiniteColouring r} {S T : Finset ℕ}
    (hTS : T ⊆ S) (hS : IsMonochromatic c S) : IsMonochromatic c T := by
  obtain ⟨col, hcol⟩ := hS
  exact ⟨col, fun n hn => hcol n (hTS hn)⟩

/- ## Foundational lemmas

The following develop the def-only stub above into a body of axiom-free
elementary facts about unit-fraction / rational representations and
monochromatic sets: singleton/empty exclusions, the two-element lower bound,
term and positivity bounds, additivity over disjoint unions, and the reduction
of the base Croot statement to the infinitely-many version. -/

/-- No singleton `{n}` is a unit-fraction representation of `1`: the sum is
`1/n`, and for `n ≥ 2` we have `1/n < 1`. -/
theorem not_isUnitFractionRepr_singleton (n : ℕ) : ¬IsUnitFractionRepr {n} := by
  rintro ⟨hge, hsum⟩
  have hn : 2 ≤ n := hge n (mem_singleton_self n)
  rw [Finset.sum_singleton] at hsum
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt : (1 : ℚ) / n < 1 := by
    rw [div_lt_one hnpos]; exact_mod_cast (by omega : 1 < n)
  rw [hsum] at hlt
  exact lt_irrefl 1 hlt

/-- Membership in a set all of whose elements are `≥ 2` is subset-closed. -/
theorem forall_two_le_of_subset {S T : Finset ℕ} (hTS : T ⊆ S)
    (hS : ∀ n ∈ S, 2 ≤ n) : ∀ n ∈ T, 2 ≤ n :=
  fun n hn => hS n (hTS hn)

/-- Every element of a unit-fraction representation is positive. -/
theorem pos_of_mem_isUnitFractionRepr {S : Finset ℕ} (hS : IsUnitFractionRepr S)
    {n : ℕ} (hn : n ∈ S) : 0 < n := by
  have := hS.1 n hn; omega

/-- A unit-fraction representation of `1` has at least two elements: the empty
set sums to `0` and a singleton sums to `< 1`, so neither reaches `1`. -/
theorem two_le_card_of_isUnitFractionRepr {S : Finset ℕ}
    (hS : IsUnitFractionRepr S) : 2 ≤ S.card := by
  rcases eq_or_ne S.card 0 with h0 | h0
  · rw [Finset.card_eq_zero] at h0; subst h0
    exact absurd hS not_unitFractionRepr_empty
  rcases eq_or_ne S.card 1 with h1 | h1
  · rw [Finset.card_eq_one] at h1
    obtain ⟨a, rfl⟩ := h1
    exact absurd hS (not_isUnitFractionRepr_singleton a)
  omega

/-- Each term `1/n` with `n ≥ 2` is at most `1/2`. -/
theorem term_le_half {n : ℕ} (hn : 2 ≤ n) : (1 : ℚ) / n ≤ 1 / 2 := by
  have h2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  exact one_div_le_one_div_of_le (by norm_num) h2

/-- The reciprocal sum over any set of naturals is nonnegative. -/
theorem sum_inv_nonneg (S : Finset ℕ) : 0 ≤ S.sum (fun n => (1 : ℚ) / n) := by
  apply Finset.sum_nonneg
  intro n _; positivity

/-- At `q = 1`, a rational representation is exactly a unit-fraction
representation. -/
theorem isRatFractionRepr_one_iff (S : Finset ℕ) :
    IsRatFractionRepr S 1 ↔ IsUnitFractionRepr S := Iff.rfl

/-- The rational a set represents is unique (it is the reciprocal sum). -/
theorem isRatFractionRepr_unique {S : Finset ℕ} {q p : ℚ}
    (hq : IsRatFractionRepr S q) (hp : IsRatFractionRepr S p) : q = p := by
  rw [← hq.2, ← hp.2]

/-- A rational representation by a nonempty set represents a positive rational. -/
theorem isRatFractionRepr_pos {S : Finset ℕ} {q : ℚ}
    (hS : IsRatFractionRepr S q) (hne : S.Nonempty) : 0 < q := by
  rw [← hS.2]
  apply Finset.sum_pos _ hne
  intro n hn
  have hnpos : (0 : ℚ) < n := by
    have := hS.1 n hn; exact_mod_cast (by omega : 0 < n)
  positivity

/-- Rational representations add over disjoint unions: representing `q` on `S`
and `p` on a disjoint `T` gives a representation of `q + p` on `S ∪ T`. This is
the arithmetic backbone of assembling disjoint monochromatic solutions. -/
theorem isRatFractionRepr_union {S T : Finset ℕ} {q p : ℚ}
    (hdisj : Disjoint S T) (hS : IsRatFractionRepr S q)
    (hT : IsRatFractionRepr T p) : IsRatFractionRepr (S ∪ T) (q + p) := by
  obtain ⟨hS2, hSsum⟩ := hS
  obtain ⟨hT2, hTsum⟩ := hT
  refine ⟨fun n hn => ?_, ?_⟩
  · rcases Finset.mem_union.mp hn with h | h
    · exact hS2 n h
    · exact hT2 n h
  · rw [Finset.sum_union hdisj, hSsum, hTsum]

/-- The empty set is monochromatic under any colouring with at least one
colour (vacuously, using colour `0`). -/
theorem isMonochromatic_empty {r : ℕ} (hr : 0 < r) (c : FiniteColouring r) :
    IsMonochromatic c (∅ : Finset ℕ) :=
  ⟨⟨0, hr⟩, fun n hn => by simp at hn⟩

/-- Every singleton is monochromatic under any colouring. -/
theorem isMonochromatic_singleton {r : ℕ} (c : FiniteColouring r) (n : ℕ) :
    IsMonochromatic c ({n} : Finset ℕ) :=
  ⟨c n, fun m hm => by rw [Finset.mem_singleton.mp hm]⟩

/-- The base Croot statement (Erdős Problem 46) follows from the stronger
infinitely-many-disjoint-solutions version by taking the threshold `N = 0`. -/
theorem erdosProblem46_of_infinitely_many
    (h : ErdosProblem46_infinitely_many) : ErdosProblem46 := by
  intro r hr c
  obtain ⟨S, hrepr, hmono, _⟩ := h r hr c 0
  exact ⟨S, hrepr, hmono⟩

/-! ## Unit-fraction splitting and a concrete representation

The Fibonacci–Sylvester *splitting identity* `1/n = 1/(n+1) + 1/(n(n+1))` is the
elementary engine behind unit-fraction constructions: it replaces one reciprocal by
two strictly larger ones with the same total. Together with a concrete base
representation it witnesses that `IsUnitFractionRepr` is inhabited. -/

/-- **Telescoping identity.** `1/(n(n+1)) = 1/n - 1/(n+1)` for `n ≥ 1` (as rationals). -/
theorem inv_mul_succ (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℚ) / (n * (n + 1)) = 1 / n - 1 / (n + 1) := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **Splitting identity.** `1/n = 1/(n+1) + 1/(n(n+1))` for `n ≥ 1`: a single unit
fraction splits into two strictly larger ones with the same sum. The Fibonacci–Sylvester
step used to lengthen unit-fraction representations. -/
theorem split_unit_fraction (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℚ) / n = 1 / (n + 1) + 1 / (n * (n + 1)) := by
  rw [inv_mul_succ n hn]; ring

/-- **A concrete unit-fraction representation of `1`:** `{2, 3, 6}`, since
`1/2 + 1/3 + 1/6 = 1`. Witnesses that `IsUnitFractionRepr` is inhabited. -/
theorem isUnitFractionRepr_two_three_six :
    IsUnitFractionRepr ({2, 3, 6} : Finset ℕ) := by
  refine ⟨?_, ?_⟩
  · decide
  · norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

/-- Unit-fraction representations of `1` exist. -/
theorem exists_isUnitFractionRepr : ∃ S : Finset ℕ, IsUnitFractionRepr S :=
  ⟨{2, 3, 6}, isUnitFractionRepr_two_three_six⟩

/-- **Term-replacement / lengthening step.** Given a unit-fraction representation `S`
containing `m`, if the two split denominators `m+1` and `m(m+1)` are not already in `S`,
then replacing `m` by `{m+1, m(m+1)}` (via the splitting identity) yields another
unit-fraction representation of `1`. This is the elementary induction step behind
producing arbitrarily long — and, with disjoint choices, infinitely many — monochromatic
representations. -/
theorem isUnitFractionRepr_replace
    {S : Finset ℕ} (hS : IsUnitFractionRepr S) {m : ℕ} (hm : m ∈ S)
    (h1 : m + 1 ∉ S) (h2 : m * (m + 1) ∉ S) :
    IsUnitFractionRepr (insert (m + 1) (insert (m * (m + 1)) (S.erase m))) := by
  obtain ⟨hge, hsum⟩ := hS
  have hm2 : 2 ≤ m := hge m hm
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm2
  have h2erase : m * (m + 1) ∉ S.erase m := fun h => h2 (Finset.mem_of_mem_erase h)
  have hne : m + 1 ≠ m * (m + 1) := by nlinarith
  have h1insert : m + 1 ∉ insert (m * (m + 1)) (S.erase m) := by
    simp only [Finset.mem_insert]
    push_neg
    exact ⟨hne, fun h => h1 (Finset.mem_of_mem_erase h)⟩
  refine ⟨?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_insert] at hn
    rcases hn with rfl | rfl | hn
    · omega
    · nlinarith
    · exact hge n (Finset.mem_of_mem_erase hn)
  · rw [Finset.sum_insert h1insert, Finset.sum_insert h2erase]
    have herase : (S.erase m).sum (fun n => (1 : ℚ) / n) = 1 - 1 / m := by
      have hadd := Finset.add_sum_erase S (fun n => (1 : ℚ) / n) hm
      rw [hsum] at hadd
      linarith [hadd]
    have hcast1 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
    have hcast2 : ((m * (m + 1) : ℕ) : ℚ) = (m : ℚ) * ((m : ℚ) + 1) := by push_cast; ring
    have hsplit := split_unit_fraction m hm1
    rw [herase]
    simp only [hcast1, hcast2]
    linarith [hsplit]

/-- **Arbitrarily long unit-fraction representations of `1`.** For every `k` there
is a representation `S` with `k ≤ |S|`.  Induction on `k`: start from `{2, 3, 6}`
and, at each step, split the *largest* denominator `m` of the current
representation via `isUnitFractionRepr_replace` — both split denominators `m+1` and
`m(m+1)` exceed `m` (hence lie outside `S`), so the replacement is legal and
strictly increases the cardinality by one. -/
theorem exists_isUnitFractionRepr_card_ge (k : ℕ) :
    ∃ S : Finset ℕ, IsUnitFractionRepr S ∧ k ≤ S.card := by
  induction k with
  | zero => exact ⟨{2, 3, 6}, isUnitFractionRepr_two_three_six, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨S, hS, hcard⟩ := ih
    have hc2 : 2 ≤ S.card := two_le_card_of_isUnitFractionRepr hS
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    -- split the largest denominator `m`
    set m := S.max' hne with hm_def
    have hmS : m ∈ S := S.max'_mem hne
    have hmax : ∀ a ∈ S, a ≤ m := fun a ha => S.le_max' a ha
    have hm2 : 2 ≤ m := (hS.1) m hmS
    -- `m+1` and `m(m+1)` both exceed `m`, so neither is already in `S`
    have h1 : m + 1 ∉ S := fun h => by have := hmax _ h; omega
    have h2 : m * (m + 1) ∉ S := fun h => by
      have := hmax _ h; nlinarith
    have hrepl := isUnitFractionRepr_replace hS hmS h1 h2
    refine ⟨insert (m + 1) (insert (m * (m + 1)) (S.erase m)), hrepl, ?_⟩
    -- the replacement raises the cardinality by exactly one
    have hne' : m + 1 ≠ m * (m + 1) := by nlinarith
    have h2erase : m * (m + 1) ∉ S.erase m := fun h => h2 (Finset.mem_of_mem_erase h)
    have h1insert : m + 1 ∉ insert (m * (m + 1)) (S.erase m) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hne', fun h => h1 (Finset.mem_of_mem_erase h)⟩
    rw [Finset.card_insert_of_notMem h1insert, Finset.card_insert_of_notMem h2erase,
      Finset.card_erase_of_mem hmS]
    omega

/-- **There are infinitely many distinct unit-fraction representations of `1`.**
Consequence of `exists_isUnitFractionRepr_card_ge`: the representations have
unbounded cardinality, so the set of them cannot be finite (a finite family of
`Finset`s would have bounded cardinality). This is the elementary,
colouring-free lower bound behind Erdős Problem 46 — the deep monochromatic
statement (Croot 2003) remains unformalized. -/
theorem infinite_isUnitFractionRepr :
    {S : Finset ℕ | IsUnitFractionRepr S}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image Finset.card).bddAbove
  obtain ⟨S, hS, hcard⟩ := exists_isUnitFractionRepr_card_ge (M + 1)
  have hle : S.card ≤ M := hM ⟨S, hS, rfl⟩
  omega

/-! ## Multiplicative scaling of representations

`isRatFractionRepr_union` above assembles representations *additively* (over disjoint
unions of denominator sets). The complementary *multiplicative* engine scales every
denominator by a common factor `t`: this divides the represented rational by `t` and
pushes every denominator up to at least `2t`. It is the natural tool for producing
representations whose denominators are all large — a prerequisite for the pairwise-disjoint
chaining behind `ErdosProblem46_infinitely_many` (reprs with `min > N` are automatically
disjoint from any repr supported below `N`). -/

/-- **Scaling lemma.** If `S` represents the rational `q`, then scaling every denominator by
`t ≥ 1` (the map `n ↦ t · n`, injective since `t > 0`) yields a representation of `q / t`.
The multiplicative counterpart of `isRatFractionRepr_union`. -/
theorem isRatFractionRepr_smul {S : Finset ℕ} {q : ℚ}
    (hS : IsRatFractionRepr S q) {t : ℕ} (ht : 1 ≤ t) :
    IsRatFractionRepr (S.image (fun n => t * n)) (q / t) := by
  obtain ⟨hge, hsum⟩ := hS
  have htpos : 0 < t := ht
  have hinj : ∀ a ∈ S, ∀ b ∈ S, t * a = t * b → a = b :=
    fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left htpos hab
  refine ⟨?_, ?_⟩
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    have hn2 : 2 ≤ n := hge n hn
    have hle : n ≤ t * n := Nat.le_mul_of_pos_left n htpos
    omega
  · rw [Finset.sum_image hinj]
    have hterm : ∀ n ∈ S, (1 : ℚ) / (↑(t * n)) = (1 / t) * (1 / n) := by
      intro n _
      push_cast
      rw [one_div, one_div, one_div, mul_inv]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum]
    ring

/-- **Arbitrarily large denominators for `1/t`.** For every `t ≥ 1`, the reciprocal `1/t`
has a rational representation `{2t, 3t, 6t}` (the concrete representation `{2,3,6}` of `1`
scaled by `t`) whose denominators are all `≥ 2t`. Witnesses that the large-denominator
regime is reachable for reciprocals of arbitrary size. -/
theorem exists_isRatFractionRepr_inv_min_ge (t : ℕ) (ht : 1 ≤ t) :
    ∃ S : Finset ℕ, IsRatFractionRepr S (1 / t) ∧ ∀ n ∈ S, 2 * t ≤ n := by
  refine ⟨({2, 3, 6} : Finset ℕ).image (fun n => t * n), ?_, ?_⟩
  · have h236 : IsRatFractionRepr ({2, 3, 6} : Finset ℕ) 1 :=
      (isRatFractionRepr_one_iff _).mpr isUnitFractionRepr_two_three_six
    exact isRatFractionRepr_smul h236 ht
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    fin_cases hn <;> omega
