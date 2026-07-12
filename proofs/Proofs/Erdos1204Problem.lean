/-
Erdős Problem #1204: Admissible Sequences

We call a sequence of integers 0 ≤ a₁ < ⋯ < a_k *admissible* if it is missing
at least one congruence class modulo every prime p. (This is exactly the
notion of an "admissible k-tuple" from the Hardy–Littlewood prime k-tuples
conjecture and the bounded-gaps-between-primes work of Zhang, Maynard, Tao.)

Let A(k) = min a_k over admissible k-element sequences.

**Main Questions (OPEN)**:
1. Estimate A(k). In particular, is it true that A(k) ∼ k log k?
2. Estimate B(k) = min (a₁ + ⋯ + a_k)/k.

**What is formalized here**:
- `Admissible`: a finite set of naturals misses a residue class mod every prime.
- `missing_class_of_card_lt`: a set of size < p always misses a class mod p
  (only `card` distinct residues can be occupied, and there are `p` of them).
- `admissible_iff_card`: **the key reduction** — admissibility is equivalent to
  missing a class modulo every prime `p ≤ card`; all larger primes are automatic.
- Worked examples: `∅`, `{0}`, `{0,2}` are admissible; `{0,1}` is not (it covers
  both classes mod 2).

The asymptotic questions A(k) ∼ k log k and the estimate for B(k) are OPEN and
are not asserted here.

Reference: https://erdosproblems.com/1204
-/

import Mathlib

open Finset

namespace Erdos1204

/- ## Definition -/

/-- A finite set `a ⊆ ℕ` is **admissible** if, for every prime `p`, it misses at
least one residue class modulo `p`: there is some `r : ZMod p` not equal to `↑x`
for any `x ∈ a`. -/
def Admissible (a : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ x ∈ a, (x : ZMod p) ≠ r

/- ## The reduction to small primes

The content of admissibility lies entirely in the small primes `p ≤ |a|`. For a
prime `p` larger than `|a|`, the `|a|` elements occupy at most `|a| < p` of the
`p` residue classes, so some class is automatically missed. -/

/-- A set with fewer than `p` elements always misses a residue class modulo `p`:
its image in `ZMod p` cannot be all of `ZMod p`. -/
theorem missing_class_of_card_lt {a : Finset ℕ} {p : ℕ} [NeZero p]
    (h : a.card < p) : ∃ r : ZMod p, ∀ x ∈ a, (x : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ r, ∃ x ∈ a, (x : ZMod p) = r, i.e. the image is all of ZMod p
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ a.image (fun x : ℕ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have hle : (Finset.univ : Finset (ZMod p)).card ≤ a.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card p] at hle
  omega

/-- **Key reduction.** A finite set is admissible iff it misses a residue class
modulo every prime `p` that is at most its cardinality. Larger primes impose no
constraint. -/
theorem admissible_iff_card {a : Finset ℕ} :
    Admissible a ↔
      ∀ p : ℕ, p.Prime → p ≤ a.card → ∃ r : ZMod p, ∀ x ∈ a, (x : ZMod p) ≠ r := by
  constructor
  · intro ha p hp _; exact ha p hp
  · intro h p hp
    rcases le_or_gt p a.card with hle | hlt
    · exact h p hp hle
    · haveI : NeZero p := ⟨hp.pos.ne'⟩
      exact missing_class_of_card_lt hlt

/- ## Examples -/

/-- The empty set is admissible (it misses every class). -/
theorem admissible_empty : Admissible (∅ : Finset ℕ) :=
  fun p _ => ⟨0, by simp⟩

/-- Every singleton is admissible: with only one element occupied there is
nothing to check below `p = 2`, and `missing_class_of_card_lt` handles the rest. -/
theorem admissible_singleton (n : ℕ) : Admissible ({n} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  rw [Finset.card_singleton] at hcard
  -- p ≤ 1 contradicts p prime (p ≥ 2)
  have := hp.two_le
  exfalso; omega

/-- `{0, 2}` is admissible: modulo 2 both elements are even, so the odd class
is missed; modulo every larger prime the size bound applies. This is the
smallest nontrivial admissible 2-tuple. -/
theorem admissible_zero_two : Admissible ({0, 2} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  -- card {0,2} = 2, so the only prime to check is p = 2
  have hc : ({0, 2} : Finset ℕ).card = 2 := by decide
  rw [hc] at hcard
  interval_cases p
  · exact absurd hp (by decide)   -- p = 0
  · exact absurd hp (by decide)   -- p = 1
  · -- p = 2: miss the class 1
    refine ⟨1, ?_⟩
    intro x hx
    fin_cases hx <;> decide

/-- `{0, 1}` is **not** admissible: modulo 2 it occupies both residue classes,
so no class is missed. -/
theorem not_admissible_zero_one : ¬ Admissible ({0, 1} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr⟩ := h 2 (by decide)
  -- both residue classes 0 and 1 mod 2 are occupied, so no r is missed
  fin_cases r
  · exact (hr 0 (by decide)) (by decide)
  · exact (hr 1 (by decide)) (by decide)

/- ## Structural properties

Admissibility is closed downward and is invariant under translation, and admissible
`k`-tuples exist for every `k` — so the extremal quantity `A(k)` is well-defined. -/

/-- **Downward closure.** Any subset of an admissible set is admissible: a residue class
missed by `a` mod `p` is still missed by any subset of `a`. -/
theorem Admissible.subset {a b : Finset ℕ} (ha : Admissible a) (hba : b ⊆ a) :
    Admissible b := by
  intro p hp
  obtain ⟨r, hr⟩ := ha p hp
  exact ⟨r, fun x hx => hr x (hba hx)⟩

/-- **Translation invariance.** Translating every element by a fixed `t` preserves
admissibility: if `a` misses class `r` modulo `p`, then `a + t` misses class `r + t`.
Admissibility depends only on the *pattern* of a tuple, not its position. -/
theorem admissible_image_add {a : Finset ℕ} (t : ℕ) (ha : Admissible a) :
    Admissible (a.image (· + t)) := by
  intro p hp
  obtain ⟨r, hr⟩ := ha p hp
  refine ⟨r + (t : ZMod p), fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hx' := hr x hx
  push_cast
  exact fun h => hx' (add_right_cancel h)

/-- Translation by a fixed `t` is injective, so it preserves cardinality: it sends
admissible `k`-tuples to admissible `k`-tuples. -/
theorem card_image_add (a : Finset ℕ) (t : ℕ) :
    (a.image (· + t)).card = a.card :=
  Finset.card_image_of_injective _ (add_left_injective t)

/-- **Translation invariance under subtraction.** The downward companion of
`admissible_image_add`: if every element of an admissible set is at least `t`, then subtracting
`t` from every element preserves admissibility (`a` missing class `r` mod `p` gives `a - t`
missing `r - t`). This is what lets an admissible tuple be *normalised to start at `0`* without
losing admissibility. -/
theorem admissible_image_sub {a : Finset ℕ} (t : ℕ) (ha : Admissible a)
    (ht : ∀ x ∈ a, t ≤ x) : Admissible (a.image (· - t)) := by
  intro p hp
  obtain ⟨r, hr⟩ := ha p hp
  refine ⟨r - (t : ZMod p), fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hxt : t ≤ x := ht x hx
  have hx' := hr x hx
  intro h
  apply hx'
  have hcast : ((x - t : ℕ) : ZMod p) = (x : ZMod p) - (t : ZMod p) := by
    push_cast [Nat.cast_sub hxt]; ring
  rw [hcast] at h
  have := congrArg (· + (t : ZMod p)) h
  simpa using this

/-- **Existence / well-definedness of `A(k)`.** For every `k` there is an admissible set of
size exactly `k`, so the extremal value `A(k) = min a_k` is taken over a nonempty family.

Construction: the multiples `0, N, 2N, …, (k-1)N` of the primorial
`N = ∏_{p ≤ k, p prime} p`. Modulo each prime `p ≤ k` every element is `≡ 0` (since `p ∣ N`),
so the class `1` is missed; primes `p > k = card` are automatic by `missing_class_of_card_lt`.
This also gives the explicit (weak) upper bound `A(k) ≤ (k-1)·∏_{p ≤ k} p`. -/
theorem exists_admissible_card (k : ℕ) :
    ∃ a : Finset ℕ, a.card = k ∧ Admissible a := by
  classical
  -- An `N > 0` divisible by every prime `p ≤ k` (the primorial works).
  obtain ⟨N, hNpos, hNdvd⟩ : ∃ N : ℕ, 0 < N ∧ ∀ p, p.Prime → p ≤ k → p ∣ N := by
    refine ⟨((Finset.range (k + 1)).filter Nat.Prime).prod id, ?_, ?_⟩
    · exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.pos)
    · intro p hp hpk
      exact Finset.dvd_prod_of_mem id
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
  have hinj : Function.Injective (fun x : ℕ => x * N) :=
    fun x y h => Nat.eq_of_mul_eq_mul_right hNpos h
  refine ⟨(Finset.range k).image (fun x => x * N), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  · rw [admissible_iff_card, Finset.card_image_of_injective _ hinj, Finset.card_range]
    intro p hp hpk
    haveI : Fact p.Prime := ⟨hp⟩
    have hp0 : (N : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p N).mpr (hNdvd p hp hpk)
    refine ⟨1, fun x hx => ?_⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    push_cast
    rw [hp0, mul_zero]
    exact zero_ne_one

/- ## The parity constraint and a sharper diameter bound

The trivial packing bound says `k` distinct naturals span at least `k - 1`. The smallest
prime already doubles this: modulo `2` an admissible set misses a residue class, and `ZMod 2`
has only two classes, so **every element shares the same parity**. Distinct same-parity
naturals differ by at least `2`, so an admissible `k`-set has diameter `≥ 2(k-1)`. This is the
leading term of the sieve heuristic behind the conjecture `A(k) ∼ k log k`. -/

/-- **All elements of an admissible set share parity.** Modulo the prime `2` the set misses a
residue class, and `ZMod 2` has only two classes, so the remaining class holds every element. -/
theorem admissible_same_parity {a : Finset ℕ} (ha : Admissible a) {x y : ℕ}
    (hx : x ∈ a) (hy : y ∈ a) : (x : ZMod 2) = (y : ZMod 2) := by
  obtain ⟨r, hr⟩ := ha 2 (by norm_num)
  -- in `ZMod 2`, two elements both `≠ r` must be equal (only two classes)
  have key : ∀ (s z w : ZMod 2), z ≠ s → w ≠ s → z = w := by decide
  exact key r _ _ (hr x hx) (hr y hy)

/-- **Parity lower bound on the diameter.** Any nonempty admissible set has diameter
`max - min ≥ 2(card - 1)`: its elements share parity (`admissible_same_parity`), so the
map `x ↦ (x - min)/2` injects `a` into `{0, 1, …, (max-min)/2}`, forcing
`card ≤ (max-min)/2 + 1`. This doubles the trivial packing bound `card - 1`. -/
theorem admissible_diam_ge {a : Finset ℕ} (ha : Admissible a) (hne : a.Nonempty) :
    2 * (a.card - 1) ≤ a.max' hne - a.min' hne := by
  classical
  -- every element is `≥ min`, `≤ max`, and `≡ min (mod 2)`, hence `2 ∣ x - min`
  have hdvd : ∀ x ∈ a, 2 ∣ (x - a.min' hne) := by
    intro x hx
    have hmx : a.min' hne ≤ x := a.min'_le x hx
    have hpar : ((a.min' hne : ℕ) : ZMod 2) = (x : ZMod 2) :=
      admissible_same_parity ha (a.min'_mem hne) hx
    rw [ZMod.natCast_eq_natCast_iff] at hpar
    exact (Nat.modEq_iff_dvd' hmx).mp hpar
  -- `x ↦ (x - min)/2` maps `a` into `range ((max-min)/2 + 1)` ...
  have hmono : ∀ x ∈ a, (x - a.min' hne) / 2 ∈ Finset.range ((a.max' hne - a.min' hne)/2 + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hxM : x ≤ a.max' hne := a.le_max' x hx
    have hmx : a.min' hne ≤ x := a.min'_le x hx
    omega
  -- ... and it is injective (distinct same-parity values give distinct halves)
  have hinj : Set.InjOn (fun x => (x - a.min' hne) / 2) a := by
    intro x hx y hy hxy
    simp only at hxy
    have hmx : a.min' hne ≤ x := a.min'_le x hx
    have hmy : a.min' hne ≤ y := a.min'_le y hy
    obtain ⟨u, hu⟩ := hdvd x hx
    obtain ⟨v, hv⟩ := hdvd y hy
    omega
  have hcard : a.card ≤ (a.max' hne - a.min' hne)/2 + 1 := by
    have h := Finset.card_le_card_of_injOn
      (f := fun x => (x - a.min' hne) / 2)
      (t := Finset.range ((a.max' hne - a.min' hne)/2 + 1)) hmono hinj
    simpa using h
  omega

/- ## The extremal quantity `A(k)`

The headline question of Problem #1204 concerns `A(k) = min a_k`, the minimal possible
*largest element* of an admissible `k`-set. We now make this object precise. Because
admissible `k`-sets exist for every `k` (`exists_admissible_card`), the set of achievable
maxima is nonempty, so its infimum (`A k`) is attained. We bracket it between the trivial
packing bound `k - 1` and the primorial bound, and compute the first values exactly. The
exact value `A(2) = 2 > 1 = k - 1` is the first place where admissibility is *binding*:
the densest 2-set `{0,1}` is inadmissible, forcing the max strictly above the packing bound. -/

/-- The largest element (`a.sup id`) of any `k`-element finset of `ℕ` is at least `k - 1`:
the `k` distinct elements all lie in `{0, 1, …, a.sup id}`, which has `a.sup id + 1`
members. -/
theorem card_le_sup_succ (a : Finset ℕ) : a.card ≤ a.sup id + 1 := by
  have hsub : a ⊆ Finset.range (a.sup id + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have : x ≤ a.sup id := Finset.le_sup (f := id) hx
    omega
  calc a.card ≤ (Finset.range (a.sup id + 1)).card := Finset.card_le_card hsub
    _ = a.sup id + 1 := Finset.card_range _

/-- **`A(k)`**, the minimal largest element over admissible `k`-element sets. We use
`a.sup id` (the maximum, with the empty set giving `0`) so that `A` is total; for `k ≥ 1`
this is exactly `min a_k`. The minimization is over a nonempty family
(`exists_admissible_card`), so the infimum is attained (`A_mem`). -/
noncomputable def A (k : ℕ) : ℕ :=
  sInf { m | ∃ a : Finset ℕ, a.card = k ∧ Admissible a ∧ a.sup id = m }

/-- The family of achievable maxima is nonempty (an admissible `k`-set always exists). -/
theorem A_set_nonempty (k : ℕ) :
    { m | ∃ a : Finset ℕ, a.card = k ∧ Admissible a ∧ a.sup id = m }.Nonempty := by
  obtain ⟨a, hcard, ha⟩ := exists_admissible_card k
  exact ⟨a.sup id, a, hcard, ha, rfl⟩

/-- The infimum defining `A(k)` is **attained**: there is an admissible `k`-set whose
largest element equals `A(k)`. -/
theorem A_mem (k : ℕ) :
    ∃ a : Finset ℕ, a.card = k ∧ Admissible a ∧ a.sup id = A k :=
  Nat.sInf_mem (A_set_nonempty k)

/-- `A(k)` is a lower bound: any admissible `k`-set has largest element at least `A(k)`. -/
theorem A_le {k : ℕ} {a : Finset ℕ} (hcard : a.card = k) (ha : Admissible a) :
    A k ≤ a.sup id :=
  Nat.sInf_le ⟨a, hcard, ha, rfl⟩

/-- **One-step monotonicity.** `A(k) ≤ A(k+1)`: deleting one element from an optimal
admissible `(k+1)`-set leaves an admissible `k`-set (admissibility passes to subsets,
`Admissible.subset`) whose largest element is no larger (`Finset.sup_mono`), so its
diameter — which is `≥ A(k)` — bounds `A(k+1)` from above. -/
theorem A_le_A_succ (k : ℕ) : A k ≤ A (k + 1) := by
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem (k + 1)
  have hne : a.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  obtain ⟨x, hx⟩ := hne
  have hsub : a.erase x ⊆ a := fun y hy => Finset.mem_of_mem_erase hy
  have hcard' : (a.erase x).card = k := by
    rw [Finset.card_erase_of_mem hx, hcard, Nat.add_sub_cancel]
  have ha' : Admissible (a.erase x) := ha.subset hsub
  calc A k ≤ (a.erase x).sup id := A_le hcard' ha'
    _ ≤ a.sup id := Finset.sup_mono hsub
    _ = A (k + 1) := hsup

/-- **`A` is monotone.** The minimal-diameter function `A(k)` is non-decreasing in `k`:
a larger admissible tuple can only need a larger diameter. Immediate from the one-step
bound `A_le_A_succ`. -/
theorem A_monotone : Monotone A :=
  monotone_nat_of_le_succ A_le_A_succ

/-- **Strict one-step monotonicity.** For `k ≥ 1`, `A(k) < A(k+1)`. Deleting the
*largest* element (rather than an arbitrary one) from an optimal admissible
`(k+1)`-set leaves an admissible `k`-set whose maximum is *strictly* smaller: every
surviving element lies below the deleted maximum. Since `A(k)` bounds that smaller
maximum and the deleted maximum is `A(k+1)`, we get `A(k) < A(k+1)`.

This sharpens `A_le_A_succ` from `≤` to `<`: no two distinct admissible-tuple sizes
`k ≥ 1` share a minimal diameter — the exact-value frontier
`A(2)=2, A(3)=6, A(4)=8, …` is genuinely strictly increasing. -/
theorem A_lt_A_succ {k : ℕ} (hk : 1 ≤ k) : A k < A (k + 1) := by
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem (k + 1)
  have hne : a.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  obtain ⟨x, hxa, hxsup⟩ := Finset.exists_mem_eq_sup a hne id
  have hsub : a.erase x ⊆ a := fun y hy => Finset.mem_of_mem_erase hy
  have hcard' : (a.erase x).card = k := by
    rw [Finset.card_erase_of_mem hxa, hcard, Nat.add_sub_cancel]
  have ha' : Admissible (a.erase x) := ha.subset hsub
  -- The maximum `x` is positive: `a` has `k + 1 ≥ 2` distinct naturals, so `x ≥ k ≥ 1`.
  have hxpos : 0 < x := by
    have hcs := card_le_sup_succ a
    rw [hcard, hxsup] at hcs
    simp only [id_eq] at hcs
    omega
  -- Every surviving element is strictly below the deleted maximum `x`.
  have hlt : (a.erase x).sup id < x := by
    rw [Finset.sup_lt_iff (by simpa using hxpos)]
    intro y hy
    have hya : y ∈ a := Finset.mem_of_mem_erase hy
    have hyne : y ≠ x := Finset.ne_of_mem_erase hy
    have hle : id y ≤ a.sup id := Finset.le_sup hya
    rw [hxsup] at hle
    simp only [id_eq] at hle ⊢
    omega
  have hup : A k ≤ (a.erase x).sup id := A_le hcard' ha'
  have hlt2 : (a.erase x).sup id < a.sup id := by rw [hxsup]; simpa using hlt
  omega

/-- **The frontier is strictly increasing.** Reindexing by `j ↦ A(j+1)` (so the
domain starts at the first strictly-increasing index `k = 1`), `A` is strictly
monotone. Packages `A_lt_A_succ`, which holds for every `k ≥ 1`. -/
theorem A_succ_strictMono : StrictMono (fun j => A (j + 1)) :=
  strictMono_nat_of_lt_succ (fun j => A_lt_A_succ (by omega))

/-- **`A(k)` is always even.** Every value of the extremal function is divisible by `2` — the
structural fact behind the observed table `A(0)=A(1)=0, A(2)=2, A(3)=6, A(4)=8, A(5)=12, …`, all
even.

Reason: an optimal admissible `k`-set (`A_mem`) can be *normalised to start at `0`* by subtracting
its minimum (`admissible_image_sub`); the normalised set is still admissible, still has `k`
elements, and its maximum is no larger — hence equals `A(k)` by minimality. But a set containing
`0` is (by the prime `2`) entirely even (`admissible_same_parity`), so its maximum `A(k)` is even.
This is the exact-value analogue of the prime-`2` diameter bound `two_mul_sub_one_le_A`: prime `2`
does not merely double the packing bound, it pins the *parity* of the optimum. -/
theorem A_even (k : ℕ) : 2 ∣ A k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- `A 0 = 0` (only the empty set is a `0`-set), which is even.
    have h00 : A 0 = 0 :=
      Nat.le_zero.mp (by simpa using A_le (a := (∅ : Finset ℕ)) Finset.card_empty admissible_empty)
    subst hk; simp [h00]
  · obtain ⟨a, hcard, ha, hsup⟩ := A_mem k
    have hne : a.Nonempty := by rw [← Finset.card_pos, hcard]; omega
    set m := a.min' hne with hm
    have hmle : ∀ x ∈ a, m ≤ x := fun x hx => a.min'_le x hx
    set a' := a.image (· - m) with ha'
    have hinj : Set.InjOn (· - m) a := by
      intro x hx y hy hxy
      simp only at hxy
      have hx' := hmle x hx; have hy' := hmle y hy; omega
    have hcard' : a'.card = k := by
      rw [ha', Finset.card_image_of_injOn hinj, hcard]
    have ha'adm : Admissible a' := admissible_image_sub m ha hmle
    -- every element of the normalised set is `≤ A k`, so its `sup` is too; minimality gives `=`.
    have hle_sup : a'.sup id ≤ A k := by
      rw [ha']
      apply Finset.sup_le
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      simp only [id_eq]
      have hxle : x ≤ a.sup id := Finset.le_sup (f := id) hx
      rw [hsup] at hxle; omega
    have hsup' : a'.sup id = A k := le_antisymm hle_sup (A_le hcard' ha'adm)
    -- `0 ∈ a'` (the minimum maps to `0`), forcing every element — hence the maximum — even.
    have h0 : (0 : ℕ) ∈ a' := by
      rw [ha']
      refine Finset.mem_image.mpr ⟨m, a.min'_mem hne, ?_⟩
      omega
    obtain ⟨z, hz, hzeq⟩ := Finset.exists_mem_eq_sup a' ⟨0, h0⟩ id
    have hzeven : (z : ZMod 2) = (0 : ZMod 2) := by
      simpa using admissible_same_parity ha'adm hz h0
    have hdvd : 2 ∣ z := (ZMod.natCast_eq_zero_iff z 2).mp (by simpa using hzeven)
    rw [← hsup', hzeq]
    simpa [id_eq] using hdvd

/-- **Even step size.** For `k ≥ 1`, consecutive values of `A` differ by at least `2`:
`A(k) + 2 ≤ A(k+1)`. This sharpens the strict step `A_lt_A_succ` (`A(k) < A(k+1)`) using
evenness (`A_even`): two distinct even numbers differ by at least `2`. Consistent with the table
(`A(2)=2 → A(3)=6` jumps by `4`, `A(3)=6 → A(4)=8` by `2`), and gives the clean linear consequence
`A(k) ≥ 2(k-1)` a second, purely order-theoretic derivation. -/
theorem A_succ_ge_add_two {k : ℕ} (hk : 1 ≤ k) : A k + 2 ≤ A (k + 1) := by
  have hlt := A_lt_A_succ hk
  obtain ⟨s, hs⟩ := A_even k
  obtain ⟨t, ht⟩ := A_even (k + 1)
  omega

/-- **Trivial lower bound.** `A(k) ≥ k - 1`, since any `k` distinct naturals have maximum
at least `k - 1`. -/
theorem sub_one_le_A (k : ℕ) : k - 1 ≤ A k := by
  obtain ⟨a, hcard, _, hsup⟩ := A_mem k
  have := card_le_sup_succ a
  rw [hcard, hsup] at this
  omega

/-- **Sharpened lower bound (parity).** Any admissible `k`-set has largest element
`a.sup id ≥ 2(k-1)`: its diameter is `≥ 2(k-1)` (`admissible_diam_ge`) and its least element
is `≥ 0`, so the maximum (which is `≤ a.sup id`) is at least `2(k-1)`. -/
theorem admissible_two_mul_card_sub_one_le_sup {a : Finset ℕ} (ha : Admissible a) :
    2 * (a.card - 1) ≤ a.sup id := by
  rcases a.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hdiam := admissible_diam_ge ha hne
    have hmax_le_sup : a.max' hne ≤ a.sup id := Finset.le_sup (f := id) (a.max'_mem hne)
    omega

/-- **Sharpened lower bound on `A(k)`: `A(k) ≥ 2(k-1)`,** twice the trivial packing bound
`sub_one_le_A`. The prime `2` forces every admissible set to be single-parity, so its `k`
distinct elements span at least `2(k-1)`. This is sharp at `k = 2` (`A 2 = 2`) and is the
leading prime-`2` contribution toward the conjectured `A(k) ∼ k log k`. -/
theorem two_mul_sub_one_le_A (k : ℕ) : 2 * (k - 1) ≤ A k := by
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem k
  have h := admissible_two_mul_card_sub_one_le_sup ha
  rw [hcard, hsup] at h
  exact h

/-- `A(0) = 0` (the only admissible `0`-set is `∅`). -/
theorem A_zero : A 0 = 0 :=
  Nat.le_zero.mp (by simpa using A_le (a := (∅ : Finset ℕ)) Finset.card_empty admissible_empty)

/-- `A(1) = 0` (the singleton `{0}` is admissible with maximum `0`). -/
theorem A_one : A 1 = 0 := by
  refine Nat.le_zero.mp ?_
  simpa using A_le (a := ({0} : Finset ℕ)) (by simp) (admissible_singleton 0)

/-- **`A(2) = 2`.** The upper bound comes from the admissible set `{0, 2}`. The lower
bound `A(2) ≥ 2` is where admissibility first bites: the only `2`-set with maximum `1` is
`{0, 1}`, which is *not* admissible, so the minimal maximum jumps from the packing value
`k - 1 = 1` to `2`. -/
theorem A_two : A 2 = 2 := by
  apply le_antisymm
  · have h := A_le (k := 2) (a := ({0, 2} : Finset ℕ)) (by decide) admissible_zero_two
    have hs : ({0, 2} : Finset ℕ).sup id = 2 := by decide
    rwa [hs] at h
  · by_contra hlt
    push_neg at hlt
    have hlb := sub_one_le_A 2
    have hA1 : A 2 = 1 := by omega
    obtain ⟨a, hcard, ha, hsup⟩ := A_mem 2
    have hsub : a ⊆ ({0, 1} : Finset ℕ) := by
      intro x hx
      have hle : x ≤ a.sup id := Finset.le_sup (f := id) hx
      rw [hsup, hA1] at hle
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have heq : a = ({0, 1} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
    rw [heq] at ha
    exact not_admissible_zero_one ha

/- ## The exact value `A(3) = 6`

The next value after `A(2) = 2` is `A(3) = 6`. This is the first place where the
gap between `A(k)` and the trivial packing bound `k - 1` opens up appreciably
(`6` versus `2`), and `6` is exactly the Hardy–Littlewood minimal diameter
`H(3)` of an admissible `3`-tuple.

*Upper bound* `A(3) ≤ 6`: the set `{0, 2, 6}` is admissible (mod `2` all even, so
the odd class is missed; mod `3` the residues are `{0, 2, 0}`, so class `1` is
missed) and has largest element `6`.

*Lower bound* `A(3) ≥ 6`: any admissible `3`-set with largest element `≤ 5` lies
in `{0, …, 5}`. Modulo `2` it must miss a class, hence all three elements share a
parity, forcing the set to be `{0, 2, 4}` or `{1, 3, 5}`. But each of those covers
**all** residue classes modulo `3` (`{0,2,4} ≡ {0,2,1}`, `{1,3,5} ≡ {1,0,2}`), so
neither is admissible — a contradiction. Hence no admissible `3`-set fits below `6`. -/

/-- `{0, 2, 6}` is admissible: even mod `2` (misses the odd class) and `≡ {0,2,0}`
mod `3` (misses class `1`); larger primes are automatic by the size bound. -/
theorem admissible_zero_two_six : Admissible ({0, 2, 6} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 2, 6} : Finset ℕ).card = 3 := by decide
  rw [hc] at hcard
  interval_cases p
  · exact absurd hp (by decide)   -- p = 0
  · exact absurd hp (by decide)   -- p = 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 2: miss class 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 3: miss class 1

/-- `{0, 2, 4}` is **not** admissible: modulo `3` the residues `{0, 2, 1}` cover all
three classes, so no class is missed. -/
theorem not_admissible_zero_two_four : ¬ Admissible ({0, 2, 4} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr⟩ := h 3 (by decide)
  fin_cases r
  · exact hr 0 (by decide) (by decide)   -- class 0 occupied by 0
  · exact hr 4 (by decide) (by decide)   -- class 1 occupied by 4
  · exact hr 2 (by decide) (by decide)   -- class 2 occupied by 2

/-- `{1, 3, 5}` is **not** admissible: modulo `3` the residues `{1, 0, 2}` cover all
three classes, so no class is missed. -/
theorem not_admissible_one_three_five : ¬ Admissible ({1, 3, 5} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr⟩ := h 3 (by decide)
  fin_cases r
  · exact hr 3 (by decide) (by decide)   -- class 0 occupied by 3
  · exact hr 1 (by decide) (by decide)   -- class 1 occupied by 1
  · exact hr 5 (by decide) (by decide)   -- class 2 occupied by 5

/-- **Lower-bound core.** Every admissible `3`-set has largest element at least `6`.
If the maximum were `≤ 5`, the set would sit in `{0, …, 5}`; missing a class mod `2`
forces a single parity, pinning the set to `{0,2,4}` or `{1,3,5}`, both inadmissible
mod `3`. -/
theorem admissible_three_sup_ge {a : Finset ℕ} (hcard : a.card = 3)
    (ha : Admissible a) : 6 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  -- every element is ≤ 5
  have hbound : ∀ x ∈ a, x ≤ 5 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  -- in ZMod 2 every value is 0 or 1
  have hy : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  -- 2 ∣ x ↔ (x : ZMod 2) = 0
  have hdvd : ∀ x : ℕ, (x : ZMod 2) = 0 ↔ 2 ∣ x := fun x =>
    ZMod.natCast_eq_zero_iff x 2
  -- mod 2 the set misses a class, so all elements share a parity
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  fin_cases r2
  · -- misses class 0 ⇒ all elements odd ⇒ a = {1,3,5}
    have hsub : a ⊆ ({1, 3, 5} : Finset ℕ) := by
      intro x hx
      have hx5 := hbound x hx
      have hne : (x : ZMod 2) ≠ 0 := hr2 x hx
      have hodd : ¬ 2 ∣ x := fun hd => hne ((hdvd x).mpr hd)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have : a = ({1, 3, 5} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
    rw [this] at ha
    exact not_admissible_one_three_five ha
  · -- misses class 1 ⇒ all elements even ⇒ a = {0,2,4}
    have hsub : a ⊆ ({0, 2, 4} : Finset ℕ) := by
      intro x hx
      have hx5 := hbound x hx
      have hne : (x : ZMod 2) ≠ 1 := hr2 x hx
      have heven : 2 ∣ x := by
        rcases hy (x : ZMod 2) with h0 | h1
        · exact (hdvd x).mp h0
        · exact absurd h1 hne
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have : a = ({0, 2, 4} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
    rw [this] at ha
    exact not_admissible_zero_two_four ha

/-- **`A(3) = 6`.** The minimal largest element of an admissible `3`-set is `6`,
attained by `{0, 2, 6}` (equivalently `{0, 4, 6}`). This matches the
Hardy–Littlewood minimal diameter `H(3) = 6`. -/
theorem A_three : A 3 = 6 := by
  apply le_antisymm
  · -- upper bound from the witness {0,2,6}
    have h := A_le (k := 3) (a := ({0, 2, 6} : Finset ℕ)) (by decide)
      admissible_zero_two_six
    have hs : ({0, 2, 6} : Finset ℕ).sup id = 6 := by decide
    rwa [hs] at h
  · -- lower bound: the attained minimizer also has sup ≥ 6
    obtain ⟨a, hcard, ha, hsup⟩ := A_mem 3
    have hge := admissible_three_sup_ge hcard ha
    omega

/- ## Open Problems

The asymptotic behaviour of the extremal quantities is OPEN:

- **A(k)** = min a_k over admissible k-element sequences `0 ≤ a₁ < ⋯ < a_k`.
  Is A(k) ∼ k log k? (The prime k-tuples heuristic suggests the minimal
  diameter of an admissible k-tuple is ∼ k log k.)
- **B(k)** = min (a₁ + ⋯ + a_k)/k over admissible k-element sequences.
  Estimate B(k).

These require analytic number theory (sieve methods, distribution of primes in
residue classes) and are not formalized here.
-/

/- ## An explicit upper bound on `A(k)`

The `admissible_diam_ge` / `two_mul_sub_one_le_A` results bound `A(k)` from
*below*.  The dual weak *upper* bound comes from the explicit primorial-spacing
construction `{0, N, 2N, …, (k-1)N}` (with `N` the product of the primes `≤ k`)
already used in `exists_admissible_card`: its largest element is `(k-1)·N`, so
`A(k) ≤ (k-1)·N`.  This is far from the conjectured truth `A(k) ∼ k log k`
(`N` grows like `e^{(1+o(1))k}`), but it is the elementary two-sided companion of
the lower bounds, and pins `A(k)` between `2(k-1)` and `(k-1)·∏_{p ≤ k} p`. -/

/-- The **primorial-type product** `∏_{p ≤ k, p prime} p`, the spacing used by the
explicit admissible construction. Divisible by every prime `p ≤ k`. -/
def primorialUpTo (k : ℕ) : ℕ :=
  ((Finset.range (k + 1)).filter Nat.Prime).prod id

/-- **Explicit weak upper bound `A(k) ≤ (k-1)·∏_{p ≤ k} p`.**  The arithmetic
progression `{0, N, 2N, …, (k-1)N}` with `N = primorialUpTo k` is admissible
(every element is `≡ 0` modulo each prime `p ≤ k`, so the class `1` is missed;
larger primes are automatic), has `k` elements, and largest element `(k-1)·N`.
Feeding it to `A_le` gives the bound.  Together with `two_mul_sub_one_le_A` this
sandwiches `A(k)` between `2(k-1)` and `(k-1)·primorialUpTo k`. -/
theorem A_le_primorial (k : ℕ) : A k ≤ (k - 1) * primorialUpTo k := by
  classical
  set N := primorialUpTo k with hN
  have hNpos : 0 < N := by
    rw [hN, primorialUpTo]
    exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.pos)
  have hNdvd : ∀ p, p.Prime → p ≤ k → p ∣ N := by
    intro p hp hpk
    rw [hN, primorialUpTo]
    exact Finset.dvd_prod_of_mem id
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
  have hinj : Function.Injective (fun x : ℕ => x * N) :=
    fun x y h => Nat.eq_of_mul_eq_mul_right hNpos h
  set a := (Finset.range k).image (fun x => x * N) with ha_def
  have hcard : a.card = k := by
    rw [ha_def, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hadm : Admissible a := by
    rw [admissible_iff_card, hcard]
    intro p hp hpk
    haveI : Fact p.Prime := ⟨hp⟩
    have hp0 : (N : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p N).mpr (hNdvd p hp hpk)
    refine ⟨1, fun x hx => ?_⟩
    rw [ha_def] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    push_cast
    rw [hp0, mul_zero]
    exact zero_ne_one
  have hsup : a.sup id ≤ (k - 1) * N := by
    rw [ha_def]
    apply Finset.sup_le
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_range] at hi
    simp only [id_eq]
    exact mul_le_mul_right' (by omega) N
  exact le_trans (A_le hcard hadm) hsup

/- ## The two-sided sandwich and the divergence of `A(k)`

The lower bound `two_mul_sub_one_le_A` and the upper bound `A_le_primorial`
promised (in prose) to *sandwich* `A(k)`; we record that sandwich as a single
statement, and read off its qualitative consequence: `A(k) → ∞`.  While the
sharp rate `A(k) ∼ k log k` is open, the fact that the extremal quantity is
*unbounded* is already forced by the prime-`2` lower bound alone. -/

/-- **Two-sided sandwich for `A(k)`.**  Packaging the prime-`2` lower bound
`two_mul_sub_one_le_A` with the primorial upper bound `A_le_primorial`:
`2(k-1) ≤ A(k) ≤ (k-1)·∏_{p ≤ k} p`.  This is the explicit bracket promised in
the file header; the conjectured truth `A(k) ∼ k log k` lies strictly inside
it. -/
theorem A_sandwich (k : ℕ) :
    2 * (k - 1) ≤ A k ∧ A k ≤ (k - 1) * primorialUpTo k :=
  ⟨two_mul_sub_one_le_A k, A_le_primorial k⟩

/-- **`A(k)` diverges.**  The minimal-largest-element function tends to infinity:
`A(k) → ∞` as `k → ∞`.  This is immediate from the trivial packing bound
`k - 1 ≤ A(k)` (`sub_one_le_A`), and is the unconditional qualitative core of
the growth-rate question of Problem #1204 — no admissible `k`-tuple can be kept
in a bounded window once `k` is large. -/
theorem A_tendsto_atTop : Filter.Tendsto A Filter.atTop Filter.atTop := by
  have hsub : Filter.Tendsto (fun k : ℕ => k - 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    exact fun b => ⟨b + 1, fun k hk => by omega⟩
  exact Filter.tendsto_atTop_mono (f := fun k : ℕ => k - 1) sub_one_le_A hsub

end Erdos1204
