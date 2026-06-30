import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Proofs.InclusionExclusionSieve

/-
# Derangements as an Instance of the Inclusion–Exclusion Sieve

## What This Proves
This file answers the first open question of `InclusionExclusionSieve` ("The Sieve (Dual)
Form of Inclusion–Exclusion"):

> Instantiate the sieve to derive the derangement count
> `D_n = n! · Σ_k (-1)^k / k!` directly as "permutations avoiding every fixed-point set".

A **derangement** of `Fin n` is a permutation with no fixed point. We realise the set of
derangements as the "avoid" set of the sieve, taking the universe to be `Equiv.Perm (Fin n)`
and the bad property `i` to be "the permutation fixes the point `i`". The sieve
`InclusionExclusionSieve.card_avoid_sieve` then yields the **closed sieve form**

    D_n  =  Σ_{k=0}^n (-1)^k · C(n,k) · (n-k)!,

and, dividing each binomial term, the classical exponential form

    D_n  =  n! · Σ_{k=0}^n (-1)^k / k!.

## Why This Is Not Already in the Gallery / Mathlib
Mathlib's `numDerangements_sum` and the gallery file `DerangementsOQ03` both prove closed
forms for `D_n`, but **via the recurrence** `D_{n+2} = (n+1)(D_n + D_{n+1})` and induction.
The derivation here is conceptually different: it is the *textbook inclusion–exclusion*
argument, obtained as a genuine instance of the general dual sieve proved in the parent file.
The binomial sieve form `Σ_k (-1)^k C(n,k)(n-k)!` is, to our knowledge, not stated elsewhere
in the gallery (which records the `ascFactorial` form and the `n!·Σ 1/k!` form).

## Crux
The one piece of real counting is:

    #{ σ ∈ Perm (Fin n) : σ fixes every point of `t` }  =  (n - |t|)!,

proved by the Mathlib equivalence `Equiv.Perm.subtypeEquivSubtypePerm`, which identifies
permutations fixing the complement of a subtype with permutations of that subtype.

## Status
- [x] Complete proof, no `sorry`, no `axiom`
- [x] No `native_decide`; the worked example uses `decide`, so the file is axiom-free.

## Mathlib / Gallery Dependencies
- `InclusionExclusionSieve.card_avoid_sieve` : the general dual sieve (parent file)
- `Equiv.Perm.subtypeEquivSubtypePerm` : perms fixing the complement ≃ perms of the subtype
- `card_derangements_eq_numDerangements`, `Fintype.card_perm`, `Finset.powerset_card_disjiUnion`
-/

namespace InclusionExclusionSieveDerangements

open Equiv Finset

variable {n : ℕ}

/-- The set of permutations of `Fin n` that fix the point `i`. This is the `i`-th "bad
property" whose avoidance defines a derangement. -/
def fixSet (i : Fin n) : Finset (Perm (Fin n)) :=
  univ.filter (fun σ => σ i = i)

@[simp] theorem mem_fixSet (i : Fin n) (σ : Perm (Fin n)) : σ ∈ fixSet i ↔ σ i = i := by
  simp [fixSet]

/-
## Part I: The crux count — permutations fixing a prescribed set pointwise

The intersection `t.inf fixSet` is the set of permutations fixing every point of `t`. We
first identify it as a filter, then count it via `subtypeEquivSubtypePerm`.
-/

/-- The intersection of the fixed-point sets over `t` is exactly the permutations fixing
every point of `t`. -/
theorem inf_fixSet_eq_filter (t : Finset (Fin n)) :
    t.inf fixSet = univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ t, σ i = i) := by
  ext σ
  simp [fixSet, Finset.mem_inf]

/-- **Crux count.** The number of permutations of `Fin n` fixing every point of a finite set
`t` equals `(n - |t|)!` — the number of ways to permute the remaining `n - |t|` points.

Proved by the Mathlib equivalence `Equiv.Perm.subtypeEquivSubtypePerm`, which identifies the
permutations fixing the complement of `{x // x ∉ t}` with permutations of that subtype. -/
theorem card_fixesOn (t : Finset (Fin n)) :
    (univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ t, σ i = i)).card = (n - t.card).factorial := by
  -- predicate-level equivalence:  (∀ a, ¬(a ∉ t) → σ a = a)  ↔  (∀ i ∈ t, σ i = i)
  have hpred : ∀ σ : Perm (Fin n),
      (∀ a, ¬(a ∉ t) → σ a = a) ↔ (∀ i ∈ t, σ i = i) := by
    intro σ
    constructor
    · intro h i hi; exact h i (by simpa using hi)
    · intro h a ha; exact h a (by simpa using ha)
  -- card of the subtype of permutations fixing `t` pointwise
  have key : Fintype.card {σ : Perm (Fin n) // ∀ i ∈ t, σ i = i} = (n - t.card).factorial := by
    have e :
        Perm {x : Fin n // x ∉ t} ≃ {σ : Perm (Fin n) // ∀ i ∈ t, σ i = i} :=
      (Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin n => x ∉ t)).trans
        (Equiv.subtypeEquivRight hpred)
    have hcompl : Fintype.card {x : Fin n // x ∉ t} = n - t.card := by
      have h := Fintype.card_subtype_compl (p := fun x : Fin n => x ∈ t)
      simp only [Fintype.card_fin, Fintype.card_coe] at h
      exact h
    calc Fintype.card {σ : Perm (Fin n) // ∀ i ∈ t, σ i = i}
        = Fintype.card (Perm {x : Fin n // x ∉ t}) := (Fintype.card_congr e).symm
      _ = (Fintype.card {x : Fin n // x ∉ t}).factorial := Fintype.card_perm
      _ = (n - t.card).factorial := by rw [hcompl]
  rw [← key, Fintype.card_subtype]

/-
## Part II: The avoid set is the set of derangements
-/

/-- The "avoid" set of the sieve — permutations lying in *none* of the `fixSet i` — is the set
of derangements, so it has cardinality `numDerangements n`. -/
theorem card_avoid_eq_numDerangements :
    (univ.inf (fun i : Fin n => (fixSet i)ᶜ)).card = numDerangements n := by
  have h1 : univ.inf (fun i : Fin n => (fixSet i)ᶜ)
      = univ.filter (fun σ : Perm (Fin n) => ∀ i, σ i ≠ i) := by
    ext σ; simp [fixSet, Finset.mem_inf]
  rw [h1, ← Fintype.card_subtype (fun σ : Perm (Fin n) => ∀ i, σ i ≠ i)]
  have hd : Fintype.card (derangements (Fin n)) = numDerangements n := by
    rw [card_derangements_eq_numDerangements, Fintype.card_fin]
  rw [← hd]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))

/-
## Part III: The closed sieve form of the derangement count

Applying `card_avoid_sieve` and grouping the powerset sum by cardinality `k` (there are
`C(n,k)` subsets of size `k`, each contributing `(-1)^k (n-k)!`) gives the binomial form.
-/

/-- **The sieve form of the derangement count.** Derived directly from the general
inclusion–exclusion sieve `InclusionExclusionSieve.card_avoid_sieve`:

    D_n = Σ_{k=0}^n (-1)^k · C(n,k) · (n-k)!.

This is the textbook inclusion–exclusion derivation, independent of the recurrence-based
proof of `numDerangements_sum`. -/
theorem numDerangements_eq_sieve_sum (n : ℕ) :
    (numDerangements n : ℤ) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k).factorial : ℤ) := by
  have hsieve := InclusionExclusionSieve.card_avoid_sieve (univ : Finset (Fin n)) fixSet
  rw [card_avoid_eq_numDerangements] at hsieve
  rw [hsieve, Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  -- now: Σ_{k ∈ range (univ.card + 1)} Σ_{t ∈ univ.powersetCard k} (-1)^|t| |⋂ fixSet| = RHS
  rw [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro k _hk
  have hconst : ∀ t ∈ (univ : Finset (Fin n)).powersetCard k,
      (-1 : ℤ) ^ t.card * ((t.inf fixSet).card : ℤ)
        = (-1 : ℤ) ^ k * ((n - k).factorial : ℤ) := by
    intro t ht
    have htk : t.card = k := (Finset.mem_powersetCard.mp ht).2
    rw [inf_fixSet_eq_filter, card_fixesOn, htk]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-
## Part IV: The exponential form, recovered from the sieve

Each binomial term factors as `C(n,k)(n-k)! = n!/k!`, so the sieve sum collapses to the
classical `n! · Σ (-1)^k / k!`. We derive this here from the sieve form above (not from the
recurrence), literally answering the open question.
-/

/-- **The exponential closed form, derived from the sieve.**

    D_n = n! · Σ_{k=0}^n (-1)^k / k!.

Obtained from `numDerangements_eq_sieve_sum` by the identity `C(n,k)(n-k)! = n!/k!`. -/
theorem numDerangements_eq_factorial_mul_altSum (n : ℕ) :
    (numDerangements n : ℝ)
      = (n.factorial : ℝ) * ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k / (k.factorial : ℝ) := by
  have hz := numDerangements_eq_sieve_sum n
  have hr : (numDerangements n : ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * (n.choose k : ℝ) * ((n - k).factorial : ℝ) := by
    have h := congrArg (Int.cast : ℤ → ℝ) hz
    push_cast at h
    exact h
  rw [hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk0 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'
  have hfac : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ)
      = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hquot : (n.choose k : ℝ) * ((n - k).factorial : ℝ)
      = (n.factorial : ℝ) / (k.factorial : ℝ) := by
    rw [eq_div_iff hk0]; linear_combination hfac
  rw [mul_assoc, hquot]
  ring

/-
## Part V: Concrete check (axiom-free)

`D_4 = 9`, verified against the sieve sum `Σ_{k=0}^4 (-1)^k C(4,k)(4-k)!
= 24 - 24 + 12 - 4 + 1 = 9`, with `decide` (not `native_decide`).
-/

/-- The sieve form specialised to `n = 4`. -/
example : (numDerangements 4 : ℤ) =
    ∑ k ∈ Finset.range 5, (-1 : ℤ) ^ k * (Nat.choose 4 k : ℤ) * ((4 - k).factorial : ℤ) :=
  numDerangements_eq_sieve_sum 4

/-- The sieve sum evaluates to `9 = D_4`. -/
example :
    (∑ k ∈ Finset.range 5, (-1 : ℤ) ^ k * (Nat.choose 4 k : ℤ) * ((4 - k).factorial : ℤ)) = 9 := by
  decide

#check @numDerangements_eq_sieve_sum
#check @numDerangements_eq_factorial_mul_altSum
#check @card_fixesOn

end InclusionExclusionSieveDerangements
