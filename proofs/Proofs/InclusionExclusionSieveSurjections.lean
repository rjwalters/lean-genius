import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Proofs.InclusionExclusionSieve

/-
# Surjection Counts as an Instance of the Inclusion–Exclusion Sieve

## What This Proves
This file answers the first open question of `InclusionExclusionSieveDerangements`
("Derangements as an Instance of the Inclusion–Exclusion Sieve"):

> Instantiate the same sieve to derive the surjection count
> `#(surjections [n] ↠ [k]) = Σ_j (-1)^j C(k,j) (k-j)^n`,
> taking the bad property `j` to be "value `j` is missed" — the crux count being
> `|intersection over a j-set of missed values| = (k - |J|)^n`.

We realise the set of **surjections** `Fin n → Fin k` as the "avoid" set of the sieve,
taking the universe to be the function type `Fin n → Fin k` and the bad property `j`
(for `j : Fin k`) to be "the value `j` is missed", i.e. no input maps to `j`. A function
avoiding *every* bad property hits every value, so it is exactly a surjection. The general
dual sieve `InclusionExclusionSieve.card_avoid_sieve` then yields the **closed sieve form**

    #(surjections Fin n → Fin k)  =  Σ_{j=0}^k (-1)^j · C(k,j) · (k-j)^n.

## Why This Is Not Already in the Gallery / Mathlib
Mathlib does not record a closed form for the number of surjections between finite types,
and the gallery's only sieve instance so far is the derangement count
(`InclusionExclusionSieveDerangements`). This file adds the second classical application of
the dual sieve — the surjection / "onto function" count, equivalently `k! · S(n,k)` with
`S` the Stirling numbers of the second kind — obtained as a genuine instance of the reusable
theorem `card_avoid_sieve`, exactly parallel to the derangement derivation.

## Crux
The one piece of real counting is:

    #{ f : Fin n → Fin k : f misses every value in t }  =  (k - |t|)^n,

because such an `f` is exactly a function into the `(k - |t|)`-element set `Fin k \ t`, and
there are `(k - |t|)^n` functions from an `n`-element domain into a `(k - |t|)`-element
codomain. We prove this by the explicit equivalence with `Fin n → {x : Fin k // x ∉ t}`.

## Status
- [x] Complete proof, no `sorry`, no `axiom`
- [x] No `native_decide`; the worked example uses `decide`, so the file is axiom-free.

## Mathlib / Gallery Dependencies
- `InclusionExclusionSieve.card_avoid_sieve` : the general dual sieve (parent file)
- `Fintype.card_fun`, `Fintype.card_subtype_compl` : function- and subtype-cardinalities
- `Finset.powerset_card_disjiUnion`, `Finset.card_powersetCard` : grouping the powerset by size
-/

namespace InclusionExclusionSieveSurjections

open Finset

variable {k : ℕ}

/-- The set of functions `Fin n → Fin k` that *miss* the value `j` (no input maps to `j`).
This is the `j`-th "bad property" whose avoidance defines a surjection. -/
def missSet (n : ℕ) (j : Fin k) : Finset (Fin n → Fin k) :=
  univ.filter (fun f => ∀ i, f i ≠ j)

@[simp] theorem mem_missSet (n : ℕ) (j : Fin k) (f : Fin n → Fin k) :
    f ∈ missSet n j ↔ ∀ i, f i ≠ j := by simp [missSet]

/-
## Part I: The crux count — functions missing a prescribed set of values

The intersection `t.inf (missSet n)` is the set of functions missing every value in `t`.
We first identify it as a filter, then count it via the equivalence with functions into
the complementary subtype.
-/

/-- The intersection of the "miss" sets over `t` is exactly the functions whose every value
avoids `t`. -/
theorem inf_missSet_eq_filter (n : ℕ) (t : Finset (Fin k)) :
    t.inf (missSet n) = univ.filter (fun f : Fin n → Fin k => ∀ i, f i ∉ t) := by
  ext f
  simp only [Finset.mem_inf, mem_missSet, mem_filter, mem_univ, true_and]
  constructor
  · intro h i hi
    exact h (f i) hi i rfl
  · intro h j hj i hi
    exact h i (hi ▸ hj)

/-- **Crux count.** The number of functions `Fin n → Fin k` missing every value of a finite
set `t` equals `(k - |t|)^n` — there are `k - |t|` allowed output values for each of the `n`
inputs.

Proved by the explicit equivalence with `Fin n → {x : Fin k // x ∉ t}`. -/
theorem card_missesOn (n : ℕ) (t : Finset (Fin k)) :
    (univ.filter (fun f : Fin n → Fin k => ∀ i, f i ∉ t)).card = (k - t.card) ^ n := by
  -- equivalence: functions all of whose values avoid `t`  ≃  functions into `{x // x ∉ t}`
  have e : {f : Fin n → Fin k // ∀ i, f i ∉ t} ≃ (Fin n → {x : Fin k // x ∉ t}) :=
    { toFun := fun f i => ⟨f.1 i, f.2 i⟩
      invFun := fun g => ⟨fun i => (g i).1, fun i => (g i).2⟩
      left_inv := by rintro ⟨f, hf⟩; rfl
      right_inv := by intro g; funext i; rfl }
  -- the complementary subtype has `k - |t|` elements
  have hcompl : Fintype.card {x : Fin k // x ∉ t} = k - t.card := by
    have h := Fintype.card_subtype_compl (p := fun x : Fin k => x ∈ t)
    simp only [Fintype.card_fin, Fintype.card_coe] at h
    exact h
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, hcompl, Fintype.card_fin]

/-
## Part II: The avoid set is the set of surjections
-/

/-- The "avoid" set of the sieve — functions lying in *none* of the `missSet n j` — is the
set of surjections `Fin n → Fin k`: missing no value means hitting every value. -/
theorem avoid_eq_filter_surjective (n : ℕ) :
    (univ.inf (fun j : Fin k => (missSet n j)ᶜ))
      = univ.filter (fun f : Fin n → Fin k => Function.Surjective f) := by
  ext f
  simp only [Finset.mem_inf, mem_univ, mem_compl, mem_missSet, mem_filter, true_and,
    Function.Surjective]
  push_neg
  tauto

/-
## Part III: The closed sieve form of the surjection count

Applying `card_avoid_sieve` and grouping the powerset sum by cardinality `j` (there are
`C(k,j)` subsets of size `j`, each contributing `(-1)^j (k-j)^n`) gives the binomial form.
-/

/-- **The sieve form of the surjection count.** Derived directly from the general
inclusion–exclusion sieve `InclusionExclusionSieve.card_avoid_sieve`:

    #(surjections Fin n → Fin k)  =  Σ_{j=0}^k (-1)^j · C(k,j) · (k-j)^n.

This is the textbook inclusion–exclusion derivation of the surjection / onto-function count,
exactly parallel to the derangement instance in the sibling file. -/
theorem card_surjective_eq_sieve_sum (n k : ℕ) :
    ((univ.filter (fun f : Fin n → Fin k => Function.Surjective f)).card : ℤ) =
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℤ) ^ j * (k.choose j : ℤ) * (((k - j) ^ n : ℕ) : ℤ) := by
  have hsieve := InclusionExclusionSieve.card_avoid_sieve (univ : Finset (Fin k)) (missSet n)
  rw [avoid_eq_filter_surjective n] at hsieve
  rw [hsieve, Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  -- now: Σ_{j ∈ range (univ.card + 1)} Σ_{t ∈ univ.powersetCard j} (-1)^|t| |⋂ missSet| = RHS
  rw [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro j _hj
  have hconst : ∀ t ∈ (univ : Finset (Fin k)).powersetCard j,
      (-1 : ℤ) ^ t.card * ((t.inf (missSet n)).card : ℤ)
        = (-1 : ℤ) ^ j * (((k - j) ^ n : ℕ) : ℤ) := by
    intro t ht
    have htj : t.card = j := (Finset.mem_powersetCard.mp ht).2
    rw [inf_missSet_eq_filter, card_missesOn, htj]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-
## Part IV: Concrete check (axiom-free)

The number of surjections `[3] ↠ [2]` is `2^3 - 2 = 6`, verified against the sieve sum
`Σ_{j=0}^2 (-1)^j C(2,j)(2-j)^3 = 8 - 2 + 0 = 6`, with `decide` (not `native_decide`).
-/

/-- The sieve form specialised to `n = 3`, `k = 2`. -/
example :
    ((univ.filter (fun f : Fin 3 → Fin 2 => Function.Surjective f)).card : ℤ) =
      ∑ j ∈ Finset.range 3,
        (-1 : ℤ) ^ j * (Nat.choose 2 j : ℤ) * (((2 - j) ^ 3 : ℕ) : ℤ) :=
  card_surjective_eq_sieve_sum 3 2

/-- The sieve sum evaluates to `6`, the number of surjections `[3] ↠ [2]`. -/
example :
    (∑ j ∈ Finset.range 3,
      (-1 : ℤ) ^ j * (Nat.choose 2 j : ℤ) * (((2 - j) ^ 3 : ℕ) : ℤ)) = 6 := by
  decide

#check @card_surjective_eq_sieve_sum
#check @card_missesOn
#check @avoid_eq_filter_surjective

end InclusionExclusionSieveSurjections
