/-
Erdős Problem #1023 (OQ-03): Single-layer constructions and an explicit
exponential lower bound for union-free families.

Parent: `Erdos1023Problem.lean` proves the union-free extremal function
satisfies `F(n) = C(n, ⌊n/2⌋)`, with the lower bound coming from the single
*middle* layer (`unionFreeMax_ge_middle`) and the matching upper bound routed
through Problem 447 (`problem_447_solution`, an external input).

This file isolates the part of the story that is fully self-contained and
**axiom-free**: the lower-bound construction. It makes three points.

  1. The middle layer is not special — *every* layer (the family of all
     `k`-element subsets, for any fixed `k`) is an antichain, hence union-free.
     So `F(n) ≥ C(n, k)` for every `k`, generalising the middle-layer bound.

  2. Summing the binomial row and bounding each term by the central one gives
     `2^n ≤ (n+1) · C(n, ⌊n/2⌋)`.

  3. Combining (1) and (2) yields an explicit, axiom-free exponential lower
     bound

        `2^n ≤ (n + 1) · F(n)`,      equivalently   `F(n) ≥ 2^n / (n + 1)`,

     proved purely from the single middle-layer construction and independent of
     the (harder) matching upper bound. This already certifies that `F(n)` grows
     exponentially — the crude pigeonhole `2^n / (n+1)` differs from the true
     `~ √(2/π) · 2^n / √n` only by the polynomial factor `√n / (n+1)`.

## Self-contained
To keep this contribution axiom-free and independent of the parent's asymptotic
section (which carries the 5 axioms routing the *upper* bound through Problem
447), the small amount of lower-bound infrastructure it needs — set families,
`isUnionFree`, `isAntichain`, `antichain_unionFree`, the extremal function
`unionFreeMax`, and the `layer` construction — is re-declared here verbatim from
the parent. Nothing below depends on any axiom: only `Classical.choice`,
`propext`, `Quot.sound` are used.

## Mathlib API used
- `Nat.choose_le_middle` (`Mathlib.Data.Nat.Choose.Basic`)
- `Nat.sum_range_choose` (`Mathlib.Data.Nat.Choose.Sum`)
- `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.card_range`
- `Nat.div_le_div_right`, `Nat.mul_div_cancel_left`

Tags: combinatorics, extremal-set-theory, union-free, antichain, sperner,
      binomial-coefficients, lower-bound
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Finset

namespace Erdos1023OQ03

/-!
## Lower-bound infrastructure (re-declared from the parent, axiom-free)
-/

/-- A set family is a collection of subsets of `Fin n`. -/
abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- The union of a subfamily. -/
def familyUnion (F : SetFamily n) : Finset (Fin n) :=
  F.sup id

/-- A set is a union of a subfamily (of size ≥ 2). -/
def isUnionOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card ≥ 2 ∧ A ∉ G ∧ familyUnion G = A

/-- A family is union-free: no member is the union of other members. -/
def isUnionFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isUnionOf A (F.erase A)

/-- A family is an antichain if no set contains another. -/
def isAntichain (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- Each element of a subfamily contributes to the union. -/
lemma mem_sub_familyUnion {F : SetFamily n} {B : Finset (Fin n)} (hB : B ∈ F) :
    B ⊆ familyUnion F := by
  intro x hx
  simp only [familyUnion]
  exact Finset.mem_sup.mpr ⟨B, hB, hx⟩

/-- Antichains are union-free. -/
theorem antichain_unionFree (F : SetFamily n) : isAntichain F → isUnionFree F := by
  intro hanti A hA ⟨G, hGsub, hGcard, hAnotG, hGunion⟩
  have hBsubA : ∀ B ∈ G, B ⊆ A := by
    intro B hB
    rw [← hGunion]
    exact mem_sub_familyUnion hB
  have hBeqA : ∀ B ∈ G, B = A := by
    intro B hB
    have hBF : B ∈ F := Finset.mem_of_mem_erase (hGsub hB)
    exact hanti B hBF A hA (hBsubA B hB)
  have : G.card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp h
    exact hBC (by rw [hBeqA B hB, hBeqA C hC])
  omega

/-- The set of achievable cardinalities is bounded above by `2^n`. -/
theorem unionFree_sizes_bddAbove (n : ℕ) :
    BddAbove { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k } :=
  ⟨2 ^ n, fun k ⟨F, _, hk⟩ => hk ▸ (Finset.card_le_univ F).trans (by simp)⟩

/-- `F(n)`: maximum size of a union-free family on `{0,…,n-1}`. -/
noncomputable def unionFreeMax (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k }

/-- The `k`-th layer: all `k`-element subsets of `Fin n`. -/
def layer (n k : ℕ) : SetFamily n :=
  (univ.powerset).filter (fun A => A.card = k)

/-- Size of a layer equals the binomial coefficient. -/
theorem layer_card (n k : ℕ) : (layer n k).card = Nat.choose n k := by
  simp [layer]

/-!
## OQ-03 results
-/

/-- **Every layer is an antichain.** The family of all `k`-element subsets of
`Fin n` contains no two distinct comparable sets: if `A ⊆ B` and both have
cardinality `k`, then `A = B`. This generalises the parent's
`middleLayer_antichain` (the `k = n/2` case). -/
theorem layer_antichain (n k : ℕ) : isAntichain (layer n k) := by
  intro A hA B hB hAB
  simp only [layer, mem_filter] at hA hB
  exact Finset.eq_of_subset_of_card_le hAB (hA.2 ▸ hB.2 ▸ le_refl _)

/-- **Every layer is union-free.** Immediate from `layer_antichain` and
`antichain_unionFree`. -/
theorem layer_unionFree (n k : ℕ) : isUnionFree (layer n k) :=
  antichain_unionFree _ (layer_antichain n k)

/-- **Lower bound at every layer.** Each binomial coefficient `C(n, k)` is
realised by a union-free family (the `k`-th layer), so `F(n) ≥ C(n, k)` for
*every* `k`. This strictly generalises the parent's middle-layer bound. -/
theorem unionFreeMax_ge_choose (n k : ℕ) :
    unionFreeMax n ≥ Nat.choose n k := by
  apply le_csSup (unionFree_sizes_bddAbove n)
  exact ⟨layer n k, layer_unionFree n k, layer_card n k⟩

/-- The middle-layer bound, recovered as the `k = n/2` instance of
`unionFreeMax_ge_choose`, confirming the generalisation subsumes it. -/
theorem unionFreeMax_ge_middle (n : ℕ) :
    unionFreeMax n ≥ Nat.choose n (n / 2) :=
  unionFreeMax_ge_choose n (n / 2)

/-- **Row sum bounded by the central term.** The binomial coefficients in row `n`
sum to `2^n`, and each is at most the central coefficient `C(n, ⌊n/2⌋)`, so
`2^n ≤ (n + 1) · C(n, ⌊n/2⌋)`. -/
theorem two_pow_le_succ_mul_central (n : ℕ) :
    2 ^ n ≤ (n + 1) * Nat.choose n (n / 2) := by
  calc 2 ^ n = ∑ k ∈ Finset.range (n + 1), Nat.choose n k := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _k ∈ Finset.range (n + 1), Nat.choose n (n / 2) :=
        Finset.sum_le_sum (fun k _ => Nat.choose_le_middle k n)
    _ = (n + 1) * Nat.choose n (n / 2) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Explicit exponential lower bound (axiom-free).** Purely from the single
middle-layer construction,

  `2^n ≤ (n + 1) · F(n)`.

In particular `F(n)` grows at least like `2^n / (n + 1)` — exponentially —
without invoking the matching (harder) upper bound. -/
theorem unionFreeMax_exponential_lower_bound (n : ℕ) :
    2 ^ n ≤ (n + 1) * unionFreeMax n := by
  refine (two_pow_le_succ_mul_central n).trans ?_
  gcongr
  exact unionFreeMax_ge_middle n

/-- Division form of the exponential lower bound: `2^n / (n + 1) ≤ F(n)`. -/
theorem unionFreeMax_ge_two_pow_div (n : ℕ) :
    2 ^ n / (n + 1) ≤ unionFreeMax n := by
  calc 2 ^ n / (n + 1)
      ≤ ((n + 1) * unionFreeMax n) / (n + 1) :=
        Nat.div_le_div_right (unionFreeMax_exponential_lower_bound n)
    _ = unionFreeMax n := Nat.mul_div_cancel_left _ (Nat.succ_pos n)

/-!
## Monotonicity of the extremal function

A new structural property absent from the parent and the lower-bound section
above: the extremal function `F(n) = unionFreeMax n` is **monotone**,
`n ≤ m → F(n) ≤ F(m)`.

The proof is by a *relabelling push-forward*. Any injection `e : Fin n ↪ Fin m`
lifts to a map on set families, `pushFamily e`, that relabels every member set
by `e`. This map

  * preserves cardinality (`pushFamily_card`), because relabelling along an
    embedding is injective; and
  * preserves union-freeness (`pushFamily_unionFree`), because taking images
    along an injection commutes with unions (`familyUnion_pushFamily`) and
    keeps distinct sets distinct, so a spurious union among the relabelled sets
    would pull back to a spurious union among the originals.

Hence every achievable family size on `Fin n` is also achievable on `Fin m`,
the set of achievable sizes only grows, and the supremum `unionFreeMax` is
monotone (`unionFreeMax_mono`). Specialising to `m = n + 1` gives the successor
form `F(n) ≤ F(n+1)` (`unionFreeMax_le_succ`).
-/

/-- The empty family is (vacuously) union-free; it witnesses `0 ∈` the set of
achievable sizes, so that set is nonempty for every `n`. -/
theorem isUnionFree_empty : isUnionFree (∅ : SetFamily n) :=
  fun A hA => absurd hA (Finset.notMem_empty A)

/-- Membership characterisation of `familyUnion`: a point lies in the union of a
family iff it lies in some member. -/
lemma mem_familyUnion {n : ℕ} {F : SetFamily n} {x : Fin n} :
    x ∈ familyUnion F ↔ ∃ A ∈ F, x ∈ A := by
  simp [familyUnion, Finset.mem_sup]

/-- **Relabelling push-forward.** Transport a set family on `Fin n` to one on
`Fin m` along an embedding `e : Fin n ↪ Fin m`, relabelling every member set by
`e`. -/
def pushFamily {n m : ℕ} (e : Fin n ↪ Fin m) (F : SetFamily n) : SetFamily m :=
  F.map ⟨Finset.map e, Finset.map_injective e⟩

/-- Membership in the push-forward: `B` is a relabelled member iff it is the
image `A.map e` of some `A ∈ F`. -/
@[simp] lemma mem_pushFamily {n m : ℕ} {e : Fin n ↪ Fin m} {F : SetFamily n}
    {B : Finset (Fin m)} : B ∈ pushFamily e F ↔ ∃ A ∈ F, A.map e = B := by
  simp [pushFamily, Finset.mem_map, Function.Embedding.coeFn_mk]

/-- **Relabelling preserves family size.** Since `e` is injective, the induced
relabelling of member sets is injective, so the push-forward has the same
cardinality as the original family. -/
@[simp] lemma pushFamily_card {n m : ℕ} (e : Fin n ↪ Fin m) (F : SetFamily n) :
    (pushFamily e F).card = F.card := by
  unfold pushFamily; exact Finset.card_map _

/-- **Relabelling commutes with taking unions.** The union of a relabelled
family is the relabelling of its union: `⋃ e[G] = e[⋃ G]`. This is the key
compatibility making union-freeness stable under push-forward. -/
lemma familyUnion_pushFamily {n m : ℕ} (e : Fin n ↪ Fin m) (G : SetFamily n) :
    familyUnion (pushFamily e G) = (familyUnion G).map e := by
  ext y
  simp only [mem_familyUnion, mem_pushFamily, Finset.mem_map]
  constructor
  · rintro ⟨B, ⟨A, hA, rfl⟩, hyB⟩
    rw [Finset.mem_map] at hyB
    obtain ⟨a, ha, rfl⟩ := hyB
    exact ⟨a, ⟨A, hA, ha⟩, rfl⟩
  · rintro ⟨a, ⟨A, hA, ha⟩, rfl⟩
    exact ⟨A.map e, ⟨A, hA, rfl⟩, Finset.mem_map.mpr ⟨a, ha, rfl⟩⟩

/-- **Relabelling preserves union-freeness.** If `F` is union-free on `Fin n`
and `e : Fin n ↪ Fin m` is an embedding, then the relabelled family
`pushFamily e F` is union-free on `Fin m`. A spurious union `e[A₀] = ⋃ 𝒢` among
the relabelled sets pulls back (the originals of `𝒢` form a subfamily `𝒢₀ ⊆ F`
with `pushFamily e 𝒢₀ = 𝒢`) to a spurious union `A₀ = ⋃ 𝒢₀` in `F`, because
relabelling is injective and commutes with unions. -/
theorem pushFamily_unionFree {n m : ℕ} (e : Fin n ↪ Fin m) (F : SetFamily n)
    (hF : isUnionFree F) : isUnionFree (pushFamily e F) := by
  intro B hB hUnion
  rw [mem_pushFamily] at hB
  obtain ⟨A₀, hA₀, rfl⟩ := hB
  obtain ⟨G, hGsub, hGcard, hBnotG, hGunion⟩ := hUnion
  set G₀ : SetFamily n := F.filter (fun A => A.map e ∈ G) with hG₀def
  have hGeq : G = pushFamily e G₀ := by
    apply Finset.ext
    intro C
    rw [mem_pushFamily]
    constructor
    · intro hCG
      have hCH : C ∈ pushFamily e F := Finset.mem_of_mem_erase (hGsub hCG)
      rw [mem_pushFamily] at hCH
      obtain ⟨A, hA, rfl⟩ := hCH
      refine ⟨A, ?_, rfl⟩
      rw [hG₀def, Finset.mem_filter]
      exact ⟨hA, hCG⟩
    · rintro ⟨A, hA, rfl⟩
      rw [hG₀def, Finset.mem_filter] at hA
      exact hA.2
  refine hF A₀ hA₀ ⟨G₀, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rw [hG₀def, Finset.mem_filter] at hA
    rw [Finset.mem_erase]
    refine ⟨?_, hA.1⟩
    intro hAeq
    apply hBnotG
    rw [← hAeq]
    exact hA.2
  · have hcard : G₀.card = G.card := by rw [hGeq, pushFamily_card]
    rw [hcard]; exact hGcard
  · intro hA₀G₀
    rw [hG₀def, Finset.mem_filter] at hA₀G₀
    exact hBnotG hA₀G₀.2
  · have h1 : familyUnion (pushFamily e G₀) = (familyUnion G₀).map e :=
      familyUnion_pushFamily e G₀
    rw [← hGeq, hGunion] at h1
    exact (Finset.map_injective e h1).symm

/-- **Monotonicity of the extremal function.** For `n ≤ m`, every union-free
family on `Fin n` relabels to a union-free family of the same size on `Fin m`
(via `Fin.castLEEmb`), so the set of achievable sizes can only grow and
`F(n) ≤ F(m)`. -/
theorem unionFreeMax_mono {n m : ℕ} (h : n ≤ m) :
    unionFreeMax n ≤ unionFreeMax m := by
  have hne : { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k }.Nonempty :=
    ⟨0, ∅, isUnionFree_empty, Finset.card_empty⟩
  apply csSup_le_csSup (unionFree_sizes_bddAbove m) hne
  rintro k ⟨F, hF, rfl⟩
  exact ⟨pushFamily (Fin.castLEEmb h) F, pushFamily_unionFree _ F hF,
    pushFamily_card _ F⟩

/-- `unionFreeMax` packaged as a `Monotone` function. -/
theorem unionFreeMax_monotone : Monotone unionFreeMax :=
  fun _ _ h => unionFreeMax_mono h

/-- **Successor form of monotonicity:** `F(n) ≤ F(n+1)`. Adding one more ground
element never decreases the maximum union-free family size. -/
theorem unionFreeMax_le_succ (n : ℕ) : unionFreeMax n ≤ unionFreeMax (n + 1) :=
  unionFreeMax_mono (Nat.le_succ n)

/-!
## Strict monotonicity via a fresh ground element

The successor bound `F(n) ≤ F(n+1)` above can be sharpened to *strict*
monotonicity `F(n) + 1 ≤ F(n+1)`: the extra ground element `n` always lets us
enlarge an extremal family by exactly one. Take an extremal union-free family
`G` on `Fin n`, relabel it into `Fin (n+1)` (so no member then contains the new
top element `Fin.last n`), and adjoin the singleton `{Fin.last n}`. That new
element is *fresh* — it lies in no relabelled member — so the enlarged family is
still union-free (`unionFree_insert_fresh`) and strictly larger, giving
`F(n) + 1 ≤ F(n+1)` (`unionFreeMax_succ_strict`). Hence `F` is *strictly*
increasing (`unionFreeMax_strictMono`), a sharpening of `unionFreeMax_monotone`.
-/

/-- **Adjoining a set with a fresh element preserves union-freeness.** If `F` is
union-free and `A` contains a ground element `x` lying in no member of `F`, then
`insert A F` is union-free. The fresh element `x` blocks every potential
spurious union: a union of `≥ 2` members equal to `A` would have to omit `x`
(no member of `F` contains it), and a union producing some `B ∈ F` cannot use
`A` (that would force `x ∈ B`), so it reduces to a spurious union already inside
`F`. -/
theorem unionFree_insert_fresh {n : ℕ} {F : SetFamily n} {A : Finset (Fin n)}
    (hF : isUnionFree F) {x : Fin n} (hxA : x ∈ A) (hxF : ∀ B ∈ F, x ∉ B) :
    isUnionFree (insert A F) := by
  -- `x` lies in no union of a subfamily of `F`
  have hxUnion : ∀ {G : SetFamily n}, G ⊆ F → x ∉ familyUnion G := by
    intro G hG hx
    rw [mem_familyUnion] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    exact hxF C (hG hC) hxC
  intro B hB ⟨G, hGsub, hGcard, hBnotG, hGunion⟩
  rcases Finset.mem_insert.mp hB with rfl | hBF
  · -- `B = A`: the union `G` lives in `F`, so it misses `x ∈ A`
    have hGF : G ⊆ F := by
      intro C hC
      have hmem := hGsub hC
      rw [Finset.mem_erase, Finset.mem_insert] at hmem
      rcases hmem.2 with rfl | h
      · exact absurd rfl hmem.1
      · exact h
    apply hxUnion hGF
    rw [hGunion]; exact hxA
  · -- `B ∈ F`: `A ∉ G` (else `x ∈ B`), so `G ⊆ F.erase B` is a spurious union in `F`
    have hAnotG : A ∉ G := by
      intro hAG
      exact hxF B hBF (hGunion ▸ mem_sub_familyUnion hAG hxA)
    have hGsub' : G ⊆ F.erase B := by
      intro C hC
      have hmem := hGsub hC
      rw [Finset.mem_erase, Finset.mem_insert] at hmem
      rw [Finset.mem_erase]
      refine ⟨hmem.1, ?_⟩
      rcases hmem.2 with rfl | h
      · exact absurd hC hAnotG
      · exact h
    exact hF B hBF ⟨G, hGsub', hGcard, hBnotG, hGunion⟩

/-- **Strict monotonicity:** `F(n) + 1 ≤ F(n+1)`. The fresh ground element `n`
strictly increases the maximum union-free family size: relabel an extremal
family into `Fin (n+1)` and adjoin the singleton `{Fin.last n}` of the new top
element, which lies in no relabelled member. -/
theorem unionFreeMax_succ_strict (n : ℕ) :
    unionFreeMax n + 1 ≤ unionFreeMax (n + 1) := by
  -- an extremal family `G` of size `F(n)` exists: the `sSup` of a nonempty
  -- subset of `ℕ` bounded above is attained
  have hne : { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k }.Nonempty :=
    ⟨0, ∅, isUnionFree_empty, Finset.card_empty⟩
  obtain ⟨G, hG, hGcard⟩ :
      ∃ G : SetFamily n, isUnionFree G ∧ G.card = unionFreeMax n :=
    Nat.sSup_mem hne (unionFree_sizes_bddAbove n)
  -- relabel into `Fin (n+1)` along `castLE`, then adjoin `{Fin.last n}`
  set e : Fin n ↪ Fin (n + 1) := Fin.castLEEmb (Nat.le_succ n) with he
  set A : Finset (Fin (n + 1)) := {Fin.last n} with hA
  have hxA : Fin.last n ∈ A := Finset.mem_singleton_self _
  -- the new element is fresh: no relabelled member contains `Fin.last n`
  have hfresh : ∀ B ∈ pushFamily e G, Fin.last n ∉ B := by
    intro B hB
    rw [mem_pushFamily] at hB
    obtain ⟨C, _, rfl⟩ := hB
    rw [Finset.mem_map]
    rintro ⟨a, _, ha⟩
    have h1 : ((e a : Fin (n + 1)) : ℕ) = (a : ℕ) := rfl
    have h2 : ((e a : Fin (n + 1)) : ℕ) = n := by rw [ha]; exact Fin.val_last n
    have h3 : (a : ℕ) < n := a.isLt
    omega
  -- the enlarged family is union-free and strictly larger
  have hUF : isUnionFree (insert A (pushFamily e G)) :=
    unionFree_insert_fresh (pushFamily_unionFree e G hG) hxA hfresh
  have hAnot : A ∉ pushFamily e G := fun h => hfresh A h hxA
  have hcard : (insert A (pushFamily e G)).card = unionFreeMax n + 1 := by
    rw [Finset.card_insert_of_notMem hAnot, pushFamily_card, hGcard]
  rw [← hcard]
  exact le_csSup (unionFree_sizes_bddAbove (n + 1))
    ⟨insert A (pushFamily e G), hUF, rfl⟩

/-- **`F` is strictly monotone.** Strengthens `unionFreeMax_monotone`: the
extremal union-free family size strictly increases with the number of ground
elements, `n < m → F(n) < F(m)`. -/
theorem unionFreeMax_strictMono : StrictMono unionFreeMax :=
  strictMono_nat_of_lt_succ unionFreeMax_succ_strict

#check @layer_antichain
#check @unionFreeMax_ge_choose
#check @unionFreeMax_exponential_lower_bound
#check @unionFreeMax_mono
#check @pushFamily_unionFree
#check @unionFreeMax_succ_strict
#check @unionFreeMax_strictMono

end Erdos1023OQ03
