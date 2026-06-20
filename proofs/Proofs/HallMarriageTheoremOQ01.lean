import Mathlib

/-!
# Hall's marriage theorem: SDR existence, the deficiency obstruction, and witnesses

Let `ι` be an index set and `t : ι → Finset α` a family of finite "preference" sets.  A
**system of distinct representatives** (SDR), or *transversal*, is an injective map
`f : ι → α` with `f i ∈ t i` for every `i` — a way to choose a distinct representative from
each set.  **Hall's marriage theorem** characterizes exactly when one exists: an SDR exists
iff **Hall's condition** holds, namely that every sub-family covers at least as many elements
as it has members,

`∀ s : Finset ι, #s ≤ #(s.biUnion t)`.

Mathlib proves the biconditional in `Finset.all_card_le_biUnion_card_iff_exists_injective`
(`Mathlib/Combinatorics/Hall/Basic.lean`), via Rado's compactness argument over the finite
case.  What Mathlib does **not** package — and what this file adds — are the two practical
faces of the theorem used in applications:

## New content

* **Necessity, standalone** (`hall_condition_of_sdr`, `hall_condition_of_exists_sdr`).  The
  easy direction proved directly, *not* extracted from the biconditional: if an SDR exists
  then Hall's condition holds.  The proof is one counting step — `s.image f ⊆ s.biUnion t` and
  `f` injective forces `#s = #(s.image f) ≤ #(s.biUnion t)`.  This direction needs **no**
  finiteness of `ι` and no compactness, so isolating it is genuinely cheaper than invoking the
  full theorem.

* **The deficiency / failure obstruction** (`no_sdr_of_deficiency`).  The contrapositive form
  actually used to *certify non-existence*: if some sub-family is "deficient"
  (`#(s.biUnion t) < #s`, more members than available representatives) then **no** SDR exists.
  This is the workhorse for proving a matching impossible.

* **Concrete `0`-axiom witnesses** (`hall_satisfiable_example`, `hall_violating_example`).  A
  satisfying `Fin 3` family with an exhibited transversal, and a violating family
  (`t₀ = t₁ = t₂ = {0,1}`) where three indices compete for two values, certified impossible
  through the deficiency theorem.  Both are checked by **kernel `decide`** (not
  `native_decide`), so they carry no `Lean.ofReduceBool` and remain axiom-free.

## What this file packages

* `HallMarriage.hall_marriage_iff` — re-export of Mathlib's biconditional (badge: mathlib).
* `HallMarriage.exists_sdr_of_hall` — sufficiency direction as a standalone corollary.
* `HallMarriage.hall_condition_of_sdr` / `hall_condition_of_exists_sdr` — necessity, proved
  directly by a counting argument.
* `HallMarriage.no_sdr_of_deficiency` — the deficiency obstruction (new).
* `HallMarriage.hall_violating_deficiency` — a concrete deficient sub-family.
* `HallMarriage.hall_satisfiable_example` / `hall_violating_example` — concrete witnesses.

All results are `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).
-/

namespace HallMarriage

variable {ι α : Type*} [DecidableEq α]

/-- **Hall's marriage theorem** (re-export).  For a family `t : ι → Finset α`, a system of
distinct representatives — an injective `f` with `f i ∈ t i` for all `i` — exists iff every
sub-family `s` satisfies Hall's condition `#s ≤ #(s.biUnion t)`.  This is Mathlib's
`Finset.all_card_le_biUnion_card_iff_exists_injective`, the foundation the corollaries below
refine. -/
theorem hall_marriage_iff (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  Finset.all_card_le_biUnion_card_iff_exists_injective t

/-- **Sufficiency direction.**  If Hall's condition holds for every sub-family, then a system
of distinct representatives exists.  (The substantive half of the theorem; relies on Mathlib's
compactness argument.) -/
theorem exists_sdr_of_hall {t : ι → Finset α}
    (h : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  (hall_marriage_iff t).mp h

/-- **Necessity, direct proof.**  If `f` is an injective transversal of `t` then Hall's
condition holds: every sub-family covers at least as many elements as it has members.  Proved
by the counting inequality `#s = #(s.image f) ≤ #(s.biUnion t)`, using only that `f` is
injective and lands in the sets — no finiteness of `ι`, no compactness. -/
theorem hall_condition_of_sdr {t : ι → Finset α} {f : ι → α}
    (hinj : Function.Injective f) (hf : ∀ x, f x ∈ t x) (s : Finset ι) :
    s.card ≤ (s.biUnion t).card := by
  calc s.card = (s.image f).card := (Finset.card_image_of_injective s hinj).symm
    _ ≤ (s.biUnion t).card :=
        Finset.card_le_card (by
          intro a ha
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
          exact Finset.mem_biUnion.mpr ⟨x, hx, hf x⟩)

/-- **Necessity, existential form.**  If *some* system of distinct representatives exists, then
Hall's condition holds.  This is the clean standalone converse of `exists_sdr_of_hall`, proved
without re-deriving the biconditional. -/
theorem hall_condition_of_exists_sdr {t : ι → Finset α}
    (h : ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x) (s : Finset ι) :
    s.card ≤ (s.biUnion t).card := by
  obtain ⟨f, hinj, hf⟩ := h
  exact hall_condition_of_sdr hinj hf s

/-- **The deficiency obstruction.**  If a sub-family `s` is *deficient* — it has strictly more
members than the number of elements its sets jointly cover, `#(s.biUnion t) < #s` — then **no**
system of distinct representatives exists.  This is the contrapositive of necessity and the
form used in practice to certify that a matching is impossible. -/
theorem no_sdr_of_deficiency {t : ι → Finset α} {s : Finset ι}
    (hs : (s.biUnion t).card < s.card) :
    ¬ ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := fun h =>
  absurd (hall_condition_of_exists_sdr h s) (not_le.mpr hs)

/-! ### Concrete witnesses over `Fin 3` (kernel `decide`, axiom-free) -/

/-- **A satisfiable instance.**  The family `t₀ = {0,1}`, `t₁ = {1,2}`, `t₂ = {0,2}` over
`Fin 3` admits the identity transversal `f = ![0,1,2]`: it is injective and `f i ∈ t i` for
each `i`.  (Verified by kernel `decide` searching the `3³` candidate maps.) -/
theorem hall_satisfiable_example :
    ∃ f : Fin 3 → Fin 3, Function.Injective f ∧
      ∀ x, f x ∈ (![({0, 1} : Finset (Fin 3)), {1, 2}, {0, 2}]) x := by
  decide

/-- **A deficient sub-family.**  For the family `t₀ = t₁ = t₂ = {0,1}` over `Fin 3`, the whole
index set `univ` covers only `{0,1}` — two elements for three indices — so
`#(univ.biUnion t) = 2 < 3 = #univ`. -/
theorem hall_violating_deficiency :
    ((Finset.univ : Finset (Fin 3)).biUnion
        (![({0, 1} : Finset (Fin 3)), {0, 1}, {0, 1}])).card
      < (Finset.univ : Finset (Fin 3)).card := by
  decide

/-- **A violating instance.**  Because three indices compete for the two values `{0,1}`, the
family `t₀ = t₁ = t₂ = {0,1}` has **no** system of distinct representatives.  Established not by
brute force over the maps but by applying the deficiency obstruction to the deficient sub-family
`univ` — exactly how Hall's theorem is used to rule out a matching. -/
theorem hall_violating_example :
    ¬ ∃ f : Fin 3 → Fin 3, Function.Injective f ∧
      ∀ x, f x ∈ (![({0, 1} : Finset (Fin 3)), {0, 1}, {0, 1}]) x :=
  no_sdr_of_deficiency hall_violating_deficiency

end HallMarriage
