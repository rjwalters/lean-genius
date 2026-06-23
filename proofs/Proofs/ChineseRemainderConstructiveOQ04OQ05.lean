/-
Chinese Remainder Theorem — Effective Canonical Solver (OQ-04-OQ-05)

Extends ChineseRemainderConstructiveOQ04OQ04.lean. Where OQ-04-OQ-04 proves
*non-constructively* that every pairwise-coprime system has a unique solution in
[0, M) (reduce an arbitrary solution mod M), this file exhibits that witness as
an explicit *computable* function `crtCanonical` by wrapping Mathlib's verified
combinator `Nat.chineseRemainderOfList`, and bridges the two frameworks:

  * the project's list-CRT (`CRTList.crt_list`, defined over `List (ℕ × ℕ)`), and
  * Mathlib's `Nat.chineseRemainderOfList (a s : ι → ℕ)` over an index list.

The system `sys : List (ℕ × ℕ)` is fed to Mathlib with `a = Prod.fst`,
`s = Prod.snd`, `l = sys`, so `(sys.map Prod.snd).prod = moduliProd sys` and
`Pairwise (Coprime on Prod.snd) sys ↔ (moduli sys).Pairwise Coprime`
(via `List.pairwise_map`).

Main results:
- `crtCanonical`           : computable solver `List (ℕ × ℕ) → ℕ`
- `crtCanonical_satisfies` : it solves the system
- `crtCanonical_lt`        : it lands in [0, M)  (positive moduli)
- `crtCanonical_eq_min`    : it equals the unique minimal solution of OQ-04-OQ-04
- `crtCanonical_isLeast`   : it is the *least* element of the whole solution set
- `sunzi_canonical_eq_23`  : the classic Sunzi system evaluates to 23

No `axiom`s, no `sorry`, no `native_decide` (the worked example uses `decide`).
-/

import Proofs.ChineseRemainderConstructiveOQ04OQ04

namespace CRTList

open Nat
open scoped Function -- `on` notation

/-! ## Bridge to Mathlib's index-list CRT -/

/-- Pairwise coprimality of the extracted moduli is exactly the
    `Pairwise (Coprime on Prod.snd)` hypothesis Mathlib's
    `chineseRemainderOfList` expects, via `List.pairwise_map`. -/
lemma sys_pairwise_on_snd {sys : List (ℕ × ℕ)}
    (hpc : (moduli sys).Pairwise Nat.Coprime) :
    sys.Pairwise (Nat.Coprime on Prod.snd) := by
  have h : (sys.map Prod.snd).Pairwise Nat.Coprime := hpc
  exact (List.pairwise_map (R := Nat.Coprime) (f := Prod.snd) (l := sys)).mp h

/-! ## Effective Canonical Solver -/

/-- **Effective canonical CRT solver.** For a system with pairwise-coprime
    moduli, returns the canonical representative in `{0, …, M−1}` produced by
    Mathlib's `Nat.chineseRemainderOfList`. Unlike the existence proof of
    OQ-04-OQ-04, this is a concrete computable function. -/
def crtCanonical (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime) : ℕ :=
  (Nat.chineseRemainderOfList Prod.fst Prod.snd sys (sys_pairwise_on_snd hpc) : ℕ)

/-- The canonical solver satisfies every congruence of the system: this is
    exactly the defining property of `Nat.chineseRemainderOfList`. -/
theorem crtCanonical_satisfies (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime) :
    Satisfies (crtCanonical sys hpc) sys := by
  intro p hp
  exact (Nat.chineseRemainderOfList Prod.fst Prod.snd sys
    (sys_pairwise_on_snd hpc)).property p hp

/-- The canonical solver lands in `[0, M)` (needs all moduli positive),
    via Mathlib's `chineseRemainderOfList_lt_prod`. -/
theorem crtCanonical_lt (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime)
    (hpos : ∀ p ∈ sys, 0 < p.2) :
    crtCanonical sys hpc < moduliProd sys := by
  have h := Nat.chineseRemainderOfList_lt_prod Prod.fst Prod.snd sys
    (sys_pairwise_on_snd hpc) (fun p hp => (hpos p hp).ne')
  simpa [moduliProd, moduli, crtCanonical] using h

/-- Product of positive moduli is positive. -/
lemma moduliProd_pos {sys : List (ℕ × ℕ)} (hpos : ∀ p ∈ sys, 0 < p.2) :
    0 < moduliProd sys := by
  simp only [moduliProd, moduli]
  apply List.prod_pos
  intro n hn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
  exact hpos p hp

/-! ## Bridge to the OQ-04-OQ-04 minimal representative -/

/-- **Bridge.** Any solution `x` in `[0, M)` coincides with `crtCanonical`:
    the explicit solver realises the unique minimal representative whose
    existence/uniqueness was proved non-constructively in OQ-04-OQ-04. -/
theorem crtCanonical_eq_min (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime)
    (hpos : ∀ p ∈ sys, 0 < p.2)
    {x : ℕ} (hx : x < moduliProd sys) (hxs : Satisfies x sys) :
    x = crtCanonical sys hpc :=
  crt_list_minimal_unique sys hpc (moduliProd_pos hpos) hx
    (crtCanonical_lt sys hpc hpos) hxs (crtCanonical_satisfies sys hpc)

/-- **Order characterisation.** `crtCanonical` is the *least* element of the
    entire solution set `{x | Satisfies x sys}`: it is a solution, and any
    other solution `y` satisfies `crtCanonical ≤ y` because
    `crtCanonical = y % M ≤ y`. -/
theorem crtCanonical_isLeast (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime)
    (hpos : ∀ p ∈ sys, 0 < p.2) :
    IsLeast {x | Satisfies x sys} (crtCanonical sys hpc) := by
  refine ⟨crtCanonical_satisfies sys hpc, ?_⟩
  intro y hy
  have hlt := crtCanonical_lt sys hpc hpos
  have hmod : crtCanonical sys hpc % moduliProd sys = y % moduliProd sys :=
    crt_list_unique sys hpc (crtCanonical_satisfies sys hpc) hy
  rw [Nat.mod_eq_of_lt hlt] at hmod
  calc crtCanonical sys hpc = y % moduliProd sys := hmod
    _ ≤ y := Nat.mod_le y _

/-! ## Concrete Verification: The Sunzi Problem

The classic Sunzi system
  x ≡ 2 (mod 3),  x ≡ 3 (mod 5),  x ≡ 2 (mod 7)
has canonical solution 23 in [0, 105). We compute it through the bridge,
using `decide` (no `native_decide`, so the file remains axiom-free). -/

theorem sunzi_canonical_eq_23
    (hpc : (moduli [(2, 3), (3, 5), (2, 7)]).Pairwise Nat.Coprime) :
    crtCanonical [(2, 3), (3, 5), (2, 7)] hpc = 23 := by
  refine (crtCanonical_eq_min _ hpc ?_ ?_ ?_).symm
  · decide                     -- hpos : ∀ p ∈ sys, 0 < p.2
  · decide                     -- hx   : 23 < moduliProd sys
  · intro p hp                 -- hxs  : Satisfies 23 sys
    fin_cases hp <;> decide

/-! ## Summary

`crtCanonical` upgrades OQ-04-OQ-04 from an existence statement to an explicit
algorithm:

1. **Constructive**: a computable `List (ℕ × ℕ) → ℕ` returning the canonical
   representative, built on Mathlib's certified `chineseRemainderOfList`.
2. **Correct & bounded**: `crtCanonical_satisfies` + `crtCanonical_lt` place it
   in `[0, M)` solving every congruence.
3. **Canonical**: `crtCanonical_eq_min` identifies it with the unique minimal
   representative of OQ-04-OQ-04, and `crtCanonical_isLeast` shows it is the
   least element of the entire solution set — the sharpest possible
   normal form.
-/

end CRTList
