/-
# Constructive CRT certificate for a list of pairwise-coprime moduli (OQ-05-OQ-01-OQ-01)

The sibling entry **chinese-remainder-constructive-oq-05-oq-01** packaged the
Chinese Remainder Theorem into clean *bounded-range certificates*

    crt_pair_iff   : (x % m = a ∧ x % n = b)            ↔ x = N   (two moduli)
    crt_triple_iff : (x % m = a ∧ x % n = b ∧ x % p = c) ↔ x = N   (three moduli)

each asserting, over `0 ≤ x < m·n(·p)`, that the residue conditions pin down a
*unique* witness `N`, and each deliberately avoiding `native_decide` so that the
numeric worked examples stay `Lean.ofReduceBool`-free.  That file explicitly
"stopped at three moduli".

This entry removes the arity ceiling: we build the certificate for an
**arbitrary list** `ms : List ℕ` of pairwise-coprime moduli.  Two headline results:

* `crt_list_mod_iff` — the uniqueness-in-range certificate.  For pairwise coprime
  `ms`, a witness `N < ms.prod`, and any `x < ms.prod`,

      (∀ m ∈ ms, x % m = N % m)  ↔  x = N.

  Specialising `ms` to `[m, n]` or `[m, n, p]` recovers the sibling's
  `crt_pair_iff` / `crt_triple_iff`, so this is a strict generalisation.

* `crt_list_existsUnique` — the full **existence-and-uniqueness** capstone for
  arbitrary residue targets.  Mathlib supplies the ingredients separately
  (`Nat.chineseRemainderOfList` for existence, `…_lt_prod` for the bound,
  `…_modEq_unique` for uniqueness); we assemble them into the single `∃!`
  statement

      ∃! x, x < (l.map s).prod ∧ ∀ i ∈ l, x ≡ a i [MOD s i]

  which is the CRT bijection onto `Fin (∏ sᵢ)` in `ExistsUnique` form.

We then exercise the list certificate on two examples, both kernel-checked: the
three-modulus `x = 11` mod `60` (reproving the sibling's `crt_11_mod_60` through
the list machinery) and a genuinely new **four-modulus** example `x = 100` mod
`210 = 2·3·5·7`, out of reach of the triple certificate.

`#print axioms` on every theorem lists only `propext / Classical.choice /
Quot.sound`: no `native_decide`, no `Lean.ofReduceBool`, no `sorry`, no `axiom`.
-/
import Mathlib

namespace ChineseRemainderConstructiveOQ05OQ01OQ01

open scoped Function -- for the `on` notation in `Nat.Coprime on s`

/- ## The list certificate -/

/-- **List CRT certificate (uniqueness in range).** For pairwise coprime moduli
`ms`, a witness `N < ms.prod`, and any `x` in the range `0 ≤ x < ms.prod`, the
conjunction of the congruences `x ≡ N (mod mᵢ)` (written as residue equalities
`x % mᵢ = N % mᵢ`) holds *iff* `x = N`.

Generalises the sibling's `crt_pair_iff` / `crt_triple_iff` to arbitrary arity.
The forward direction assembles the per-modulus congruences into a single
congruence modulo `ms.prod` via `Nat.modEq_list_map_prod_iff`; since both `x` and
`N` lie below the modulus, that congruence forces equality. -/
theorem crt_list_mod_iff {ms : List ℕ} (co : ms.Pairwise Nat.Coprime)
    {N x : ℕ} (hN : N < ms.prod) (hx : x < ms.prod) :
    (∀ m ∈ ms, x % m = N % m) ↔ x = N := by
  constructor
  · intro h
    have key := Nat.modEq_list_map_prod_iff (a := x) (b := N) (s := id) (l := ms)
      (co.imp fun h => h)
    simp only [List.map_id, id_eq] at key
    have hcong : x ≡ N [MOD ms.prod] := key.mpr h
    have hmod : x % ms.prod = N % ms.prod := hcong
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hN] at hmod
  · rintro rfl
    intro m _
    rfl

/-- **List CRT: existence and uniqueness.** For pairwise coprime moduli `s i`
(`i ∈ l`, all nonzero) and arbitrary residue targets `a i`, there is a *unique*
natural number below the product `∏ sᵢ` congruent to each `a i` modulo `s i`.

The witness is Mathlib's constructive `Nat.chineseRemainderOfList`; uniqueness
follows from `chineseRemainderOfList_modEq_unique`, since two solutions below the
product that are congruent modulo it must be equal. This is the CRT bijection
onto `Fin (∏ sᵢ)` packaged as a single `ExistsUnique`. -/
theorem crt_list_existsUnique {ι : Type*} (s a : ι → ℕ) (l : List ι)
    (co : l.Pairwise (Nat.Coprime on s)) (hs : ∀ i ∈ l, s i ≠ 0) :
    ∃! x, x < (l.map s).prod ∧ ∀ i ∈ l, x ≡ a i [MOD s i] := by
  refine ⟨(Nat.chineseRemainderOfList a s l co : ℕ), ⟨?_, ?_⟩, ?_⟩
  · exact Nat.chineseRemainderOfList_lt_prod a s l co hs
  · exact (Nat.chineseRemainderOfList a s l co).property
  · rintro y ⟨hy, hcong⟩
    have h1 : y ≡ (Nat.chineseRemainderOfList a s l co : ℕ) [MOD (l.map s).prod] :=
      Nat.chineseRemainderOfList_modEq_unique a s l co hcong
    have hk : (Nat.chineseRemainderOfList a s l co : ℕ) < (l.map s).prod :=
      Nat.chineseRemainderOfList_lt_prod a s l co hs
    have hmod : y % (l.map s).prod = (Nat.chineseRemainderOfList a s l co : ℕ) % (l.map s).prod :=
      h1
    rwa [Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hk] at hmod

/- ## Worked examples via the list certificate -/

/-- **`11` mod `60`, axiom-free, via the list certificate.** The sibling's
`crt_11_mod_60` is a direct `crt_triple_iff` instance; here the very same fact is
obtained from the arbitrary-arity `crt_list_mod_iff` on the modulus list
`[3, 4, 5]` (product `60`). Over `0 ≤ x < 60`, the congruences `x ≡ 2 (3)`,
`x ≡ 3 (4)`, `x ≡ 1 (5)` hold *iff* `x = 11`. -/
theorem crt_11_mod_60 (x : ℕ) (hx : x < 60) :
    (x % 3 = 2 ∧ x % 4 = 3 ∧ x % 5 = 1) ↔ x = 11 := by
  have h := crt_list_mod_iff (ms := [3, 4, 5]) (by decide) (N := 11)
    (by decide) (x := x) (by simpa using hx)
  simpa [List.forall_mem_cons] using h

/-- **`100` mod `210`, axiom-free — a genuinely four-modulus example.** With the
pairwise coprime list `[2, 3, 5, 7]` (product `210`), over `0 ≤ x < 210` the four
congruences `x ≡ 0 (2)`, `x ≡ 1 (3)`, `x ≡ 0 (5)`, `x ≡ 2 (7)` hold *iff*
`x = 100`. This is out of reach of the sibling's three-modulus `crt_triple_iff`;
`crt_list_mod_iff` handles any arity uniformly. -/
theorem crt_100_mod_210 (x : ℕ) (hx : x < 210) :
    (x % 2 = 0 ∧ x % 3 = 1 ∧ x % 5 = 0 ∧ x % 7 = 2) ↔ x = 100 := by
  have h := crt_list_mod_iff (ms := [2, 3, 5, 7]) (by decide) (N := 100)
    (by decide) (x := x) (by simpa using hx)
  simpa [List.forall_mem_cons] using h

end ChineseRemainderConstructiveOQ05OQ01OQ01
