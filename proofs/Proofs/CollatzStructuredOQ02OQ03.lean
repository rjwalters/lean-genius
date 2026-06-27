/-
# OQ-02 OQ-03: Tao's 2019 Almost-All Bound — A Feasibility Anchor

Open question OQ-03 of `collatz-structured-oq-02` (Collatz Cycles):

  "Can Tao's 2019 almost-all result (logarithmic density 1) be formalized in Lean
   using Mathlib's measure theory and ergodic theory libraries?"

Tao (2019, *Forum Math. Pi*, "Almost all orbits of the Collatz map attain almost
bounded values") proved: for every `f : ℕ → ℝ` with `f n → ∞`, the set of starting
values `n` whose orbit minimum `Col_min(n)` drops below `f n` has **logarithmic
density 1**.  This subsumes the classical Terras/Korec "almost all have finite
stopping time" statements and pushes the bound from "below `n`" down to "below any
slowly growing `f`".

## What resists formalization (honest assessment)

Tao's proof is genuinely analytic and is **out of reach of a direct Lean proof
today** (BLOCKED, >> 1000 lines):

  * It runs the Collatz/Syracuse dynamics against a carefully chosen family of
    measures on the 3-adics / on residue classes, and controls the evolution of
    those measures (a transport/coupling argument), establishing that the pushed
    forward measures concentrate.
  * The quantitative heart is a **stable point estimate** obtained from a
    `3`-adic large-deviation / entropy bound, combined with a Fourier-analytic
    input.  Mathlib currently has the general measure-theory and `Tendsto`
    plumbing used below, but not the specialised concentration/transport
    estimates Tao needs; building those is the real cost.

So, mirroring the sibling files `CollatzStructuredOQ02OQ01.lean` (which axiomatized
the Eliahou bound) and `CollatzStructuredOQ02OQ02.lean` (which proved Eliahou's
algebraic core and isolated the finite-check residue), this file:

  * gives a **precise, machine-checkable statement** of Tao's theorem
    (`tao_2019`) so the open question is no longer informal, and the
    "logarithmic density 1" target is pinned down as `HasLogDensityOne`;
  * proves, **unconditionally and axiom-free**, that several large explicit families
    of starting values already satisfy the "drops below itself" conclusion — the
    even numbers, the powers of two, the odd residue class `n ≡ 1 (mod 4)`
    (`n ≥ 5`), and the odd residue class `n ≡ 3 (mod 16)` — so the elementary part of
    the almost-all picture is real Lean content, not scaffolding on the axiom.  The
    evens together with `1 + 4ℕ` and `3 + 16ℕ` cover **thirteen-sixteenths** of the
    integers via elementary residue dynamics (`attainsBelow_density_lower_16`, a
    machine-checked `≥ 13/16` lower density), and the `mod 4`/`mod 16` families
    exercise the non-trivial `3n+1` branch of the map.  Of the odd classes
    `n ≡ 3 (mod 4)`, `n ≡ 3 (mod 16)` is precisely the one that drops within its
    residue-determined window; `7, 11, 15 (mod 16)` have `m`-dependent stopping times.

References:
- Tao, T. (2019). "Almost all orbits of the Collatz map attain almost bounded
  values." *Forum Math. Pi* 8, e9.
- Terras, R. (1976). "A stopping time problem on the positive integers."
- Korec, I. (1994). "A density estimate for the 3x+1 problem."
-/
import Mathlib

namespace CollatzStructuredOQ02OQ03

open Filter

/-! ## Part I: The Collatz map (self-contained) -/

/-- The Collatz function: `n ↦ n/2` if even, `n ↦ 3n+1` if odd. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

theorem collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

theorem collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz
  rw [if_neg (by omega)]

theorem collatz_two_mul (n : ℕ) : collatz (2 * n) = n := by
  simp [collatz, Nat.mul_mod_right]

/-- The Collatz map sends positive numbers to positive numbers: `n/2 ≥ 1` for a
positive even `n` and `3n+1 ≥ 1` always.  This keeps `0` out of every orbit. -/
theorem collatz_pos {n : ℕ} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

/-- Positivity propagates along the whole orbit: no iterate of a positive start
is ever `0`. -/
theorem collatz_iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < collatz^[k] n := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact collatz_pos ih

/-! ## Part II: Explicit residue families that drop below their start

These are the unconditional, axiom-free part of the almost-all picture: whatever
Tao's analytic argument gives for *almost all* `n`, the even numbers, the powers
of two, and the odd residue classes `n ≡ 1 (mod 4)` (`n ≥ 5`) and `n ≡ 3 (mod 16)`
are handled by elementary explicit dynamics. -/

/-- `n` *attains a value below itself*: some positive number of Collatz steps
takes `n` to a strictly smaller value.  This is the "finite stopping time"
event whose almost-all behaviour Tao controls. -/
def AttainsBelow (n : ℕ) : Prop := ∃ k, 0 < k ∧ collatz^[k] n < n

/-- Every positive **even** number drops below itself in a single step. -/
theorem even_attainsBelow {n : ℕ} (hn : 1 ≤ n) (he : n % 2 = 0) : AttainsBelow n :=
  ⟨1, one_pos, by
    rw [Function.iterate_one, collatz_even he]
    exact Nat.div_lt_self hn (by norm_num)⟩

/-- A power of two collapses to `1` after exactly that many steps:
`collatz^[k] (2^k) = 1`. -/
theorem pow_two_reaches_one (k : ℕ) : collatz^[k] (2 ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hstep : collatz (2 ^ (k + 1)) = 2 ^ k := by
      rw [pow_succ']
      exact collatz_two_mul (2 ^ k)
    rw [hstep, ih]

/-- Every power of two `2^k` with `k ≥ 1` drops below itself (all the way to 1). -/
theorem pow_two_attainsBelow {k : ℕ} (hk : 1 ≤ k) : AttainsBelow (2 ^ k) := by
  refine ⟨k, hk, ?_⟩
  rw [pow_two_reaches_one]
  have h2 : (2 : ℕ) ≤ 2 ^ k := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk
  omega

/-- Every `n ≡ 1 (mod 4)` with `n ≥ 5` drops below itself in exactly three steps:
`4m+1 ↦ 12m+4 ↦ 6m+2 ↦ 3m+1`, and `3m+1 < 4m+1` once `m ≥ 1`.  Unlike the even
numbers and the powers of two, this is a *positive-density* (one-quarter) family of
genuinely **odd** starting values, so it adds new unconditional content beyond the
trivially-even cases: the first Collatz step here is the non-trivial `3n+1` branch. -/
theorem mod_four_one_attainsBelow {n : ℕ} (hn : 5 ≤ n) (h : n % 4 = 1) :
    AttainsBelow n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  refine ⟨3, by norm_num, ?_⟩
  have step1 : collatz (4 * m + 1) = 12 * m + 4 := by
    rw [collatz_odd (by omega)]; ring
  have step2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  have step3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [collatz_even (by omega)]; omega
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      step1, step2, step3]
  omega

/-- Every `n ≡ 3 (mod 16)` drops below itself in exactly six steps:
`16m+3 ↦ 48m+10 ↦ 24m+5 ↦ 72m+16 ↦ 36m+8 ↦ 18m+4 ↦ 9m+2`, and `9m+2 < 16m+3` for
every `m ≥ 0`.  All six parities are forced by the residue `mod 16` alone (independent
of `m`), so this is a genuine residue-class drop, not a per-number accident.  It is the
*one* new residue that stabilises at level `16`: of the odd classes `n ≡ 3 (mod 4)`
(i.e. `n mod 16 ∈ {3, 7, 11, 15}`), only `n ≡ 3` drops within its residue-determined
window — the classes `7, 11, 15 (mod 16)` have `m`-dependent stopping times and require
a finer modulus.  Adding this class lifts the unconditional density floor from `3/4` to
`13/16`. -/
theorem mod_sixteen_three_attainsBelow {n : ℕ} (h : n % 16 = 3) : AttainsBelow n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 16 * m + 3 := ⟨n / 16, by omega⟩
  refine ⟨6, by norm_num, ?_⟩
  have s1 : collatz (16 * m + 3) = 48 * m + 10 := by rw [collatz_odd (by omega)]; ring
  have s2 : collatz (48 * m + 10) = 24 * m + 5 := by rw [collatz_even (by omega)]; omega
  have s3 : collatz (24 * m + 5) = 72 * m + 16 := by rw [collatz_odd (by omega)]; ring
  have s4 : collatz (72 * m + 16) = 36 * m + 8 := by rw [collatz_even (by omega)]; omega
  have s5 : collatz (36 * m + 8) = 18 * m + 4 := by rw [collatz_even (by omega)]; omega
  have s6 : collatz (18 * m + 4) = 9 * m + 2 := by rw [collatz_even (by omega)]; omega
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_zero_apply, s1, s2, s3, s4, s5, s6]
  omega

/-- Packaging: every positive `n` that is **even** or lies in `1 + 4ℕ` (with `n ≥ 5`)
attains a value below itself.  Together these cover three-quarters of the integers,
all handled by elementary dynamics with no appeal to Tao's axiom. -/
theorem even_or_mod_four_one_attainsBelow {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1)) : AttainsBelow n := by
  rcases h with he | ⟨h5, h1⟩
  · exact even_attainsBelow hn he
  · exact mod_four_one_attainsBelow h5 h1

/-- Extended packaging: every positive `n` that is **even**, lies in `1 + 4ℕ` (`n ≥ 5`),
or lies in `3 + 16ℕ` attains a value below itself.  These three elementary families
together cover thirteen-sixteenths of the integers — the current unconditional floor
beneath Tao's density-one theorem, with no appeal to the axiom. -/
theorem even_or_mod_four_one_or_mod_sixteen_three_attainsBelow {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1) ∨ n % 16 = 3) : AttainsBelow n := by
  rcases h with he | h1 | h3
  · exact even_attainsBelow hn he
  · exact mod_four_one_attainsBelow h1.1 h1.2
  · exact mod_sixteen_three_attainsBelow h3

/-! ## Part II.5: A quantitative density floor of 3/4

The prose "these families cover three-quarters of the integers" is upgraded here to
a machine-checked counting bound: among the first `4N` positive integers, at least
`3N - 1` already attain a value below themselves (the `2N` evens together with the
`N - 1` members of `1 + 4ℕ` that are `≥ 5`).  Dividing by `4N` and letting `N → ∞`,
the drop-below set has **lower natural density `≥ 3/4`** — the unconditional,
axiom-free floor underneath Tao's density-one theorem. -/

open Classical in
/-- **Quantitative density lower bound.**  At least `3N - 1` of the integers in
`[1, 4N]` attain a value below themselves.  The witnesses are the evens (an
injective image of `[1, 2N]` under `j ↦ 2j`) and the class `1 + 4ℕ` with value `≥ 5`
(an injective image of `[1, N-1]` under `j ↦ 4j+1`); these are disjoint by parity,
giving `2N + (N-1) = 3N - 1` distinct drop-below starts. -/
theorem attainsBelow_density_lower (N : ℕ) :
    3 * N - 1 ≤
      ((Finset.Icc 1 (4 * N)).filter (fun n => AttainsBelow n)).card := by
  classical
  -- The evens `2, 4, …, 4N`, as an injective image of `[1, 2N]`.
  set E : Finset ℕ := (Finset.Icc 1 (2 * N)).image (fun j => 2 * j) with hE
  -- The class `1 + 4ℕ` with value `≥ 5`: `5, 9, …, 4N-3`, an image of `[1, N-1]`.
  set O : Finset ℕ := (Finset.Icc 1 (N - 1)).image (fun j => 4 * j + 1) with hO
  have hEinj : Function.Injective (fun j : ℕ => 2 * j) :=
    fun a b h => by have h' : 2 * a = 2 * b := h; omega
  have hOinj : Function.Injective (fun j : ℕ => 4 * j + 1) :=
    fun a b h => by have h' : 4 * a + 1 = 4 * b + 1 := h; omega
  have hEcard : E.card = 2 * N := by
    rw [hE, Finset.card_image_of_injective _ hEinj, Nat.card_Icc]; omega
  have hOcard : O.card = N - 1 := by
    rw [hO, Finset.card_image_of_injective _ hOinj, Nat.card_Icc]; omega
  -- Parity separates the two families.
  have hEeven : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx; rw [hE, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show 2 * i % 2 = 0; omega
  have hOodd : ∀ x ∈ O, x % 2 = 1 := by
    intro x hx; rw [hO, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (4 * i + 1) % 2 = 1; omega
  have hdisj : Disjoint E O :=
    Finset.disjoint_left.mpr fun a haE haO => by
      have h1 := hEeven a haE; have h2 := hOodd a haO; omega
  -- Both families consist of drop-below starts in range.
  have hsub : E ∪ O ⊆ (Finset.Icc 1 (4 * N)).filter (fun n => AttainsBelow n) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    rcases hx with hxE | hxO
    · rw [hE, Finset.mem_image] at hxE
      obtain ⟨j, hj, rfl⟩ := hxE
      rw [Finset.mem_Icc] at hj
      show (1 ≤ 2 * j ∧ 2 * j ≤ 4 * N) ∧ AttainsBelow (2 * j)
      exact ⟨⟨by omega, by omega⟩, even_attainsBelow (by omega) (by omega)⟩
    · rw [hO, Finset.mem_image] at hxO
      obtain ⟨j, hj, rfl⟩ := hxO
      rw [Finset.mem_Icc] at hj
      show (1 ≤ 4 * j + 1 ∧ 4 * j + 1 ≤ 4 * N) ∧ AttainsBelow (4 * j + 1)
      exact ⟨⟨by omega, by omega⟩, mod_four_one_attainsBelow (by omega) (by omega)⟩
  calc 3 * N - 1 ≤ E.card + O.card := by rw [hEcard, hOcard]; omega
    _ = (E ∪ O).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **Sharpened quantitative density lower bound (`13/16`).**  Adjoining the residue
class `3 + 16ℕ` to the evens and `1 + 4ℕ` lifts the count: among the integers in
`[1, 16N]`, at least `13N - 1` already attain a value below themselves — the `8N` evens,
the `4N - 1` members of `1 + 4ℕ` that are `≥ 5`, and the `N` members of `3 + 16ℕ`.
The three families are pairwise disjoint (evens by parity; `1 + 4ℕ` vs `3 + 16ℕ` by their
residues `1` and `3` mod `4`), giving `8N + (4N - 1) + N = 13N - 1` distinct drop-below
starts.  Dividing by `16N` and letting `N → ∞`, the drop-below set has **lower natural
density `≥ 13/16`** — strictly above the previous `3/4` floor. -/
theorem attainsBelow_density_lower_16 (N : ℕ) :
    13 * N - 1 ≤
      ((Finset.Icc 1 (16 * N)).filter (fun n => AttainsBelow n)).card := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  -- The evens `2, 4, …, 16N`, an injective image of `[1, 8N]`.
  set E : Finset ℕ := (Finset.Icc 1 (8 * N)).image (fun j => 2 * j) with hE
  -- The class `1 + 4ℕ` with value `≥ 5`: `5, 9, …, 16N-3`, an image of `[1, 4N-1]`.
  set O1 : Finset ℕ := (Finset.Icc 1 (4 * N - 1)).image (fun j => 4 * j + 1) with hO1
  -- The class `3 + 16ℕ`: `3, 19, …, 16N-13`, an image of `[0, N-1]`.
  set O3 : Finset ℕ := (Finset.Icc 0 (N - 1)).image (fun j => 16 * j + 3) with hO3
  have hEinj : Function.Injective (fun j : ℕ => 2 * j) :=
    fun a b h => by have h' : 2 * a = 2 * b := h; omega
  have hO1inj : Function.Injective (fun j : ℕ => 4 * j + 1) :=
    fun a b h => by have h' : 4 * a + 1 = 4 * b + 1 := h; omega
  have hO3inj : Function.Injective (fun j : ℕ => 16 * j + 3) :=
    fun a b h => by have h' : 16 * a + 3 = 16 * b + 3 := h; omega
  have hEcard : E.card = 8 * N := by
    rw [hE, Finset.card_image_of_injective _ hEinj, Nat.card_Icc]; omega
  have hO1card : O1.card = 4 * N - 1 := by
    rw [hO1, Finset.card_image_of_injective _ hO1inj, Nat.card_Icc]; omega
  have hO3card : O3.card = N := by
    rw [hO3, Finset.card_image_of_injective _ hO3inj, Nat.card_Icc]; omega
  -- Residues separate the three families.
  have hEeven : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx; rw [hE, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show 2 * i % 2 = 0; omega
  have hO1mod4 : ∀ x ∈ O1, x % 4 = 1 := by
    intro x hx; rw [hO1, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (4 * i + 1) % 4 = 1; omega
  have hO3mod4 : ∀ x ∈ O3, x % 4 = 3 := by
    intro x hx; rw [hO3, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (16 * i + 3) % 4 = 3; omega
  have hd_E_O1 : Disjoint E O1 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hEeven a ha; have := hO1mod4 a hb; omega
  have hd_E_O3 : Disjoint E O3 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hEeven a ha; have := hO3mod4 a hb; omega
  have hd_O1_O3 : Disjoint O1 O3 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hO1mod4 a ha; have := hO3mod4 a hb; omega
  have hd_EO1_O3 : Disjoint (E ∪ O1) O3 :=
    Finset.disjoint_union_left.mpr ⟨hd_E_O3, hd_O1_O3⟩
  have hcard : (E ∪ O1 ∪ O3).card = E.card + O1.card + O3.card := by
    rw [Finset.card_union_of_disjoint hd_EO1_O3, Finset.card_union_of_disjoint hd_E_O1]
  -- All three families consist of drop-below starts in range.
  have hsub : E ∪ O1 ∪ O3 ⊆ (Finset.Icc 1 (16 * N)).filter (fun n => AttainsBelow n) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (hxE | hxO1) | hxO3
    · rw [hE, Finset.mem_image] at hxE
      obtain ⟨j, hj, rfl⟩ := hxE; rw [Finset.mem_Icc] at hj
      show (1 ≤ 2 * j ∧ 2 * j ≤ 16 * N) ∧ AttainsBelow (2 * j)
      exact ⟨⟨by omega, by omega⟩, even_attainsBelow (by omega) (by omega)⟩
    · rw [hO1, Finset.mem_image] at hxO1
      obtain ⟨j, hj, rfl⟩ := hxO1; rw [Finset.mem_Icc] at hj
      show (1 ≤ 4 * j + 1 ∧ 4 * j + 1 ≤ 16 * N) ∧ AttainsBelow (4 * j + 1)
      exact ⟨⟨by omega, by omega⟩, mod_four_one_attainsBelow (by omega) (by omega)⟩
    · rw [hO3, Finset.mem_image] at hxO3
      obtain ⟨j, hj, rfl⟩ := hxO3; rw [Finset.mem_Icc] at hj
      show (1 ≤ 16 * j + 3 ∧ 16 * j + 3 ≤ 16 * N) ∧ AttainsBelow (16 * j + 3)
      exact ⟨⟨by omega, by omega⟩, mod_sixteen_three_attainsBelow (by omega)⟩
  calc 13 * N - 1 ≤ E.card + O1.card + O3.card := by rw [hEcard, hO1card, hO3card]; omega
    _ = (E ∪ O1 ∪ O3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ## Part III: The orbit minimum and logarithmic density -/

/-- The **orbit minimum** of `n`: the infimum of the values visited by the
Collatz orbit of `n` (including `n` itself).  `Col_min` in Tao's notation. -/
noncomputable def colMin (n : ℕ) : ℕ := sInf {m | ∃ k, collatz^[k] n = m}

/-- The orbit minimum never exceeds the starting value (`k = 0` visits `n`). -/
theorem colMin_le_self (n : ℕ) : colMin n ≤ n :=
  Nat.sInf_le ⟨0, Function.iterate_zero_apply collatz n⟩

/-- The orbit of a power of two reaches `1`, so its orbit minimum is `≤ 1`. -/
theorem colMin_pow_two_le_one (k : ℕ) : colMin (2 ^ k) ≤ 1 :=
  Nat.sInf_le ⟨k, pow_two_reaches_one k⟩

/-- The orbit minimum of a positive start is itself positive: `0` never occurs in
the orbit (`collatz_iterate_pos`), and the orbit is non-empty, so its infimum is
`≥ 1`. -/
theorem colMin_pos {n : ℕ} (hn : 0 < n) : 0 < colMin n := by
  unfold colMin
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [Nat.sInf_eq_zero] at h
  rcases h with h0 | hempty
  · obtain ⟨k, hk⟩ := h0
    have := collatz_iterate_pos hn k
    rw [hk] at this
    exact absurd this (lt_irrefl 0)
  · have hmem : n ∈ {m | ∃ k, collatz^[k] n = m} :=
      ⟨0, Function.iterate_zero_apply collatz n⟩
    rw [hempty] at hmem
    exact hmem

/-- Sharpening `colMin_pow_two_le_one`: the orbit minimum of `2^k` is **exactly**
`1` (the orbit hits `1` and, being positive, never goes lower). -/
theorem colMin_pow_two_eq_one (k : ℕ) : colMin (2 ^ k) = 1 := by
  have hle := colMin_pow_two_le_one k
  have hpos := colMin_pos (n := 2 ^ k) (by positivity)
  omega

/-- **Bridge between Parts II and III.**  Any number that attains a value below
itself has orbit minimum strictly below its start: `colMin n < n`.  This connects
the explicit drop-below families to Tao's `Col_min` predicate (the `f n = n`
specialisation). -/
theorem attainsBelow_colMin_lt {n : ℕ} (h : AttainsBelow n) : colMin n < n := by
  obtain ⟨k, _, hlt⟩ := h
  refine lt_of_le_of_lt ?_ hlt
  exact Nat.sInf_le ⟨k, rfl⟩

/-- Consequently the entire three-quarters family of Part II — the even numbers
and the odd class `1 + 4ℕ` (`n ≥ 5`) — has orbit minimum strictly below the start,
unconditionally and without Tao's axiom. -/
theorem even_or_mod_four_one_colMin_lt {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1)) : colMin n < n :=
  attainsBelow_colMin_lt (even_or_mod_four_one_attainsBelow hn h)

/-- The new residue class `3 + 16ℕ` likewise has orbit minimum strictly below its start,
unconditionally and without Tao's axiom. -/
theorem mod_sixteen_three_colMin_lt {n : ℕ} (h : n % 16 = 3) : colMin n < n :=
  attainsBelow_colMin_lt (mod_sixteen_three_attainsBelow h)

/-- The full thirteen-sixteenths family — evens, `1 + 4ℕ` (`n ≥ 5`), and `3 + 16ℕ` —
has orbit minimum strictly below the start. -/
theorem even_or_mod_four_one_or_mod_sixteen_three_colMin_lt {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1) ∨ n % 16 = 3) : colMin n < n :=
  attainsBelow_colMin_lt (even_or_mod_four_one_or_mod_sixteen_three_attainsBelow hn h)

/-- The logarithmic-density partial average of a set `S` up to `N`:
`(∑_{n≤N, n∈S} 1/n) / (∑_{n≤N} 1/n)`. -/
noncomputable def logDensity (S : Set ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N, S.indicator (fun m => (1 : ℝ) / m) n)
    / (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n)

/-- `S` has **logarithmic density one** if its partial averages tend to `1`. -/
def HasLogDensityOne (S : Set ℕ) : Prop :=
  Tendsto (logDensity S) atTop (nhds 1)

/-! ## Part IV: Tao's theorem (axiomatized, deep)

The precise statement of Tao (2019).  This is the result whose formalization the
open question asks about; we record it as a single axiom and document above why a
direct Lean proof is currently out of reach.  No theorem in this file is derived
from it — the content of Parts II–III stands on its own. -/

/--
**Tao (2019):** for every `f : ℕ → ℝ` tending to infinity, the set of positive
starting values whose orbit minimum is eventually below `f n` has logarithmic
density one.  Taking `f n = n` recovers "almost all `n` have finite stopping
time"; the strength of the theorem is that `f` may grow arbitrarily slowly.
-/
axiom tao_2019 :
    ∀ f : ℕ → ℝ, Tendsto f atTop atTop →
      HasLogDensityOne {n : ℕ | 0 < n ∧ (colMin n : ℝ) < f n}

end CollatzStructuredOQ02OQ03
