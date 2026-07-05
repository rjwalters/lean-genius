import Proofs.RamseyR4k
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-
# Multicolor Ramsey: extending `RamseyProp` from 2 colors to `c` colors (OQ-04)

## What This Proves

The gallery's `RamseyR4k.RamseyProp n r s` encodes the *two-colour* Ramsey
property: every red/blue edge-colouring of the complete graph `K_n` contains a
red `r`-clique or a blue `s`-clique.  The open question ramsey-r4k-oq-04 asks to
extend this framework to **multicolourings** (`c` colours) and to hypergraphs.

This file settles the **multicolouring** half completely and machine-verified:

* `RamseyMulti n c t` — the `c`-colour Ramsey property: every colouring
  `f : Fin n → Fin n → Fin c` of the edges of `K_n` with `c` colours contains,
  for some colour `i`, a clique of size `≥ t i` monochromatic in colour `i`.

* `ramseyProp_exists` — the classical **two-colour Ramsey theorem**
  `∀ r s, ∃ n, RamseyProp n r s`, obtained from the gallery's recursive bound
  `ramsey_recursion` (`R(r,s) ≤ R(r-1,s) + R(r,s-1)`) by strong induction on
  `r + s`.  (The gallery had the recursion but not the packaged existence.)

* `ramseyMulti_transfer` — a subset-transfer lemma: if `K_m` has the `c`-colour
  property then so does every `m`-element vertex subset of a larger graph.

* `ramseyMulti_succ` — the **colour-merging reduction**, the heart of the
  multicolour theorem: collapsing colour `0` against "all other colours" turns a
  `(c+1)`-colouring into a 2-colouring; a `RamseyProp` clique in the merged
  colour then carries a `c`-colouring on which the `c`-colour property recurses.

* `ramseyMulti_exists` — the **multicolour Ramsey theorem**
  `∀ c ≥ 1, ∀ t, ∃ N, RamseyMulti N c t`, by induction on the number of colours,
  each step peeling one colour via `ramseyMulti_succ` and `ramseyProp_exists`.

* `ramseyMulti_two_iff_ramseyProp` — the bridge back to the existing gallery:
  the 2-colour instance of `RamseyMulti` is *equivalent* to `RamseyProp`.

Everything is fully verified: 0 sorries, 0 `axiom` declarations, no
`native_decide`.  Colours live in `Fin c`; the edge-colouring's diagonal is
irrelevant (cliques only constrain distinct pairs), so unlike `RamseyProp` we do
not carry an irreflexivity hypothesis.

The **hypergraph** half of OQ-04 is genuinely harder: the gallery's own
`RamseyHypergraph.ramsey_existence` still carries a `sorry` on the recursive
uniformity-induction case, so it is left open here.

Tags: combinatorics, ramsey-theory, multicolouring
-/

namespace RamseyR4kOQ04

open Finset RamseyR4k

/-!
## Part I: the multicolour Ramsey property
-/

/-- The **`c`-colour Ramsey property** on `K_n`.  Every edge-colouring
`f : Fin n → Fin n → Fin c` (symmetric on the edges) contains a clique of size
`≥ t i` monochromatic in some colour `i`.

The diagonal `f x x` is unconstrained: a clique only looks at distinct pairs. -/
def RamseyMulti (n c : ℕ) (t : Fin c → ℕ) : Prop :=
  ∀ (f : Fin n → Fin n → Fin c), (∀ x y, f x y = f y x) →
    ∃ (i : Fin c) (S : Finset (Fin n)),
      S.card ≥ t i ∧ ∀ x y, x ∈ S → y ∈ S → x ≠ y → f x y = i

/-- `RamseyMulti` is monotone in the vertex count `n`. -/
theorem ramseyMulti_mono_n {n m c : ℕ} (t : Fin c → ℕ) (h : n ≤ m)
    (hR : RamseyMulti n c t) : RamseyMulti m c t := by
  intro f hfsym
  let embed : Fin n → Fin m := fun i => ⟨i.val, by omega⟩
  have embed_inj : Function.Injective embed := by
    intro a b hab; exact Fin.ext (Fin.mk.inj hab)
  let f' : Fin n → Fin n → Fin c := fun i j => f (embed i) (embed j)
  obtain ⟨i, S, hS_card, hS_mono⟩ := hR f' (fun x y => hfsym _ _)
  refine ⟨i, S.map ⟨embed, embed_inj⟩, ?_, ?_⟩
  · rw [card_map]; exact hS_card
  · intro x y hx hy hxy
    simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hS_mono a b ha hb (fun h => hxy (congrArg embed h))

/-!
## Part II: the two-colour Ramsey theorem (existence)

The gallery has the recursive bound `ramsey_recursion` and the base cases, but
not the packaged existence statement `∀ r s, ∃ n, RamseyProp n r s`.  We supply
it by strong induction on `r + s`.
-/

/-- `RamseyProp n 0 s` holds for every `n`: the empty set is a red `0`-clique. -/
private theorem ramseyProp_zero_left (n s : ℕ) : RamseyProp n 0 s := by
  intro f _ _; exact Or.inl ⟨∅, by simp, by simp⟩

/-- `RamseyProp n r 0` holds for every `n`: the empty set is a blue `0`-clique. -/
private theorem ramseyProp_zero_right (n r : ℕ) : RamseyProp n r 0 := by
  intro f _ _; exact Or.inr ⟨∅, by simp, by simp⟩

/-- **Two-colour Ramsey theorem.** For all target sizes `r, s` there is a finite
`n` with `RamseyProp n r s`.  Proved by strong induction on `r + s`: the base
cases `r ≤ 1` or `s ≤ 1` are the gallery's `ramseyProp_*`, and the inductive
step is the gallery's recursive bound `R(r,s) ≤ R(r-1,s) + R(r,s-1)`. -/
theorem ramseyProp_exists : ∀ r s : ℕ, ∃ n, RamseyProp n r s := by
  -- strong induction on the sum r + s
  have key : ∀ N r s : ℕ, r + s ≤ N → ∃ n, RamseyProp n r s := by
    intro N
    induction N with
    | zero =>
      intro r s hrs
      have hr : r = 0 := by omega
      exact ⟨0, hr ▸ ramseyProp_zero_left 0 s⟩
    | succ N ih =>
      intro r s hrs
      match r, s with
      | 0, s => exact ⟨0, ramseyProp_zero_left 0 s⟩
      | r, 0 => exact ⟨0, ramseyProp_zero_right 0 r⟩
      | 1, (s+1) => exact ⟨1, ramseyProp_one_left 1 (s+1) le_rfl⟩
      | (r+1), 1 => exact ⟨1, ramseyProp_one_right 1 (r+1) le_rfl⟩
      | (r+2), (s+2) =>
        obtain ⟨n1, hn1⟩ := ih (r + 1) (s + 2) (by omega)
        obtain ⟨n2, hn2⟩ := ih (r + 2) (s + 1) (by omega)
        refine ⟨n1 + n2, ?_⟩
        have := ramsey_recursion n1 n2 (r+2) (s+2) (by omega) (by omega)
          (by simpa using hn1) (by simpa using hn2)
        exact this
  intro r s
  exact key (r + s) r s le_rfl

/-!
## Part III: subset transfer for the multicolour property

If `K_m` has the `c`-colour property, then every `m`-element subset `W` of the
vertex set of a larger graph does too.  This mirrors the `orderIsoOfFin`
extraction already used in the gallery's `ramsey_recursion`.
-/

/-- **Subset transfer.** Given `RamseyMulti m c t` and a vertex subset
`W : Finset (Fin N)` with `W.card ≥ m`, every symmetric `c`-colouring of `K_N`
has a monochromatic clique of colour `i` and size `≥ t i` *inside* `W`. -/
theorem ramseyMulti_transfer {N m c : ℕ} (t : Fin c → ℕ)
    (hR : RamseyMulti m c t) (W : Finset (Fin N)) (hW : W.card ≥ m)
    (f : Fin N → Fin N → Fin c) (hsym : ∀ x y, f x y = f y x) :
    ∃ (i : Fin c) (S : Finset (Fin N)),
      S ⊆ W ∧ S.card ≥ t i ∧ ∀ x y, x ∈ S → y ∈ S → x ≠ y → f x y = i := by
  -- extract an exactly-`m`-element subset `W₀ ⊆ W` and identify it with `Fin m`
  obtain ⟨W₀, hW₀sub, hW₀card⟩ := Finset.exists_subset_card_eq hW
  have hequiv := W₀.orderIsoOfFin hW₀card
  let embed : Fin m → Fin N := fun i => (hequiv i).val
  have embed_inj : Function.Injective embed :=
    fun a b hab => hequiv.injective (Subtype.val_injective hab)
  have embed_mem : ∀ i, embed i ∈ W := fun i => hW₀sub (hequiv i).prop
  -- pull the colouring back to `Fin m`
  let g : Fin m → Fin m → Fin c := fun a b => f (embed a) (embed b)
  obtain ⟨i, T, hT_card, hT_mono⟩ := hR g (fun x y => hsym _ _)
  refine ⟨i, T.map ⟨embed, embed_inj⟩, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_map, Function.Embedding.coeFn_mk] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact embed_mem a
  · rw [card_map]; exact hT_card
  · intro x y hx hy hxy
    simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hT_mono a b ha hb (fun h => hxy (congrArg embed h))

/-!
## Part IV: the colour-merging reduction

The inductive engine.  Merge colour `0` against the union of all other colours to
form a 2-colouring; a `RamseyProp` clique in the "colour 0" class is a
monochromatic `0`-clique, while a clique in the "other" class carries a genuine
`c`-colouring (the colours `1, …, c` relabelled to `0, …, c-1`) on which the
`c`-colour property recurses.
-/

/-- **Colour-merging reduction.** If `K_N` has the two-colour Ramsey property for
`(t 0, M)` and `K_M` has the `c`-colour property for the tail targets
`fun j => t j.succ`, then `K_N` has the `(c+1)`-colour property for `t`. -/
theorem ramseyMulti_succ {N M c : ℕ} (t : Fin (c+1) → ℕ) (hc : 1 ≤ c)
    (hbase : RamseyProp N (t 0) M)
    (hrec : RamseyMulti M c (fun j => t j.succ)) :
    RamseyMulti N (c+1) t := by
  intro f hfsym
  -- merged 2-colouring: `true` = colour 0, `false` = "some colour ≠ 0"
  let g : Fin N → Fin N → Bool :=
    fun x y => if x = y then false else decide ((f x y).val = 0)
  have hgsym : ∀ x y, g x y = g y x := by
    intro x y; simp only [g]
    by_cases h : x = y
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), hfsym]
  have hgirr : ∀ x, g x x = false := by intro x; simp [g]
  rcases hbase g hgsym hgirr with ⟨S, hS_card, hS_red⟩ | ⟨W, hW_card, hW_blue⟩
  · -- red clique in `g` ⇒ every edge is colour `0`
    refine ⟨0, S, by simpa using hS_card, ?_⟩
    intro x y hx hy hxy
    have := hS_red x y hx hy hxy
    simp only [g, if_neg hxy, decide_eq_true_eq] at this
    exact Fin.ext this
  · -- blue clique `W`: every edge inside `W` has colour `≠ 0`
    have hW_ne : ∀ x y, x ∈ W → y ∈ W → x ≠ y → (f x y).val ≠ 0 := by
      intro x y hx hy hxy
      have := hW_blue x y hx hy hxy
      simp only [g, if_neg hxy, decide_eq_false_iff_not] at this
      exact this
    -- relabel colours `1,…,c` to `0,…,c-1` by subtracting one
    let f' : Fin N → Fin N → Fin c :=
      fun x y => ⟨(f x y).val - 1, by have := (f x y).isLt; omega⟩
    have hf'sym : ∀ x y, f' x y = f' y x := by
      intro x y; simp only [f']; rw [Fin.mk.injEq]; rw [hfsym]
    -- recurse on `W` via subset transfer
    obtain ⟨i, T, hTsub, hT_card, hT_mono⟩ :=
      ramseyMulti_transfer (fun j => t j.succ) hrec W hW_card f' hf'sym
    refine ⟨i.succ, T, by simpa using hT_card, ?_⟩
    intro x y hx hy hxy
    have hxW := hTsub hx
    have hyW := hTsub hy
    have hne : (f x y).val ≠ 0 := hW_ne x y hxW hyW hxy
    have hf' : f' x y = i := hT_mono x y hx hy hxy
    -- decode: `f' x y = i` and `f x y ≠ 0` force `f x y = i.succ`
    have hval : (f x y).val - 1 = i.val := congrArg Fin.val hf'
    have : (f x y).val = i.val + 1 := by omega
    exact Fin.ext (by simpa [Fin.val_succ] using this)

/-!
## Part V: the multicolour Ramsey theorem
-/

/-- With a single colour every graph is monochromatic. -/
private theorem ramseyMulti_one (t : Fin 1 → ℕ) : RamseyMulti (t 0) 1 t := by
  intro f _
  refine ⟨0, Finset.univ, ?_, ?_⟩
  · simp [Finset.card_univ]
  · intro x y _ _ _; exact Subsingleton.elim _ _

/-- **Multicolour Ramsey theorem.** For every colour count `c ≥ 1` and every
tuple of target sizes `t : Fin c → ℕ`, there is a finite `N` such that every
`c`-colouring of `K_N` contains a monochromatic clique of colour `i` and size
`≥ t i` for some `i`.

Proof: induction on `c`.  The base `c = 1` is trivial; the step peels colour `0`
using the two-colour theorem `ramseyProp_exists` and the reduction
`ramseyMulti_succ`, recursing on the remaining `c` colours. -/
theorem ramseyMulti_exists :
    ∀ (c : ℕ), 1 ≤ c → ∀ (t : Fin c → ℕ), ∃ N, RamseyMulti N c t := by
  intro c
  induction c with
  | zero => intro h; omega
  | succ c ih =>
    intro _ t
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · subst hc0
      exact ⟨t 0, ramseyMulti_one t⟩
    · obtain ⟨M, hM⟩ := ih hcpos (fun j => t j.succ)
      obtain ⟨N, hN⟩ := ramseyProp_exists (t 0) M
      exact ⟨N, ramseyMulti_succ t hcpos hN hM⟩

/-- **Diagonal multicolour Ramsey.** Specialising all targets to a common size
`k` recovers the exact statement the gallery currently *axiomatises* as
`RamseysTheorem.multicolor_ramsey_exists` (see `RamseysTheorem.lean`, where it is
introduced with the note "The full formalization requires multicolor edge
colorings and lifting lemmas. We axiomatize the result").  Here it is a
**theorem**, discharged from the fully verified `ramseyMulti_exists`. -/
theorem multicolor_ramsey_exists_proved (c k : ℕ) (hc : c ≥ 1) (_hk : k ≥ 1) :
    ∃ n : ℕ, n ≥ 1 ∧ ∀ (color : Fin n → Fin n → Fin c),
      (∀ x y, color x y = color y x) →
      ∃ (clique : Finset (Fin n)) (col : Fin c),
        clique.card ≥ k ∧
          ∀ x y, x ∈ clique → y ∈ clique → x ≠ y → color x y = col := by
  obtain ⟨N, hN⟩ := ramseyMulti_exists c hc (fun _ => k)
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  intro color hsym
  obtain ⟨i, S, hcard, hmono⟩ :=
    ramseyMulti_mono_n (fun _ => k) (Nat.le_succ N) hN color hsym
  exact ⟨S, i, hcard, hmono⟩

/-!
## Part VI: bridge back to `RamseyProp`

The two-colour instance of `RamseyMulti` is exactly `RamseyProp`, so the new
framework is a conservative extension of the gallery's.
-/

/-- Colour code for the bridge: red (`true`) ↦ colour `0` (target `r`),
blue (`false`) ↦ colour `1` (target `s`), matching `![r, s]`. -/
private def b2 (b : Bool) : Fin 2 := if b then 0 else 1

private lemma b2_eq_zero (b : Bool) : b2 b = 0 ↔ b = true := by cases b <;> decide
private lemma b2_eq_one (b : Bool) : b2 b = 1 ↔ b = false := by cases b <;> decide

/-- Colour `0` of a 2-colouring corresponds to `RamseyProp`'s red clique (target
`r`) and colour `1` to the blue clique (target `s`).  Hence `RamseyMulti n 2
![r, s]` and `RamseyProp n r s` are equivalent. -/
theorem ramseyMulti_two_iff_ramseyProp (n r s : ℕ) :
    RamseyMulti n 2 ![r, s] ↔ RamseyProp n r s := by
  constructor
  · -- multicolour ⇒ two-colour
    intro hM f hfsym _
    -- encode: red (`true`) ↦ colour 0, blue (`false`) ↦ colour 1
    let f' : Fin n → Fin n → Fin 2 := fun x y => b2 (f x y)
    have hf'sym : ∀ x y, f' x y = f' y x := by
      intro x y; simp only [f', hfsym]
    obtain ⟨i, S, hS_card, hS_mono⟩ := hM f' hf'sym
    fin_cases i
    · -- colour 0 ⇒ red clique (`f = true`), target `![r,s] 0 = r`
      left
      refine ⟨S, by simpa using hS_card, ?_⟩
      intro x y hx hy hxy
      exact (b2_eq_zero (f x y)).mp (hS_mono x y hx hy hxy)
    · -- colour 1 ⇒ blue clique (`f = false`), target `![r,s] 1 = s`
      right
      refine ⟨S, by simpa using hS_card, ?_⟩
      intro x y hx hy hxy
      exact (b2_eq_one (f x y)).mp (hS_mono x y hx hy hxy)
  · -- two-colour ⇒ multicolour
    intro hR f hfsym
    -- decode: colour 0 ↦ red (`true`), colour 1 ↦ blue (`false`); `false` diagonal
    let g : Fin n → Fin n → Bool :=
      fun x y => if x = y then false else decide ((f x y).val = 0)
    have hgsym : ∀ x y, g x y = g y x := by
      intro x y; simp only [g]
      by_cases h : x = y
      · subst h; rfl
      · rw [if_neg h, if_neg (Ne.symm h), hfsym]
    have hgirr : ∀ x, g x x = false := by intro x; simp [g]
    rcases hR g hgsym hgirr with ⟨S, hS_card, hS_red⟩ | ⟨S, hS_card, hS_blue⟩
    · -- red (`g = true`) ⇒ colour 0, target `![r,s] 0 = r`
      refine ⟨0, S, by simpa using hS_card, ?_⟩
      intro x y hx hy hxy
      have := hS_red x y hx hy hxy
      simp only [g, if_neg hxy, decide_eq_true_eq] at this
      exact Fin.ext (by simpa using this)
    · -- blue (`g = false`) ⇒ colour 1 (the only other `Fin 2` value), target `s`
      refine ⟨1, S, by simpa using hS_card, ?_⟩
      intro x y hx hy hxy
      have := hS_blue x y hx hy hxy
      simp only [g, if_neg hxy, decide_eq_false_iff_not] at this
      -- `(f x y).val ≠ 0` and `f x y : Fin 2` force `f x y = 1`
      have hlt := (f x y).isLt
      exact Fin.ext (by simp only [Fin.val_one]; omega)

end RamseyR4kOQ04
