/-
  Erdős Problem #1011, Open Question 03: Computing f_5(n)

  Source: https://erdosproblems.com/1011
  Status: OPEN (this file proves only structural, unconditional facts)

  Context:
  Let f_r(n) be the minimal number of edges forcing a triangle in an n-vertex
  graph of chromatic number ≥ r (see `Proofs.Erdos1011Problem` for the full
  framework). The exact value is known only for small r:

    • f_2(n) = ⌊n²/4⌋    + 1                  (Turán)
    • f_3(n) = ⌊(n-1)²/4⌋ + 2                  (Erdős–Gallai 1962)
    • f_4(n) = ⌊(n-3)²/4⌋ + 6   (n ≥ 150)      (Ren–Wang–Wang–Yang 2024)

  The next case, **f_5(n)**, is open. This file does NOT compute it. Instead it
  establishes the unconditional scaffolding any solution must respect, with no
  new axioms:

  1. `f_antitone_in_chromatic` — `f` is antitone in the chromatic parameter:
     requiring a *higher* chromatic number is a stronger hypothesis, so it can
     only *lower* the edge threshold that forces a triangle. Hence
     `f_five_le_f_four : f 5 n ≤ f 4 n` — the open value f_5(n) is bounded above
     by the now-known f_4(n).

  1b. `forces_iff_f_le` — a complete characterization of the threshold:
     `Forces r n m ↔ f r n ≤ m`. The forcing predicate is an up-set in the edge
     bound (`forces_mono`), so `f r n` is exactly its least element.

  1c. `f_eq_zero_of_lt` — the left boundary of the table: once `r` exceeds the
     vertex count `n`, no `n`-vertex graph attains `χ ≥ r` (every such graph is
     `n`-colourable, `chromaticNumber_le_card`), so the forcing condition is
     vacuous and `f r n = 0`. The antitone-in-`r` value has bottomed out.

  2. The **vertex-shift pattern**. The shifts in the formulas above are
     0, 1, 3 for r = 2, 3, 4 — exactly C(r-1, 2). The pattern predicts a shift
     of C(4,2) = 6 for r = 5, i.e. a conjectured leading term ⌊(n-6)²/4⌋.
     `chromaticShift` packages this; `chromaticShift_known` certifies the match
     and the r = 5 prediction; `chromaticShift_mono` records monotonicity.

  3. `f5Conjecture` / `shiftConjecture` — the open statements, recorded as Props.

  Honesty note: the only mathematically new theorem here is the antitonicity of
  f and its corollary; everything else is bookkeeping that organizes the known
  data and the conjecture. f_5(n) itself remains open.

  Tags: graph-theory, chromatic-number, triangles, turan-type, open-problem
-/

import Mathlib
import Proofs.Erdos1011Problem

open Finset GraphCore
open SimpleGraph hiding chromaticNumber

/-
## The defining property of the threshold f_r(n)

`Forces r n m` is the membership predicate of the set whose infimum is
`f r n`: every n-vertex graph with chromatic number ≥ r and at least m edges
contains a triangle. We factor it out so we can reason about `f` through two
clean facts (`f_mem`, `f_le_of_forces`).
-/

/-- The predicate defining membership in the set `{m | … }` whose `sInf` is
    `f r n`. -/
def Forces (r n m : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V = n →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      hasChromatic G r → edgeCount G ≥ m → HasTriangle G

/-- The defining set of `f r n` is nonempty: once `m` exceeds the maximum
    possible number of edges `C(n,2)`, the hypothesis `edgeCount G ≥ m` is
    unsatisfiable, so the implication holds vacuously. -/
theorem forces_nonempty (n r : ℕ) : {m | Forces r n m}.Nonempty := by
  refine ⟨n.choose 2 + 1, ?_⟩
  intro V instF instD hcard G instA _ hedge
  exfalso
  have hb : edgeCount G ≤ n.choose 2 := by
    have h := G.card_edgeFinset_le_card_choose_two
    rw [hcard] at h
    exact h
  omega

/-- `f r n` itself satisfies the forcing property (the infimum is attained,
    since the defining set is nonempty). -/
theorem f_forces (n r : ℕ) : Forces r n (f r n) := by
  unfold f
  exact Nat.sInf_mem (forces_nonempty n r)

/-- Any `m` with the forcing property bounds `f r n` from above. -/
theorem f_le_of_forces {n r m : ℕ} (hm : Forces r n m) : f r n ≤ m := by
  unfold f
  exact Nat.sInf_le hm

/-- The forcing predicate is monotone (an up-set) in the edge bound: if `m`
    edges force a triangle, so does any larger bound `m'`, because the
    hypothesis `edgeCount G ≥ m'` is stronger than `edgeCount G ≥ m`. -/
theorem forces_mono {r n m m' : ℕ} (hm : Forces r n m) (hmm : m ≤ m') :
    Forces r n m' := by
  intro V instF instD hcard G instA hchrom hedge
  exact hm V hcard G hchrom (le_trans hmm hedge)

/-- **Complete characterization of the threshold.** `m` forces a triangle iff
    `m` is at least the threshold `f r n`. The forward direction is
    `f_le_of_forces`; the reverse uses that `f r n` itself forces (`f_forces`)
    together with up-set monotonicity (`forces_mono`). This pins down `f r n`
    as exactly the least `m` in the up-set `{m | Forces r n m}`. -/
theorem forces_iff_f_le {r n m : ℕ} : Forces r n m ↔ f r n ≤ m :=
  ⟨f_le_of_forces, fun h => forces_mono (f_forces n r) h⟩

/-
## Main structural theorem: antitonicity in the chromatic parameter

Requiring a higher chromatic number is a strictly stronger hypothesis on the
graph, so the edge threshold that forces a triangle can only decrease.
-/

/-- **`f` is antitone in `r`.** If `r ≤ r'` then `f r' n ≤ f r n`: demanding a
    larger chromatic number makes the triangle-forcing implication easier to
    satisfy, lowering the threshold. Proof: the defining set for `r` is contained
    in that for `r'` (the hypothesis `χ ≥ r` is implied by `χ ≥ r'`), and `sInf`
    reverses inclusion. -/
theorem f_antitone_in_chromatic {n r r' : ℕ} (h : r ≤ r') :
    f r' n ≤ f r n := by
  apply f_le_of_forces
  intro V instF instD hcard G instA hchrom hedge
  have hchrom' : hasChromatic G r := le_trans h hchrom
  exact f_forces n r V hcard G hchrom' hedge

/-- **Corollary.** The open value `f_5(n)` is bounded above by the (now known)
    `f_4(n)`. Combined with `f_4(n) = ⌊(n-3)²/4⌋ + 6` for `n ≥ 150`
    (Ren–Wang–Wang–Yang 2024) this gives an unconditional upper bound on f_5. -/
theorem f_five_le_f_four (n : ℕ) : f 5 n ≤ f 4 n :=
  f_antitone_in_chromatic (by norm_num)

/-- The full antitone chain on the known/target cases. -/
theorem f_chain (n : ℕ) : f 5 n ≤ f 4 n ∧ f 4 n ≤ f 3 n ∧ f 3 n ≤ f 2 n :=
  ⟨f_antitone_in_chromatic (by norm_num),
   f_antitone_in_chromatic (by norm_num),
   f_antitone_in_chromatic (by norm_num)⟩

/-
## The degenerate regime: r > n forces the threshold to 0

A graph on `n` vertices can be properly coloured with `n` colours (the identity
colouring `V ≃ Fin n` is proper), so `χ(G) ≤ n`. Hence once `r > n` the
hypothesis `χ(G) ≥ r` is unsatisfiable and the forcing implication holds
vacuously for *every* edge bound — including `m = 0`. So `f r n = 0` there.
This is the exact left boundary of the table: the antitone-in-`r` value
`f r n` has already bottomed out at 0 by the time `r` exceeds the vertex count.
-/

/-- Any `n`-vertex graph is `n`-colourable, hence `χ(G) ≤ n`. The identity
    bijection `V ≃ Fin (card V)` is a proper colouring because adjacent vertices
    are distinct and the bijection is injective. -/
theorem chromaticNumber_le_card {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) : chromaticNumber G ≤ Fintype.card W :=
  Nat.sInf_le ⟨Fintype.equivFin W, fun _ _ hadj heq =>
    G.ne_of_adj hadj ((Fintype.equivFin W).injective heq)⟩

/-- **Boundary value.** If the required chromatic number exceeds the vertex
    count (`n < r`) then `f r n = 0`: no `n`-vertex graph attains `χ ≥ r`, so the
    forcing condition is vacuous at every edge bound. -/
theorem f_eq_zero_of_lt {r n : ℕ} (h : n < r) : f r n = 0 := by
  refine Nat.le_antisymm (f_le_of_forces ?_) (Nat.zero_le _)
  intro V instF instD hcard G instA hchrom _
  exfalso
  unfold hasChromatic at hchrom
  have hle : chromaticNumber G ≤ n := hcard ▸ chromaticNumber_le_card G
  omega

/-
## The vertex-shift pattern

The known formulas use `⌊(n - s)²/4⌋` with s = 0, 1, 3 for r = 2, 3, 4.
These are exactly `C(r-1, 2) = (r-1)(r-2)/2`, predicting s = 6 for r = 5.
-/

/-- Conjectured vertex shift inside `f_r`: `s(r) = C(r-1, 2) = (r-1)(r-2)/2`. -/
def chromaticShift (r : ℕ) : ℕ := (r - 1).choose 2

/-- `chromaticShift` reproduces the three known shifts (0, 1, 3) and predicts
    the shift 6 for the open case r = 5. -/
theorem chromaticShift_known :
    chromaticShift 2 = 0 ∧ chromaticShift 3 = 1 ∧
    chromaticShift 4 = 3 ∧ chromaticShift 5 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Closed form: `chromaticShift r = (r-1)(r-2)/2`. -/
theorem chromaticShift_eq (r : ℕ) : chromaticShift r = (r - 1) * (r - 2) / 2 := by
  unfold chromaticShift
  rw [Nat.choose_two_right]
  have h : (r - 1) - 1 = r - 2 := by omega
  rw [h]

/-- The shift is monotone in `r`. -/
theorem chromaticShift_mono : Monotone chromaticShift := by
  intro a b hab
  unfold chromaticShift
  exact Nat.choose_le_choose 2 (by omega)

/-
## The open statements

Recorded as Props; neither is proved here.
-/

/-- The shift conjecture for general `r`: `f_r(n) = ⌊(n - C(r-1,2))²/4⌋ + c_r`
    for some constant `c_r` and all large `n`. True for r = 2, 3, 4
    (with c = 1, 2, 6). -/
def shiftConjecture : Prop :=
  ∀ r ≥ 2, ∃ c n₀ : ℕ, ∀ n ≥ n₀, f r n = (n - chromaticShift r) ^ 2 / 4 + c

/-- The concrete open question of this entry: the conjectured closed form for
    `f_5(n)`, namely `⌊(n - 6)²/4⌋ + c` for some constant `c` and all large `n`. -/
def f5Conjecture : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀, f 5 n = (n - chromaticShift 5) ^ 2 / 4 + c

/-- The shift conjecture (general r) specializes to the f_5 conjecture. -/
theorem shiftConjecture_imp_f5 (h : shiftConjecture) : f5Conjecture := by
  obtain ⟨c, n₀, hc⟩ := h 5 (by norm_num)
  exact ⟨c, n₀, hc⟩

#check f_antitone_in_chromatic
#check f_five_le_f_four
#check forces_iff_f_le
#check f_eq_zero_of_lt
#check chromaticShift_known
#print axioms f_antitone_in_chromatic
#print axioms forces_iff_f_le
#print axioms f_eq_zero_of_lt
#print axioms chromaticShift_known
