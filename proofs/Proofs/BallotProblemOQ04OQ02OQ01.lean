/-
# Non-Crossing Partitions are Counted by the Catalan Numbers
## (ballot-problem-oq-04-oq-02-oq-01)

**Open question** (from `ballot-problem-oq-04-oq-02`, the countable Finpartition model):
the sibling entry `ballot-problem-oq-04-oq-02` introduced `nonCrossingCount n`, the number
of non-crossing partitions of `Fin n`, as a well-typed `Fintype.card`, and pinned down its
first divergence from the Bell numbers at `n = 4`. The *exact value* was left open:

> `nonCrossingCount n = catalan n`.

This file supplies the **structural reduction** of that counting statement to a single
combinatorial recurrence, and discharges everything except that recurrence.

## The reduction

Mathlib's Catalan numbers satisfy the convolution recurrence
(`Mathlib.Combinatorics.Enumerative.Catalan`):
* `catalan 0 = 1`;
* `catalan (n+1) = ∑ (i,j) ∈ antidiagonal n, catalan i * catalan j`  (`catalan_succ'`).

So `nonCrossingCount = catalan` follows by strong induction the moment we know
`nonCrossingCount` obeys the *same* two laws:

* **Base** (`nonCrossingCount_zero`): there is a unique partition of the empty set, and it
  is (vacuously) non-crossing, so `nonCrossingCount 0 = 1`. **Proved here, 0 sorry.**

* **Recurrence** (`nonCrossingCount_recurrence`):
  `nonCrossingCount (n+1) = ∑ (i,j) ∈ antidiagonal n, nonCrossingCount i * nonCrossingCount j`.
  This is the genuine combinatorial content — the classical Catalan decomposition of a
  non-crossing partition of `{0,…,n}` according to the block structure around a distinguished
  point. It is split here into its *counting* and *combinatorial* halves (see below): the
  counting half is proved, and the combinatorial half — a first-return **bijection** — is the
  sole remaining `sorry`. The decomposition is **not** in Mathlib in any form.

Given the base case and recurrence, `nonCrossingCount_eq_catalan` is a four-line strong
induction matching the `antidiagonal` shape of `catalan_succ'`. The point of this file is that
it isolates the *entire* difficulty of `nonCrossing = Catalan` into one explicit bijection: a
reduction in the spirit of "one structural theorem in place of an explicit bijection".

## Status

**Sorry count**: 0. The conjecture `nonCrossingCount n = catalan n` is now **fully proved**
(`nonCrossingCount_eq_catalan`). The first-return bijection `nonempty_firstReturnEquiv` — the
formerly-open combinatorial heart — is discharged by an equinumerosity count
(`card_lhs_eq_card_rhs`): the two sides of the decomposition are shown to have equal cardinality
via antisymmetry of two explicit injections (`fwdMid` / `glMid`), and `Fintype.equivOfCardEq`
then supplies the (noncomputable) bijection. This sidesteps the dependent-`HEq` casts a *natural*
equiv would require by routing through the `Fin (n+1)`-indexed intermediate type `MidNc`, whose
window fibers match `glueFp`'s signature definitionally.

**Axiom count**: 0 literal `axiom` declarations and 0 structure-encoded assumptions. The proof
uses only the foundational `propext`/`Classical.choice`/`Quot.sound` (`Classical.choice` via
`Fintype.equivOfCardEq` and `.some` on the bijection's `Nonempty`) — no `sorryAx`, no
`Lean.ofReduceBool` (the `n ≤ 3` corollary uses kernel `decide`, not `native_decide`). The
gallery status of this entry is therefore `verified`.
-/

import Mathlib
import Proofs.BallotProblemOQ04
import Proofs.BallotProblemOQ04OQ02

open Finset
open scoped BigOperators

namespace BallotProblemOQ04OQ02OQ01

open BallotProblemOQ04OQ02 (IsNonCrossingFp nonCrossingCount nonCrossingCount_eq_card_of_n_le_three)

/-! ## The base case `n = 0` -/

/-- **Base case.** There is exactly one partition of the empty set `Fin 0`, and (with no four
indices to cross) it is non-crossing, so `nonCrossingCount 0 = 1 = catalan 0`. -/
theorem nonCrossingCount_zero : nonCrossingCount 0 = 1 := by
  rw [nonCrossingCount_eq_card_of_n_le_three (n := 0) (by norm_num)]
  have hbot : (univ : Finset (Fin 0)) = ⊥ := by
    rw [Finset.univ_eq_empty, Finset.bot_eq_empty]
  simp only [hbot]
  exact Fintype.card_unique

/-! ## First-return infrastructure: restriction of non-crossing partitions

The outstanding bijection `nonempty_firstReturnEquiv` decomposes a non-crossing partition of
`Fin (n+1)` into the induced partitions on the two sub-intervals cut out by a distinguished
block. Building those induced partitions is where the earlier survey estimated "several hundred
lines" of manual `Finpartition` construction (providing `SupIndep`, `sup_parts`, `not_bot`
by hand). This section removes that obstacle with a short, reusable construction:

* the *same-part* relation of any `Finpartition (univ : Finset (Fin n))` is exactly
  `Setoid.ker P.part` (relation `P.part a = P.part b`), by `mem_part_iff_part_eq_part`;
* pulling it back along an index embedding `emb : Fin i → Fin (n+1)` (`Setoid.comap`) and
  re-materialising it with `Finpartition.ofSetoid` yields the restricted partition `restrictFp`
  **without any manual partition-axiom proof** — `ofSetoid` supplies them;
* and restriction *preserves* non-crossing whenever `emb` is strictly monotone
  (`isNonCrossingFp_restrictFp`): a crossing in the restriction lifts, through the
  order-embedding, to a crossing in `P`.

This is the forward (restriction) half of the first-return decomposition, proved with `0`
`sorry`; the remaining work for the bijection is the gluing (inverse) map and the mutual-inverse
laws (see the entry's research notes). -/

/-- The *same-part* relation of `P`, pulled back along an index map `emb`, as a `Setoid`.
Its relation is `P.part (emb a) = P.part (emb b)` (`Setoid.ker P.part` is the same-part relation
by `Finpartition.mem_part_iff_part_eq_part`). -/
def restrictSetoid {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (P : Finpartition (univ : Finset (Fin (n + 1)))) : Setoid (Fin i) :=
  Setoid.comap emb (Setoid.ker P.part)

instance instDecidableRestrictRel {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (P : Finpartition (univ : Finset (Fin (n + 1)))) :
    DecidableRel (restrictSetoid emb P).r :=
  fun a b => (inferInstance : Decidable (P.part (emb a) = P.part (emb b)))

/-- **Restriction of a finpartition along an index embedding.** The finpartition of `Fin i`
whose blocks are the `emb`-preimages of the blocks of `P`. Built via `Finpartition.ofSetoid`, so
the partition axioms come for free. -/
def restrictFp {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (P : Finpartition (univ : Finset (Fin (n + 1)))) :
    Finpartition (univ : Finset (Fin i)) :=
  Finpartition.ofSetoid (restrictSetoid emb P)

/-- Membership in a block of the restriction is same-block-under-`emb` in `P`. -/
@[simp] theorem mem_part_restrictFp {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (P : Finpartition (univ : Finset (Fin (n + 1)))) (a b : Fin i) :
    b ∈ (restrictFp emb P).part a ↔ P.part (emb a) = P.part (emb b) :=
  Finpartition.mem_part_ofSetoid_iff_rel

/-- **Restriction preserves non-crossing (forward half of the first-return decomposition).**
If `emb : Fin i → Fin (n+1)` is strictly monotone (an order-embedding of an index interval) and
`P` is non-crossing, then the restricted partition `restrictFp emb P` is non-crossing. A crossing
`a < b < c < d` in the restriction maps, through the order-embedding, to a crossing
`emb a < emb b < emb c < emb d` in `P`; the same-block hypotheses transport along `emb`, so
non-crossing of `P` forces `emb a, emb b` into a common block, i.e. `a, b` into a common block of
the restriction. -/
theorem isNonCrossingFp_restrictFp {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (hmono : StrictMono emb) (P : Finpartition (univ : Finset (Fin (n + 1))))
    (hP : IsNonCrossingFp P) : IsNonCrossingFp (restrictFp emb P) := by
  intro a b c d hab hbc hcd hca hdb
  rw [mem_part_restrictFp] at hca hdb ⊢
  have Hca : emb c ∈ P.part (emb a) := by rw [hca]; exact P.mem_part (mem_univ _)
  have Hdb : emb d ∈ P.part (emb b) := by rw [hdb]; exact P.mem_part (mem_univ _)
  have hb_in_a : emb b ∈ P.part (emb a) :=
    hP (emb a) (emb b) (emb c) (emb d) (hmono hab) (hmono hbc) (hmono hcd) Hca Hdb
  exact ((P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).mp hb_in_a).symm

/-! ### Concrete interval embeddings for the first-return split

The first-return decomposition restricts a non-crossing partition of `Fin (n+1)` to the two
sub-intervals cut out by the distinguished block. The abstract restriction lemma
`isNonCrossingFp_restrictFp` needs a strictly monotone index embedding; the two embeddings the
split actually uses are the *initial segment* `[0, i)` and an *offset window* `k + [0, j)`. Both
are order-embeddings of an index interval, so restriction along them preserves non-crossing —
unconditionally, for every choice of endpoints. These corollaries package that fact in the exact
form the forward map consumes, isolating the remaining combinatorial content to *which* intervals
the cut selects (not whether the restrictions are non-crossing). -/

/-- The initial-segment embedding `Fin i → Fin (n+1)` (`Fin.castLE`) is strictly monotone. -/
theorem strictMono_castLE {i n : ℕ} (h : i ≤ n + 1) : StrictMono (Fin.castLE h) :=
  fun _ _ hab => hab

/-- **Restriction to an initial segment preserves non-crossing.** Restricting a non-crossing
partition of `Fin (n+1)` to the initial interval `[0, i)` (via `Fin.castLE`) is non-crossing. -/
theorem isNonCrossingFp_restrictFp_castLE {i n : ℕ} (h : i ≤ n + 1)
    (P : Finpartition (univ : Finset (Fin (n + 1)))) (hP : IsNonCrossingFp P) :
    IsNonCrossingFp (restrictFp (Fin.castLE h) P) :=
  isNonCrossingFp_restrictFp _ (strictMono_castLE h) P hP

/-- The offset-window embedding `Fin j → Fin (n+1)`, `x ↦ k + x`, placing an index interval of
length `j` starting at position `k`. -/
def offsetEmb {j n : ℕ} (k : ℕ) (h : k + j ≤ n + 1) (x : Fin j) : Fin (n + 1) :=
  ⟨k + x.val, by have := x.isLt; omega⟩

/-- The offset-window embedding is strictly monotone. -/
theorem strictMono_offsetEmb {j n : ℕ} (k : ℕ) (h : k + j ≤ n + 1) :
    StrictMono (offsetEmb (n := n) k h) := by
  intro a b hab
  have hab' : a.val < b.val := hab
  show k + a.val < k + b.val
  omega

/-- **Restriction to an offset window preserves non-crossing.** Restricting a non-crossing
partition of `Fin (n+1)` to the window `k + [0, j)` (via `offsetEmb`) is non-crossing. -/
theorem isNonCrossingFp_restrictFp_offset {j n : ℕ} (k : ℕ) (h : k + j ≤ n + 1)
    (P : Finpartition (univ : Finset (Fin (n + 1)))) (hP : IsNonCrossingFp P) :
    IsNonCrossingFp (restrictFp (offsetEmb k h) P) :=
  isNonCrossingFp_restrictFp _ (strictMono_offsetEmb k h) P hP

/-! ### The forward map of the first-return bijection

With the restriction infrastructure in place, the **forward** direction of
`nonempty_firstReturnEquiv` is now concrete, and the previously-open "which interval does the cut
select" question is settled. The **cut index** is `firstBlockMax P := max (block containing 0)`:
the largest element sharing a block with `0`.

This is the *correct binary* cut. Decomposing the block of `0` into its successive gaps gives the
wrong, multi-part ("composition") recurrence; the single number `m = max (block 0)` gives the
Catalan convolution, because non-crossing forces every block to lie entirely within `[1, m]` or
entirely within `[m+1, n]` — a block with points on both sides of `m` would, together with the
pair `0, m` of the distinguished block, form a crossing `0 < b < m < d`. Hence `P` restricts
*independently* to the two offset windows `[1, m]` (length `m`) and `[m+1, n]` (length `n - m`),
with `(m, n - m) ∈ antidiagonal n`; both restrictions are non-crossing by
`isNonCrossingFp_restrictFp_offset`. Small-case check: at `n = 1` the cut `m ∈ {0,1}` separates
the two partitions of `{0,1}`; at `n = 2` the three values of `m` distribute the five partitions
of `{0,1,2}` as `1 + 2 + 2` over `(m, n-m) = (0,2), (1,1), (2,0)`, matching
`NC 0·NC 2 + NC 1·NC 1 + NC 2·NC 0 = 5`.

The remaining open content is the *inverse* (gluing) map and the two mutual-inverse laws; the
forward map `firstReturnForward` and its target indices are pinned down here (0 `sorry`). -/

/-- The distinguished **cut index** of the first-return decomposition: the largest element in the
block containing `0`. Non-crossing forces every block to sit entirely on one side of it. -/
def firstBlockMax {n : ℕ} (P : Finpartition (univ : Finset (Fin (n + 1)))) : Fin (n + 1) :=
  (P.part 0).max' ⟨0, P.mem_part (mem_univ 0)⟩

/-- The cut index shares a block with `0`. -/
theorem firstBlockMax_mem_part {n : ℕ} (P : Finpartition (univ : Finset (Fin (n + 1)))) :
    firstBlockMax P ∈ P.part 0 :=
  (P.part 0).max'_mem _

/-- The cut index and its complement form an `antidiagonal n` pair, so the two restricted
intervals have exactly the sizes the recurrence's `Σ` ranges over. -/
theorem firstBlockMax_mem_antidiagonal {n : ℕ}
    (P : Finpartition (univ : Finset (Fin (n + 1)))) :
    ((firstBlockMax P).val, n - (firstBlockMax P).val) ∈ antidiagonal n := by
  rw [mem_antidiagonal]
  have h : (firstBlockMax P).val ≤ n := Nat.lt_succ_iff.mp (firstBlockMax P).isLt
  omega

/-- **No block straddles the cut (separation lemma, 0 `sorry`).** For a non-crossing partition
`P`, no block contains a point `a` at-or-below the cut `m = firstBlockMax P` together with a point
`c` strictly above it. This is the structural fact that makes the first-return decomposition a
*binary* (Catalan) split rather than a multi-part one: every block lies entirely in `[0, m]` or
entirely in `[m+1, n]`, so `P` restricts independently to the two windows.

Proof: were `c ∈ P.part a` with `a ≤ m < c`, non-crossing applied to `0 < a < m < c` (using that
`m ∈ P.part 0`, i.e. `0` and the cut share a block) forces `a ∈ P.part 0`; transporting `c` through
`a` then puts `c ∈ P.part 0`, so `c ≤ (P.part 0).max' = m` — contradicting `m < c`. (The boundary
cases `a = 0` and `a = m` land in `P.part 0` immediately.) -/
theorem not_mem_part_across_firstBlockMax {n : ℕ}
    (P : Finpartition (univ : Finset (Fin (n + 1)))) (hP : IsNonCrossingFp P)
    {a c : Fin (n + 1)} (hac : a ≤ firstBlockMax P) (hc : firstBlockMax P < c) :
    c ∉ P.part a := by
  intro hmem
  have h0m : firstBlockMax P ∈ P.part 0 := firstBlockMax_mem_part P
  -- First show `a` shares a block with `0`.
  have ha0 : a ∈ P.part 0 := by
    rcases lt_or_eq_of_le hac with hlt | heq
    · -- `a < m`: split on whether `a = 0`.
      rcases Nat.eq_zero_or_pos a.val with ha0v | hapos
      · have hazero : a = 0 := by apply Fin.ext; rw [Fin.val_zero]; exact ha0v
        rw [hazero]; exact P.mem_part (mem_univ 0)
      · -- `0 < a < m < c`: apply non-crossing to `(0, a, m, c)`.
        have h0a : (0 : Fin (n + 1)) < a := by rw [Fin.lt_def]; simpa using hapos
        exact hP 0 a (firstBlockMax P) c h0a hlt hc h0m hmem
    · rw [heq]; exact h0m
  -- Transport `c` from the block of `a` to the block of `0`.
  have hpart : P.part a = P.part 0 :=
    (P.mem_part_iff_part_eq_part (mem_univ a) (mem_univ 0)).mp ha0
  have hc0 : c ∈ P.part 0 := by rw [← hpart]; exact hmem
  -- Then `c ≤ m`, contradicting `m < c`.
  exact absurd (Finset.le_max' (P.part 0) c hc0) (not_le.mpr hc)

/-- **Forward map of the first-return bijection (0 `sorry`).** A non-crossing partition of
`Fin (n+1)` maps to its cut index `m = firstBlockMax P` (paired with `n - m` in `antidiagonal n`)
together with the two non-crossing restrictions to the offset windows `[1, m]` and `[m+1, n]`.
This realizes the forward half of `nonempty_firstReturnEquiv`; only the inverse (gluing) map and
the mutual-inverse laws remain. -/
def firstReturnForward {n : ℕ}
    (Pnc : {P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P}) :
    Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
      {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
      {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P} :=
  let m := (firstBlockMax Pnc.1).val
  have hm : m ≤ n := Nat.lt_succ_iff.mp (firstBlockMax Pnc.1).isLt
  have hL : 1 + m ≤ n + 1 := by omega
  have hR : (m + 1) + (n - m) ≤ n + 1 := by omega
  ⟨⟨(m, n - m), firstBlockMax_mem_antidiagonal Pnc.1⟩,
    ⟨restrictFp (offsetEmb 1 hL) Pnc.1,
      isNonCrossingFp_restrictFp_offset 1 hL Pnc.1 Pnc.2⟩,
    ⟨restrictFp (offsetEmb (m + 1) hR) Pnc.1,
      isNonCrossingFp_restrictFp_offset (m + 1) hR Pnc.1 Pnc.2⟩⟩

/-- **No block straddles the cut (the structural heart of the split).** Let `m` be the *maximum*
of the block containing `0` (`hm0 : m ∈ P.part 0`, `hmax : m` dominates that block). Then in a
non-crossing partition `P` of `Fin (n+1)`, no block contains points on *both* sides of `m`: there
are no two points `x, y` of one block with `x ≤ m < y`.

This is exactly what makes `m = firstBlockMax P` the *correct* binary cut, and what a future
gluing (inverse) map consumes for injectivity: every block lies entirely in the window `[0, m]`
or entirely in `[m+1, n]`, so restricting `P` to the two offset windows loses no block and the
pieces recombine uniquely. Stated for an abstract max element `m` (rather than `firstBlockMax P`
directly) so the proof is a pure order/partition argument, free of `Finset.max'` unfolding.

Proof: if the straddling block is `0`'s block, then `y ≤ m` (maximality) contradicts `m < y`.
Otherwise `0 < x < m < y` with `m ∈ P.part 0` and `y ∈ P.part x`, so non-crossing forces
`x ∈ P.part 0` — but then `0` and `x` share a block, contradicting that this block is not
`0`'s. -/
theorem noStraddle_of_isMax {n : ℕ} (P : Finpartition (univ : Finset (Fin (n + 1))))
    (hP : IsNonCrossingFp P) (m : Fin (n + 1)) (hm0 : m ∈ P.part 0)
    (hmax : ∀ z ∈ P.part 0, z ≤ m) (a x y : Fin (n + 1))
    (hx : x ∈ P.part a) (hy : y ∈ P.part a) (hxm : x ≤ m) (hmy : m < y) : False := by
  by_cases hcase : (0 : Fin (n + 1)) ∈ P.part a
  · -- `a`'s block is `0`'s block: `y ∈ P.part 0`, so `y ≤ m`, contradicting `m < y`.
    have h0a : P.part a = P.part 0 :=
      ((P.mem_part_iff_part_eq_part (mem_univ 0) (mem_univ a)).mp hcase).symm
    have hy0 : y ∈ P.part 0 := h0a ▸ hy
    exact absurd (hmax y hy0) (not_le.mpr hmy)
  · -- `0 ∉ P.part a`: build the crossing `0 < x < m < y`.
    have hpartx : P.part a = P.part x :=
      ((P.mem_part_iff_part_eq_part (mem_univ x) (mem_univ a)).mp hx).symm
    -- `0 ∉ P.part x` (else `0 ∈ P.part a`).
    have zeroNotX : (0 : Fin (n + 1)) ∉ P.part x := by
      intro h0x
      have hx0eq : P.part x = P.part 0 :=
        ((P.mem_part_iff_part_eq_part (mem_univ 0) (mem_univ x)).mp h0x).symm
      exact hcase (by rw [hpartx, hx0eq]; exact P.mem_part (mem_univ 0))
    have hxne : x ≠ 0 := fun hh => hcase (hh ▸ hx)
    -- `x ≠ m`: else `x = m ∈ P.part 0`, forcing `0 ∈ P.part x`.
    have hxnem : x ≠ m := by
      intro hh
      have hxm0 : x ∈ P.part 0 := hh ▸ hm0
      have heq : P.part 0 = P.part x :=
        ((P.mem_part_iff_part_eq_part (mem_univ x) (mem_univ 0)).mp hxm0).symm
      exact zeroNotX (heq ▸ P.mem_part (mem_univ 0))
    have hyx : y ∈ P.part x := hpartx ▸ hy
    have hlt1 : (0 : Fin (n + 1)) < x := Fin.pos_iff_ne_zero.mpr hxne
    have hlt2 : x < m := lt_of_le_of_ne hxm hxnem
    have hcross : x ∈ P.part 0 := hP 0 x m y hlt1 hlt2 hmy hm0 hyx
    have hx0eq : P.part 0 = P.part x :=
      ((P.mem_part_iff_part_eq_part (mem_univ x) (mem_univ 0)).mp hcross).symm
    exact zeroNotX (hx0eq ▸ P.mem_part (mem_univ 0))

/-- **No block straddles `firstBlockMax P`.** The concrete instance of `noStraddle_of_isMax` at
the cut index `m = firstBlockMax P`: its maximality over the block of `0` is `Finset.le_max'`. -/
theorem noStraddle {n : ℕ} (P : Finpartition (univ : Finset (Fin (n + 1))))
    (hP : IsNonCrossingFp P) (a x y : Fin (n + 1))
    (hx : x ∈ P.part a) (hy : y ∈ P.part a)
    (hxm : x ≤ firstBlockMax P) (hmy : firstBlockMax P < y) : False :=
  noStraddle_of_isMax P hP (firstBlockMax P) (firstBlockMax_mem_part P)
    (fun z hz => Finset.le_max' _ z hz) a x y hx hy hxm hmy

/-- **Every block lies entirely on one side of the cut.** A direct corollary of `noStraddle`:
for a non-crossing partition `P`, each block `P.part a` is contained either entirely in the lower
window `[0, m]` or entirely in the upper window `[m+1, n]` (`m = firstBlockMax P`). This is the
clean structural form the inverse (gluing) map consumes: since no block straddles `m`, restricting
`P` to the two offset windows `[1, m]` and `[m+1, n]` drops no block, so the two pieces recombine
uniquely into `P`. Proof: if some point of the block exceeds `m` then, by `noStraddle`, no point can
be `≤ m` (else that pair would straddle), giving the right disjunct; otherwise every point is `≤ m`,
the left disjunct. -/
theorem part_side_of_firstBlockMax {n : ℕ} (P : Finpartition (univ : Finset (Fin (n + 1))))
    (hP : IsNonCrossingFp P) (a : Fin (n + 1)) :
    (∀ x ∈ P.part a, x ≤ firstBlockMax P) ∨ (∀ x ∈ P.part a, firstBlockMax P < x) := by
  by_cases hex : ∃ y ∈ P.part a, firstBlockMax P < y
  · obtain ⟨y, hy, hmy⟩ := hex
    refine Or.inr fun x hx => ?_
    by_contra hxle
    exact noStraddle P hP a x y hx hy (not_lt.mp hxle) hmy
  · push_neg at hex
    exact Or.inl hex

/-! ### The inverse (gluing) map of the first-return bijection

`firstReturnForward` restricts a non-crossing `P` to the two offset windows `[1, m]` and
`[m+1, n]` (`m = firstBlockMax P`), dropping point `0`. The inverse **glues** an independent
pair `(P₁, P₂)` of non-crossing partitions of `Fin m` and `Fin (n-m)` back into a single
partition of `Fin (n+1)`:

* window `A = [1, m]` carries `P₁` (index `a ↦ a + 1`);
* window `B = [m+1, n]` carries `P₂` (index `b ↦ b + (m+1)`);
* point `0` joins the `P₁`-block containing the top index `m-1` (so `0` and `m` share a block,
  restoring `firstBlockMax = m`); when `m = 0`, point `0` is a fresh singleton.

The gluing is realized as the kernel setoid of a *label* function `glueLabel`, so the partition
axioms come free from `Finpartition.ofSetoid` — no manual `SupIndep`/`sup_parts`/`not_bot`. -/

/-- Block **label** of a point under the gluing of `(P₁, P₂)`: window-`A` points (and `0`, when
`m ≥ 1`) are labelled by their `P₁`-block, window-`B` points by their `P₂`-block, and `0` gets a
fresh label `Sum.inl none` when `m = 0`. Two points share a glued block iff they share a label. -/
def glueLabel {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) (x : Fin (n + 1)) :
    Option (Finset (Fin m)) ⊕ Finset (Fin (n - m)) :=
  if hx0 : x.val = 0 then
    if hm0 : m = 0 then Sum.inl none
    else Sum.inl (some (P₁.part ⟨m - 1, by omega⟩))
  else if hxA : x.val ≤ m then
    Sum.inl (some (P₁.part ⟨x.val - 1, by omega⟩))
  else
    Sum.inr (P₂.part ⟨x.val - (m + 1), by have := x.isLt; omega⟩)

/-- The **glued setoid**: same-label under `glueLabel`. -/
def glueSetoid {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) : Setoid (Fin (n + 1)) :=
  Setoid.ker (glueLabel m hm P₁ P₂)

instance instDecidableGlueRel {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) :
    DecidableRel (glueSetoid m hm P₁ P₂).r :=
  fun a b => (inferInstance :
    Decidable (glueLabel m hm P₁ P₂ a = glueLabel m hm P₁ P₂ b))

/-- **The glued partition** of `Fin (n+1)`, built from an independent pair `(P₁, P₂)` of
partitions of the two windows. The inverse (up to the round-trip laws, still open) of
`firstReturnForward`. -/
def glueFp {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) :
    Finpartition (univ : Finset (Fin (n + 1))) :=
  Finpartition.ofSetoid (glueSetoid m hm P₁ P₂)

/-- Membership in a glued block is same-label under `glueLabel`. -/
@[simp] theorem mem_part_glueFp {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) (a b : Fin (n + 1)) :
    b ∈ (glueFp m hm P₁ P₂).part a ↔
      glueLabel m hm P₁ P₂ a = glueLabel m hm P₁ P₂ b :=
  Finpartition.mem_part_ofSetoid_iff_rel

/-! ### The left restriction's top block recovers `0`'s block (forward-map side) -/

/-- **The left restriction's top block recovers the block of `0` (0 `sorry`).** Let
`m = firstBlockMax P` be the cut of a non-crossing `P`, assume the left window is nonempty
(`0 < m`), and let `e = offsetEmb 1 : Fin m → Fin (n+1)` place the window `[1, m]`. Writing
`Q = restrictFp e P` for the left restriction and `tm : Fin m` (`tm = m - 1`, so `e tm = m`) for its
top index, an index `t` lies in `Q`'s *top block* `Q.part tm` **iff** `e t` shares `P`'s block with
`0`:  `t ∈ Q.part tm ↔ e t ∈ P.part 0`.

This is the linchpin of the first-return *inverse* (gluing) map's well-definedness and of the
forward map's injectivity. The forward map `firstReturnForward` records only `m` and the two
window restrictions `Q, R`; it drops `0` itself (which lies in *neither* window `[1, m]` nor
`[m+1, n]`), so a priori it forgets *which* points of `[1, m]` share `0`'s block. This lemma shows
that information is **not** lost: those points are exactly the top block `Q.part tm` of the left
restriction (the block whose top index maps to the cut `m`, which shares `P`'s block with `0`).
Hence `0`'s block is reconstructible from `Q` alone — glue `0` onto `Q`'s top block — so two
non-crossing partitions with the same `(m, Q, R)` must coincide. It is the exact forward-side
counterpart of `mem_part_zero_glueFp_left` below (the gluing side): read together they show the
round-trip `glue ∘ forward` restores `0`'s block.

Proof: unfold restriction membership to `P.part (e tm) = P.part (e t)`; since `e tm = m` and
`m ∈ P.part 0` gives `P.part m = P.part 0`, this is `P.part 0 = P.part (e t)`, i.e. `e t ∈ P.part 0`
by `mem_part_iff_part_eq_part`. -/
theorem restrict_top_recovers_part_zero {n : ℕ}
    (P : Finpartition (univ : Finset (Fin (n + 1))))
    (m : ℕ) (hm0 : 0 < m) (hL : 1 + m ≤ n + 1)
    (hmeq : (firstBlockMax P).val = m) (t : Fin m) :
    t ∈ (restrictFp (offsetEmb 1 hL) P).part ⟨m - 1, by omega⟩
      ↔ offsetEmb 1 hL t ∈ P.part 0 := by
  rw [mem_part_restrictFp]
  -- `e tm = firstBlockMax P` because `1 + (m - 1) = m = (firstBlockMax P).val`.
  have he_tm : offsetEmb 1 hL (⟨m - 1, by omega⟩ : Fin m) = firstBlockMax P := by
    apply Fin.ext
    show 1 + (m - 1) = (firstBlockMax P).val
    omega
  rw [he_tm]
  -- `P.part (firstBlockMax P) = P.part 0` since `firstBlockMax P ∈ P.part 0`.
  have hpm0 : P.part (firstBlockMax P) = P.part 0 :=
    (P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ 0)).mp (firstBlockMax_mem_part P)
  rw [hpm0]
  -- Goal: `P.part 0 = P.part (e t) ↔ e t ∈ P.part 0`.
  constructor
  · intro h
    exact (P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ 0)).mpr h.symm
  · intro h
    exact ((P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ 0)).mp h).symm

/-! ### Evaluation lemmas for `glueLabel` (the gluing map's computational API)

`glueLabel` is defined by a three-way `dite` on `x.val` (`= 0` / `≤ m` / `> m`). The round-trip
laws for the first-return bijection reason about it only at the three *canonical* inputs — the
distinguished point `0`, a left-window point `offsetEmb 1 a` (`a : Fin m`), and a right-window
point `offsetEmb (m+1) b` (`b : Fin (n-m)`). These three equations collapse the `dite` at each,
turning `glueLabel` into clean `Sum.inl`/`Sum.inr` values. They play, for `glueFp`, exactly the
role `mem_part_restrictFp` plays for `restrictFp`: the reusable bridge every downstream membership
argument passes through. All three are `0 sorry` and free of `firstBlockMax`/`max'` unfolding. -/

/-- `glueLabel` at the distinguished point `0`, when the left window is nonempty (`0 < m`): the
label is `P₁`'s *top* block `P₁.part ⟨m-1⟩` — i.e. `0` is glued onto that block. -/
theorem glueLabel_zero_of_pos {n : ℕ} (m : ℕ) (hm : m ≤ n) (hm0 : 0 < m)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) :
    glueLabel m hm P₁ P₂ 0 = Sum.inl (some (P₁.part ⟨m - 1, by omega⟩)) := by
  unfold glueLabel
  rw [dif_pos (by rfl), dif_neg (by omega)]

/-- `glueLabel` at a left-window point `offsetEmb 1 a` (`a : Fin m`): the label is `P₁`'s block of
`a`. So the left window carries `P₁` faithfully. -/
theorem glueLabel_offsetEmb_left {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m))))
    (hL : 1 + m ≤ n + 1) (a : Fin m) :
    glueLabel m hm P₁ P₂ (offsetEmb 1 hL a) = Sum.inl (some (P₁.part a)) := by
  have hv : (offsetEmb 1 hL a).val = 1 + a.val := rfl
  have hidx : (offsetEmb 1 hL a).val - 1 = a.val := by rw [hv]; omega
  unfold glueLabel
  rw [dif_neg (by rw [hv]; omega), dif_pos (by rw [hv]; have := a.isLt; omega)]
  congr 1
  exact congrArg (fun i => some (P₁.part i)) (Fin.ext hidx)

/-- `glueLabel` at a right-window point `offsetEmb (m+1) b` (`b : Fin (n-m)`): the label is `P₂`'s
block of `b`. So the right window carries `P₂` faithfully, in a distinct `Sum.inr` sector from the
left window and `0` — the two windows never share a glued block. -/
theorem glueLabel_offsetEmb_right {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m))))
    (hR : (m + 1) + (n - m) ≤ n + 1) (b : Fin (n - m)) :
    glueLabel m hm P₁ P₂ (offsetEmb (m + 1) hR b) = Sum.inr (P₂.part b) := by
  have hv : (offsetEmb (m + 1) hR b).val = (m + 1) + b.val := rfl
  have hidx : (offsetEmb (m + 1) hR b).val - (m + 1) = b.val := by rw [hv]; omega
  unfold glueLabel
  rw [dif_neg (by rw [hv]; omega), dif_neg (by rw [hv]; omega)]
  congr 1
  exact congrArg P₂.part (Fin.ext hidx)

/-- **The glued partition recovers `0`'s block on the left window (glue-side 0-block recovery,
0 `sorry`).** For the gluing of `(P₁, P₂)` with nonempty left window (`0 < m`), a left-window point
`offsetEmb 1 a` shares the glued block of `0` **iff** `a` lies in `P₁`'s top block `P₁.part ⟨m-1⟩`.

This is the exact mirror, on the gluing (inverse) side, of `restrict_top_recovers_part_zero` (which
recovers `0`'s block from the *restriction* of a non-crossing `P`). Read together the two say: the
forward map's left restriction `Q` has top block `Q.part ⟨m-1⟩ = {a : offsetEmb 1 a ∈ P.part 0}`,
and re-gluing attaches `0` to precisely that block. Hence the round-trip `glue ∘ forward` restores
`0`'s block exactly — the step where the forward map's dropping of `0` is undone. Proof: rewrite the
glued membership (`mem_part_glueFp`) with the two evaluation lemmas `glueLabel_zero_of_pos` and
`glueLabel_offsetEmb_left`, reducing (via `Sum`/`Option` injectivity) to `P₁.part ⟨m-1⟩ = P₁.part a`,
i.e. `a ∈ P₁.part ⟨m-1⟩`. -/
theorem mem_part_zero_glueFp_left {n : ℕ} (m : ℕ) (hm : m ≤ n) (hm0 : 0 < m)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m))))
    (hL : 1 + m ≤ n + 1) (a : Fin m) :
    offsetEmb 1 hL a ∈ (glueFp m hm P₁ P₂).part 0
      ↔ a ∈ P₁.part ⟨m - 1, by omega⟩ := by
  rw [mem_part_glueFp, glueLabel_zero_of_pos m hm hm0, glueLabel_offsetEmb_left m hm,
    Sum.inl.injEq, Option.some.injEq]
  constructor
  · intro h
    exact (P₁.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).mpr h.symm
  · intro h
    exact ((P₁.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).mp h).symm

/-! ### The glued partition is non-crossing (injectivity-side structural fact)

The gluing map `glueFp` must land in the *non-crossing* subtype for it to serve as the inverse
of `firstReturnForward`. This section proves exactly that: gluing two non-crossing partitions of
the windows `Fin m` and `Fin (n-m)` yields a non-crossing partition of `Fin (n+1)`.

The proof is a case split by the window a straddle-free block lands in. Since window-`A` points
carry `Sum.inl` labels and window-`B` points carry `Sum.inr` labels, a same-label pair lies in a
single window, and the linear order `a < b < c < d` forces *all four* of a crossing candidate
into one window (`glueLabel_le_iff`). Inside window `B` the labels are literally the shifted `P₂`,
so non-crossing transports directly. Inside window `A` the labels are the shifted `P₁` **with
point `0` attached to the top block `m-1`** — and it is precisely this "attach to the top" choice
that keeps `A` non-crossing: a crossing through `0` would pair `(0, c)` with `(b, d)` at
`0 < b < c < d ≤ m`, and `0 ~ m-1` turns it into the `P₁`-crossing `(b-1, c-1, d-1, m-1)`, whose
resolution forces `0 ~ b`. -/

/-- **Non-crossing in `Finpartition.part`-equality form.** A convenience restatement of
`IsNonCrossingFp` avoiding the membership `↔ part-equality` bookkeeping at every call site: from
`P.part w = P.part y` and `P.part x = P.part z` at `w < x < y < z`, non-crossing yields
`P.part w = P.part x`. -/
theorem ncf_part_eq {k : ℕ} {P : Finpartition (univ : Finset (Fin k))}
    (hP : IsNonCrossingFp P) {w x y z : Fin k} (hwx : w < x) (hxy : x < y) (hyz : y < z)
    (h1 : P.part w = P.part y) (h2 : P.part x = P.part z) : P.part w = P.part x := by
  have hy : y ∈ P.part w := h1.symm ▸ P.mem_part (mem_univ y)
  have hz : z ∈ P.part x := h2.symm ▸ P.mem_part (mem_univ z)
  have hx : x ∈ P.part w := hP w x y z hwx hxy hyz hy hz
  exact ((P.mem_part_iff_part_eq_part (mem_univ x) (mem_univ w)).mp hx).symm

/-- Window-`B` label (`m < x.val`): the `Sum.inr` `P₂`-block of the shifted index. -/
theorem glueLabel_of_gt {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) (x : Fin (n + 1)) (hx : m < x.val) :
    glueLabel m hm P₁ P₂ x = Sum.inr (P₂.part ⟨x.val - (m + 1), by have := x.isLt; omega⟩) := by
  unfold glueLabel
  rw [dif_neg (by omega : x.val ≠ 0), dif_neg (by omega : ¬ x.val ≤ m)]

/-- Window-`A` label, nonzero point (`0 < x.val ≤ m`): the `Sum.inl` `P₁`-block of `x-1`. -/
theorem glueLabel_of_pos_le {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) (x : Fin (n + 1))
    (hx0 : 0 < x.val) (hxm : x.val ≤ m) :
    glueLabel m hm P₁ P₂ x = Sum.inl (some (P₁.part ⟨x.val - 1, by omega⟩)) := by
  unfold glueLabel
  rw [dif_neg (by omega : x.val ≠ 0), dif_pos hxm]

/-- Label of a `0`-valued point with `m ≥ 1`: the `Sum.inl` `P₁`-block of the top index `m-1`
(this "attach `0` to the top block" is what keeps the glued window `A` non-crossing). -/
theorem glueLabel_of_zero {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) (x : Fin (n + 1))
    (hx0 : x.val = 0) (hmpos : 0 < m) :
    glueLabel m hm P₁ P₂ x = Sum.inl (some (P₁.part ⟨m - 1, by omega⟩)) := by
  unfold glueLabel
  rw [dif_pos hx0, dif_neg (by omega : m ≠ 0)]

/-- Any window-`A` point (`x.val ≤ m`) carries a `Sum.inl` label. -/
theorem glueLabel_isLeft_of_le {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) (x : Fin (n + 1)) (hx : x.val ≤ m) :
    (glueLabel m hm P₁ P₂ x).isLeft = true := by
  rcases Nat.eq_zero_or_pos x.val with h0 | hpos
  · unfold glueLabel; rw [dif_pos h0]; split_ifs <;> rfl
  · unfold glueLabel; rw [dif_neg (by omega : x.val ≠ 0), dif_pos hx]; rfl

/-- Two same-label points lie in the same window: a shared `glueLabel` forces the two points to
the same side of the cut `m`. (`Sum.inl` labels are window `A`, `Sum.inr` labels window `B`.) -/
theorem glueLabel_le_iff {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) (x y : Fin (n + 1))
    (h : glueLabel m hm P₁ P₂ x = glueLabel m hm P₁ P₂ y) : x.val ≤ m ↔ y.val ≤ m := by
  constructor
  · intro hx
    by_contra hy; push_neg at hy
    have hxL := glueLabel_isLeft_of_le m hm P₁ P₂ x hx
    rw [h, glueLabel_of_gt m hm P₁ P₂ y hy] at hxL
    simp at hxL
  · intro hy
    by_contra hx; push_neg at hx
    have hyL := glueLabel_isLeft_of_le m hm P₁ P₂ y hy
    rw [← h, glueLabel_of_gt m hm P₁ P₂ x hx] at hyL
    simp at hyL

/-- **The glued partition is non-crossing.** If `P₁` and `P₂` are non-crossing partitions of the
two windows `Fin m` and `Fin (n-m)`, their gluing `glueFp m hm P₁ P₂` is a non-crossing partition
of `Fin (n+1)`. This is the structural fact the inverse (gluing) map needs to land in the
non-crossing subtype `{P // IsNonCrossingFp P}` — half of the still-open bijection
`nonempty_firstReturnEquiv`. -/
theorem isNonCrossingFp_glueFp {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m))))
    (h₁ : IsNonCrossingFp P₁) (h₂ : IsNonCrossingFp P₂) :
    IsNonCrossingFp (glueFp m hm P₁ P₂) := by
  intro a b c d hab hbc hcd hca hdb
  rw [mem_part_glueFp] at hca hdb ⊢
  have vab : a.val < b.val := Fin.lt_def.mp hab
  have vbc : b.val < c.val := Fin.lt_def.mp hbc
  have vcd : c.val < d.val := Fin.lt_def.mp hcd
  by_cases hAm : a.val ≤ m
  · -- Window A: all four points land at value ≤ m.
    have hCm : c.val ≤ m := (glueLabel_le_iff m hm P₁ P₂ a c hca).mp hAm
    have hBm : b.val ≤ m := by omega
    have hDm : d.val ≤ m := (glueLabel_le_iff m hm P₁ P₂ b d hdb).mp hBm
    have hb1 : 1 ≤ b.val := by omega
    have hc1 : 1 ≤ c.val := by omega
    have hd1 : 1 ≤ d.val := by omega
    rcases Nat.eq_zero_or_pos a.val with ha0 | ha1
    · -- a is the special point 0: its label is the top block m-1 (m ≥ 1 since d.val ≥ 3).
      have hm1 : 0 < m := by omega
      rw [glueLabel_of_zero m hm P₁ P₂ a ha0 hm1,
          glueLabel_of_pos_le m hm P₁ P₂ c (by omega) hCm] at hca
      rw [glueLabel_of_pos_le m hm P₁ P₂ b (by omega) hBm,
          glueLabel_of_pos_le m hm P₁ P₂ d (by omega) hDm] at hdb
      rw [glueLabel_of_zero m hm P₁ P₂ a ha0 hm1,
          glueLabel_of_pos_le m hm P₁ P₂ b (by omega) hBm]
      simp only [Sum.inl.injEq, Option.some.injEq] at hca hdb ⊢
      rcases Nat.lt_or_ge d.val m with hdlt | hdge
      · -- d-1 < m-1: the crossing (b-1, c-1, d-1, m-1) resolves in P₁.
        have key : P₁.part (⟨b.val - 1, by omega⟩ : Fin m) = P₁.part ⟨c.val - 1, by omega⟩ :=
          ncf_part_eq h₁ (Fin.mk_lt_mk.mpr (show b.val - 1 < c.val - 1 by omega))
            (Fin.mk_lt_mk.mpr (show c.val - 1 < d.val - 1 by omega))
            (Fin.mk_lt_mk.mpr (show d.val - 1 < m - 1 by omega)) hdb hca.symm
        exact hca.trans key.symm
      · -- d.val = m: d and the special point 0 already share the top block m-1.
        have hdm : d.val = m := le_antisymm hDm hdge
        have efin : (⟨d.val - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
          simp only [Fin.mk.injEq]; omega
        exact ((congrArg P₁.part efin).symm).trans hdb.symm
    · -- a is an ordinary window-A point: the crossing (a-1, b-1, c-1, d-1) resolves in P₁.
      rw [glueLabel_of_pos_le m hm P₁ P₂ a ha1 hAm,
          glueLabel_of_pos_le m hm P₁ P₂ c (by omega) hCm] at hca
      rw [glueLabel_of_pos_le m hm P₁ P₂ b (by omega) hBm,
          glueLabel_of_pos_le m hm P₁ P₂ d (by omega) hDm] at hdb
      rw [glueLabel_of_pos_le m hm P₁ P₂ a ha1 hAm,
          glueLabel_of_pos_le m hm P₁ P₂ b (by omega) hBm]
      simp only [Sum.inl.injEq, Option.some.injEq] at hca hdb ⊢
      exact ncf_part_eq h₁ (Fin.mk_lt_mk.mpr (show a.val - 1 < b.val - 1 by omega))
        (Fin.mk_lt_mk.mpr (show b.val - 1 < c.val - 1 by omega))
        (Fin.mk_lt_mk.mpr (show c.val - 1 < d.val - 1 by omega)) hca hdb
  · -- Window B: all four points land at value > m; labels are the shifted P₂.
    push_neg at hAm
    have hCm : m < c.val := by
      have hiff := glueLabel_le_iff m hm P₁ P₂ a c hca
      by_contra h; push_neg at h
      exact absurd (hiff.mpr (by omega)) (by omega)
    have hBm : m < b.val := by omega
    have hDm : m < d.val := by omega
    rw [glueLabel_of_gt m hm P₁ P₂ a hAm, glueLabel_of_gt m hm P₁ P₂ c hCm] at hca
    rw [glueLabel_of_gt m hm P₁ P₂ b hBm, glueLabel_of_gt m hm P₁ P₂ d hDm] at hdb
    rw [glueLabel_of_gt m hm P₁ P₂ a hAm, glueLabel_of_gt m hm P₁ P₂ b hBm]
    simp only [Sum.inr.injEq] at hca hdb ⊢
    exact ncf_part_eq h₂ (Fin.mk_lt_mk.mpr (show a.val - (m + 1) < b.val - (m + 1) by omega))
      (Fin.mk_lt_mk.mpr (show b.val - (m + 1) < c.val - (m + 1) by omega))
      (Fin.mk_lt_mk.mpr (show c.val - (m + 1) < d.val - (m + 1) by omega)) hca hdb

/-! ### The glued partition recovers the cut index (round-trip linchpin)

`firstReturnForward` cuts a non-crossing `P` at `m = firstBlockMax P`. For the round-trip
`forward ∘ glue = id` (the `right_inv` law), the first thing the forward map must recover from a
glued partition `glueFp m hm P₁ P₂` is that same cut index `m`. `firstBlockMax_glueFp_val` proves
exactly this: the maximum of the block of `0` in the glued partition is again `m`.

Why: the glued block of `0` carries a `Sum.inl` label (`glueLabel_isLeft_of_le` / the `m = 0`
singleton case), and every `Sum.inl`-labelled point lies in the window `[0, m]` (`glueLabel_le_iff`),
so no block-of-`0` point exceeds `m` — giving `≤ m`. Conversely, when `m > 0` the point `m` itself
carries `0`'s label (`0` was glued onto `P₁`'s top block `⟨m-1⟩`, and `m`'s label is that same top
block via `glueLabel_of_pos_le`), so `m` sits in the block and `m ≤ firstBlockMax`. Together the two
force `firstBlockMax (glueFp …) = m`. This pins the forward map's cut, hence its two offset windows
`[1, m]` and `[m+1, n]`, back to the sizes `(m, n-m)` that `glue` consumed — the first step of the
`right_inv` law. -/
theorem firstBlockMax_glueFp_val {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) :
    (firstBlockMax (glueFp m hm P₁ P₂)).val = m := by
  set Q := glueFp m hm P₁ P₂ with hQ
  -- Every point sharing `0`'s glued block sits in the window `[0, m]`.
  have hle : ∀ p ∈ Q.part 0, p.val ≤ m := by
    intro p hp
    have hlabel : glueLabel m hm P₁ P₂ (0 : Fin (n + 1)) = glueLabel m hm P₁ P₂ p :=
      (mem_part_glueFp m hm P₁ P₂ 0 p).mp hp
    exact (glueLabel_le_iff m hm P₁ P₂ 0 p hlabel).mp (by simp)
  refine le_antisymm (hle _ (firstBlockMax_mem_part Q)) ?_
  -- The cut index is `≥ m`: for `m > 0`, the point `m` itself shares `0`'s block.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · omega
  · have hmmem : (⟨m, by omega⟩ : Fin (n + 1)) ∈ Q.part 0 := by
      rw [mem_part_glueFp, glueLabel_zero_of_pos m hm hmpos,
        glueLabel_of_pos_le m hm P₁ P₂ ⟨m, by omega⟩ hmpos (le_refl m)]
    exact Fin.le_def.mp (Finset.le_max' (Q.part 0) ⟨m, by omega⟩ hmmem)

/-! ### Restriction recovers each glued factor (round-trip `right_inv`, factor half)

`firstBlockMax_glueFp_val` recovered the cut index `m` from a glued partition. The forward map
`firstReturnForward` then restricts to the two offset windows `[1, m]` and `[m+1, n]`. For the
round-trip `forward ∘ glue = id` (`right_inv`), those two restrictions must return exactly the
factors `P₁, P₂` that `glue` consumed. `restrictFp_glueFp_left`/`_right` prove precisely that:
restricting the glued partition to each window recovers the corresponding factor *on the nose*.
Together with `firstBlockMax_glueFp_val` they discharge the mathematical content of `right_inv`;
only the `Sigma`/`Subtype` packaging of `firstReturnForward` would then remain. -/

/-- **Finpartition extensionality via the block function.** Two finpartitions of `univ` (over a
`Fintype`) that assign every point the same block are equal. Every part is `P.part a` for some
point `a ∈ t` it contains, so equal block functions give equal `parts` finsets. -/
theorem finpartition_eq_of_part {α : Type*} [Fintype α] [DecidableEq α]
    {P Q : Finpartition (univ : Finset α)} (h : ∀ a, P.part a = Q.part a) : P = Q := by
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha⟩ : t.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr fun he => P.empty_notMem_parts (he ▸ ht)
    have hta : P.part a = t := P.part_eq_of_mem ht ha
    rw [← hta, h a]
    exact Q.part_mem.2 (mem_univ a)
  · intro ht
    obtain ⟨a, ha⟩ : t.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr fun he => Q.empty_notMem_parts (he ▸ ht)
    have hta : Q.part a = t := Q.part_eq_of_mem ht ha
    rw [← hta, ← h a]
    exact P.part_mem.2 (mem_univ a)

/-- Two points share a glued block iff they carry the same `glueLabel` — in `part`-equality form
(the companion of `mem_part_glueFp`, phrased for the block *function* rather than membership). -/
theorem part_glueFp_eq_iff {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) (x y : Fin (n + 1)) :
    (glueFp m hm P₁ P₂).part x = (glueFp m hm P₁ P₂).part y ↔
      glueLabel m hm P₁ P₂ x = glueLabel m hm P₁ P₂ y := by
  rw [eq_comm, ← (glueFp m hm P₁ P₂).mem_part_iff_part_eq_part (mem_univ y) (mem_univ x),
      mem_part_glueFp]

/-- **Left restriction recovers `P₁` (round-trip `right_inv`, left factor).** Restricting the glued
partition `glueFp m hm P₁ P₂` to the left offset window `[1, m]` returns `P₁` exactly. The window
`[1, m]` carries the shifted `P₁` labels verbatim (`glueLabel_offsetEmb_left`), so its induced block
structure *is* `P₁`; point `0` (attached to `P₁`'s top block) lies outside the window and is
dropped, leaving `P₁` untouched. -/
theorem restrictFp_glueFp_left {n : ℕ} (m : ℕ) (hm : m ≤ n) (hL : 1 + m ≤ n + 1)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) :
    restrictFp (offsetEmb 1 hL) (glueFp m hm P₁ P₂) = P₁ := by
  refine finpartition_eq_of_part fun a => Finset.ext fun b => ?_
  rw [mem_part_restrictFp, part_glueFp_eq_iff,
      glueLabel_offsetEmb_left m hm P₁ P₂ hL a, glueLabel_offsetEmb_left m hm P₁ P₂ hL b,
      Sum.inl.injEq, Option.some.injEq, eq_comm]
  exact (P₁.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)).symm

/-- **Right restriction recovers `P₂` (round-trip `right_inv`, right factor).** Restricting the
glued partition `glueFp m hm P₁ P₂` to the right offset window `[m+1, n]` returns `P₂` exactly: the
window carries the shifted `P₂` labels verbatim (`glueLabel_offsetEmb_right`), so its induced block
structure is `P₂`. -/
theorem restrictFp_glueFp_right {n : ℕ} (m : ℕ) (hm : m ≤ n) (hR : (m + 1) + (n - m) ≤ n + 1)
    (P₁ : Finpartition (univ : Finset (Fin m)))
    (P₂ : Finpartition (univ : Finset (Fin (n - m)))) :
    restrictFp (offsetEmb (m + 1) hR) (glueFp m hm P₁ P₂) = P₂ := by
  refine finpartition_eq_of_part fun a => Finset.ext fun b => ?_
  rw [mem_part_restrictFp, part_glueFp_eq_iff,
      glueLabel_offsetEmb_right m hm P₁ P₂ hR a, glueLabel_offsetEmb_right m hm P₁ P₂ hR b,
      Sum.inr.injEq, eq_comm]
  exact (P₂.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)).symm

/-! ### Gluing the forward restrictions recovers `P` (round-trip `left_inv`, the core)

`restrictFp_glueFp_left`/`_right` and `firstBlockMax_glueFp_val` discharge the *other* round-trip
(`forward ∘ glue = id`). The law below is the harder direction — `glue ∘ forward = id` — and the
one where non-crossing is essential. It says: cutting a non-crossing `P` at `m = firstBlockMax P`,
restricting to the two windows, and gluing the pieces back reconstructs `P` exactly. -/

/-- **Gluing the forward restrictions recovers `P` (round-trip `left_inv`, the core).** For a
non-crossing `P` of `Fin (n+1)` with cut `m = firstBlockMax P`, gluing the two window restrictions
`restrictFp (offsetEmb 1) P` (on `[1, m]`) and `restrictFp (offsetEmb (m+1)) P` (on `[m+1, n]`)
reconstructs `P` on the nose: `glueFp m hm (restrictFp e₁ P) (restrictFp e₂ P) = P`.

This is the substantive round-trip law `glue ∘ forward = id` (the `left_inv` of
`nonempty_firstReturnEquiv`), and the hard direction — it is where non-crossing is used. Two points
share a glued block iff they carry the same `glueLabel`; the proof shows that is equivalent to
sharing `P`'s block, by three cases on the cut `m`:
* both in the closed lower window `[0, m]` — labels are `Sum.inl` of the shifted `P₁ = restrict`
  block, which tracks `P` on `[1, m]`; and point `0` is glued onto the top block `⟨m-1⟩`, whose
  members are exactly `0`'s `P`-block (`firstBlockMax` shares `P`'s block with `0`), so the label
  tracks `P.part 0` too;
* both in the upper window `[m+1, n]` — labels are `Sum.inr` of the shifted `P₂ = restrict` block,
  tracking `P` verbatim;
* opposite sides (`a ≤ m < b`) — the labels live in distinct `Sum` sectors, so differ, and
  `P.part a = P.part b` is impossible: it would straddle the cut (`noStraddle`).
Combined with `restrictFp_glueFp_left`/`_right` and `firstBlockMax_glueFp_val` (the `right_inv`
ingredients), only the `Sigma`/`Subtype` packaging remains to assemble the still-open
`nonempty_firstReturnEquiv`. -/
theorem glueFp_restrictFp_eq_self {n : ℕ}
    (P : Finpartition (univ : Finset (Fin (n + 1)))) (hP : IsNonCrossingFp P)
    (hm : (firstBlockMax P).val ≤ n)
    (hL : 1 + (firstBlockMax P).val ≤ n + 1)
    (hR : ((firstBlockMax P).val + 1) + (n - (firstBlockMax P).val) ≤ n + 1) :
    glueFp (firstBlockMax P).val hm
      (restrictFp (offsetEmb 1 hL) P)
      (restrictFp (offsetEmb ((firstBlockMax P).val + 1) hR) P) = P := by
  set m := (firstBlockMax P).val with hm_def
  set Q₁ := restrictFp (offsetEmb 1 hL) P with hQ₁def
  set Q₂ := restrictFp (offsetEmb (m + 1) hR) P with hQ₂def
  -- Lower-window label evaluation: for `x ≤ m` (`m > 0`), the glued label is `Sum.inl (some ·)`
  -- of a `Q₁`-block whose lifted `P`-block is `P.part x` (`0` lifts to the cut, sharing `0`'s block).
  have hlabL : ∀ x : Fin (n + 1), x.val ≤ m → 0 < m →
      ∃ j : Fin m, glueLabel m hm Q₁ Q₂ x = Sum.inl (some (Q₁.part j))
        ∧ P.part (offsetEmb 1 hL j) = P.part x := by
    intro x hx hmpos
    rcases Nat.eq_zero_or_pos x.val with hx0 | hxpos
    · refine ⟨⟨m - 1, by omega⟩, glueLabel_of_zero m hm Q₁ Q₂ x hx0 hmpos, ?_⟩
      have hemb : offsetEmb 1 hL (⟨m - 1, by omega⟩ : Fin m) = firstBlockMax P := by
        have hv : (offsetEmb 1 hL (⟨m - 1, by omega⟩ : Fin m)).val = 1 + (m - 1) := rfl
        apply Fin.ext; rw [hv]; omega
      have hx0' : x = 0 := Fin.ext hx0
      rw [hemb, hx0']
      exact (P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ 0)).mp (firstBlockMax_mem_part P)
    · refine ⟨⟨x.val - 1, by omega⟩, glueLabel_of_pos_le m hm Q₁ Q₂ x hxpos hx, ?_⟩
      have hv : (offsetEmb 1 hL (⟨x.val - 1, by omega⟩ : Fin m)).val = 1 + (x.val - 1) := rfl
      have hemb : offsetEmb 1 hL (⟨x.val - 1, by omega⟩ : Fin m) = x := by
        apply Fin.ext; rw [hv]; omega
      rw [hemb]
  -- Upper-window label evaluation: for `x > m`, the glued label is `Sum.inr ·` of a `Q₂`-block
  -- whose lifted `P`-block is `P.part x`.
  have hlabR : ∀ x : Fin (n + 1), m < x.val →
      ∃ k : Fin (n - m), glueLabel m hm Q₁ Q₂ x = Sum.inr (Q₂.part k)
        ∧ P.part (offsetEmb (m + 1) hR k) = P.part x := by
    intro x hx
    refine ⟨⟨x.val - (m + 1), by have := x.isLt; omega⟩, glueLabel_of_gt m hm Q₁ Q₂ x hx, ?_⟩
    have hv : (offsetEmb (m + 1) hR (⟨x.val - (m + 1), by have := x.isLt; omega⟩ : Fin (n - m))).val
        = (m + 1) + (x.val - (m + 1)) := rfl
    have hemb : offsetEmb (m + 1) hR (⟨x.val - (m + 1), by have := x.isLt; omega⟩ : Fin (n - m))
        = x := by
      apply Fin.ext; rw [hv]; omega
    rw [hemb]
  -- Same-side (lower window) label equality ⟺ same `P`-block.
  have keyL : ∀ a b : Fin (n + 1), a.val ≤ m → b.val ≤ m →
      (glueLabel m hm Q₁ Q₂ a = glueLabel m hm Q₁ Q₂ b ↔ P.part a = P.part b) := by
    intro a b ha hb
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hab : a = b := Fin.ext (by omega)
      subst hab; simp
    · obtain ⟨ja, hlaba, hPa⟩ := hlabL a ha hmpos
      obtain ⟨jb, hlabb, hPb⟩ := hlabL b hb hmpos
      rw [hlaba, hlabb, Sum.inl.injEq, Option.some.injEq]
      have hmem : (jb ∈ Q₁.part ja) ↔
          (P.part (offsetEmb 1 hL ja) = P.part (offsetEmb 1 hL jb)) := by
        rw [hQ₁def]; exact mem_part_restrictFp (offsetEmb 1 hL) P ja jb
      constructor
      · intro h
        have hin : jb ∈ Q₁.part ja :=
          (Q₁.mem_part_iff_part_eq_part (mem_univ jb) (mem_univ ja)).mpr h.symm
        rw [hmem, hPa, hPb] at hin; exact hin
      · intro h
        have hin : jb ∈ Q₁.part ja := by rw [hmem, hPa, hPb]; exact h
        exact ((Q₁.mem_part_iff_part_eq_part (mem_univ jb) (mem_univ ja)).mp hin).symm
  -- Same-side (upper window) label equality ⟺ same `P`-block.
  have keyR : ∀ a b : Fin (n + 1), m < a.val → m < b.val →
      (glueLabel m hm Q₁ Q₂ a = glueLabel m hm Q₁ Q₂ b ↔ P.part a = P.part b) := by
    intro a b ha hb
    obtain ⟨ka, hlaba, hPa⟩ := hlabR a ha
    obtain ⟨kb, hlabb, hPb⟩ := hlabR b hb
    rw [hlaba, hlabb, Sum.inr.injEq]
    have hmem : (kb ∈ Q₂.part ka) ↔
        (P.part (offsetEmb (m + 1) hR ka) = P.part (offsetEmb (m + 1) hR kb)) := by
      rw [hQ₂def]; exact mem_part_restrictFp (offsetEmb (m + 1) hR) P ka kb
    constructor
    · intro h
      have hin : kb ∈ Q₂.part ka :=
        (Q₂.mem_part_iff_part_eq_part (mem_univ kb) (mem_univ ka)).mpr h.symm
      rw [hmem, hPa, hPb] at hin; exact hin
    · intro h
      have hin : kb ∈ Q₂.part ka := by rw [hmem, hPa, hPb]; exact h
      exact ((Q₂.mem_part_iff_part_eq_part (mem_univ kb) (mem_univ ka)).mp hin).symm
  -- Opposite sides: labels differ (distinct `Sum` sectors) AND a shared `P`-block would straddle.
  have keyCross : ∀ a b : Fin (n + 1), a.val ≤ m → m < b.val →
      (glueLabel m hm Q₁ Q₂ a = glueLabel m hm Q₁ Q₂ b ↔ P.part a = P.part b) := by
    intro a b ha hb
    have haleft : (glueLabel m hm Q₁ Q₂ a).isLeft = true := glueLabel_isLeft_of_le m hm Q₁ Q₂ a ha
    constructor
    · intro h
      rw [h, glueLabel_of_gt m hm Q₁ Q₂ b hb] at haleft
      simp at haleft
    · intro h
      have hb_in : b ∈ P.part a := by rw [h]; exact P.mem_part (mem_univ b)
      exact (noStraddle P hP a a b (P.mem_part (mem_univ a)) hb_in
        (Fin.le_def.mpr (by omega)) (Fin.lt_def.mpr (by omega))).elim
  -- Assemble: for every pair, glued-block ⟺ `P`-block.
  refine finpartition_eq_of_part fun a => Finset.ext fun b => ?_
  rw [mem_part_glueFp]
  have hkey : glueLabel m hm Q₁ Q₂ a = glueLabel m hm Q₁ Q₂ b ↔ P.part a = P.part b := by
    by_cases hAa : a.val ≤ m
    · by_cases hBb : b.val ≤ m
      · exact keyL a b hAa hBb
      · push_neg at hBb; exact keyCross a b hAa hBb
    · push_neg at hAa
      by_cases hBb : b.val ≤ m
      · constructor
        · intro h; exact ((keyCross b a hBb hAa).mp h.symm).symm
        · intro h; exact ((keyCross b a hBb hAa).mpr h.symm).symm
      · push_neg at hBb; exact keyR a b hAa hBb
  rw [hkey, P.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)]
  exact eq_comm

/-! ### Assembling the first-return bijection via a cardinality count

The round-trip laws above (`glueFp_restrictFp_eq_self`, `restrictFp_glueFp_left`/`_right`,
`firstBlockMax_glueFp_val`) are now packaged into the existence of `nonempty_firstReturnEquiv`.

Rather than fight the dependent-`HEq` casts a *natural* `Equiv` between the antidiagonal-indexed
`Σ`-type and the non-crossing partitions would demand — the forward map's cut index equals the
target index only *propositionally*, so matching the two dependent fibers needs transport — we route
through an intermediate type `MidNc n` indexed by `m : Fin (n+1)`, whose right fiber `Fin (n - m)`
matches `glueFp`'s argument type **definitionally**. Gluing then needs no cast, both round-trips are
clean, and `card (LhsNc) = card (MidNc)` follows by antisymmetry of two injections
(`fwdMid` with left inverse `glMid`; `glMid` injective by recovering the cut and both factors).
A pure `antidiagonal ↔ range` reindexing gives `card (MidNc) = card (Rhs)`, and
`Fintype.equivOfCardEq` finally produces the (noncomputable) bijection — no cast bookkeeping. -/

/-- Non-crossing partitions of `Fin k`, as a subtype (the fibers of the first-return split). -/
abbrev NcFp (k : ℕ) := {P : Finpartition (univ : Finset (Fin k)) // IsNonCrossingFp P}

/-- The intermediate `Fin (n+1)`-indexed home of the first-return split: a cut index `m` together
with non-crossing partitions of the two windows `Fin m` and `Fin (n - m)`. Its right fiber matches
`glueFp`'s argument type definitionally, so gluing needs no cast. -/
abbrev MidNc (n : ℕ) := Σ m : Fin (n + 1), NcFp m.val × NcFp (n - m.val)

/-- Forward map into the intermediate type: cut a non-crossing `P` at `m = firstBlockMax P` and
restrict to the two offset windows `[1, m]` and `[m+1, n]`. -/
def fwdMid {n : ℕ} (P : NcFp (n + 1)) : MidNc n :=
  let m := firstBlockMax P.1
  have hm : m.val ≤ n := Nat.lt_succ_iff.mp m.isLt
  have hL : 1 + m.val ≤ n + 1 := by omega
  have hR : (m.val + 1) + (n - m.val) ≤ n + 1 := by omega
  ⟨m,
    ⟨restrictFp (offsetEmb 1 hL) P.1, isNonCrossingFp_restrictFp_offset 1 hL P.1 P.2⟩,
    ⟨restrictFp (offsetEmb (m.val + 1) hR) P.1,
      isNonCrossingFp_restrictFp_offset (m.val + 1) hR P.1 P.2⟩⟩

/-- Inverse (gluing) map from the intermediate type: glue the two windows back at the cut. -/
def glMid {n : ℕ} (x : MidNc n) : NcFp (n + 1) :=
  ⟨glueFp x.1.val (Nat.lt_succ_iff.mp x.1.isLt) x.2.1.1 x.2.2.1,
    isNonCrossingFp_glueFp x.1.val (Nat.lt_succ_iff.mp x.1.isLt) x.2.1.1 x.2.2.1 x.2.1.2 x.2.2.2⟩

/-- `glMid ∘ fwdMid = id`: gluing the two window restrictions recovers `P` (the `left_inv` core,
`glueFp_restrictFp_eq_self`). -/
theorem glMid_fwdMid {n : ℕ} (P : NcFp (n + 1)) : glMid (fwdMid P) = P := by
  apply Subtype.ext
  exact glueFp_restrictFp_eq_self P.1 P.2 _ _ _

/-- The forward map is injective (it has a left inverse). -/
theorem fwdMid_injective {n : ℕ} : Function.Injective (fwdMid (n := n)) :=
  Function.LeftInverse.injective glMid_fwdMid

/-- The gluing map is injective: from `glMid x = glMid x'` the cut index is recovered by
`firstBlockMax_glueFp_val` (an `ℕ`-level equality, so no `HEq`), and after substituting it the two
factors are recovered by `restrictFp_glueFp_left`/`_right`. -/
theorem glMid_injective {n : ℕ} : Function.Injective (glMid (n := n)) := by
  rintro ⟨m, ⟨P₁, h₁⟩, ⟨P₂, h₂⟩⟩ ⟨m', ⟨P₁', h₁'⟩, ⟨P₂', h₂'⟩⟩ hEq
  have hg : glueFp m.val (Nat.lt_succ_iff.mp m.isLt) P₁ P₂
      = glueFp m'.val (Nat.lt_succ_iff.mp m'.isLt) P₁' P₂' := congrArg Subtype.val hEq
  have hmm : m.val = m'.val := by
    have e1 := firstBlockMax_glueFp_val m.val (Nat.lt_succ_iff.mp m.isLt) P₁ P₂
    have e2 := firstBlockMax_glueFp_val m'.val (Nat.lt_succ_iff.mp m'.isLt) P₁' P₂'
    rw [hg] at e1
    exact e1.symm.trans e2
  have hm_eq : m = m' := Fin.ext hmm
  subst hm_eq
  have hL : 1 + m.val ≤ n + 1 := by omega
  have hR : (m.val + 1) + (n - m.val) ≤ n + 1 := by omega
  have hP₁ : P₁ = P₁' :=
    (restrictFp_glueFp_left m.val (Nat.lt_succ_iff.mp m.isLt) hL P₁ P₂).symm.trans
      (by rw [hg]; exact restrictFp_glueFp_left m.val (Nat.lt_succ_iff.mp m.isLt) hL P₁' P₂')
  have hP₂ : P₂ = P₂' :=
    (restrictFp_glueFp_right m.val (Nat.lt_succ_iff.mp m.isLt) hR P₁ P₂).symm.trans
      (by rw [hg]; exact restrictFp_glueFp_right m.val (Nat.lt_succ_iff.mp m.isLt) hR P₁' P₂')
  subst hP₁; subst hP₂; rfl

/-- `card (MidNc n)` as an explicit convolution sum over `range (n+1)`. -/
theorem card_midNc_eq (n : ℕ) :
    Fintype.card (MidNc n)
      = ∑ k ∈ Finset.range (n + 1),
          Fintype.card {P : Finpartition (univ : Finset (Fin k)) // IsNonCrossingFp P}
        * Fintype.card {P : Finpartition (univ : Finset (Fin (n - k))) // IsNonCrossingFp P} := by
  show Fintype.card (Σ m : Fin (n + 1),
      {P : Finpartition (univ : Finset (Fin m.val)) // IsNonCrossingFp P} ×
      {P : Finpartition (univ : Finset (Fin (n - m.val))) // IsNonCrossingFp P}) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => Fintype.card {P : Finpartition (univ : Finset (Fin k)) // IsNonCrossingFp P}
            * Fintype.card {P : Finpartition (univ : Finset (Fin (n - k))) // IsNonCrossingFp P})
    (n + 1)]

/-- `card` of the antidiagonal-indexed `Σ`-type as the same convolution sum over `range (n+1)`. -/
theorem card_rhs_eq (n : ℕ) :
    Fintype.card (Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
        {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
        {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P})
      = ∑ k ∈ Finset.range (n + 1),
          Fintype.card {P : Finpartition (univ : Finset (Fin k)) // IsNonCrossingFp P}
        * Fintype.card {P : Finpartition (univ : Finset (Fin (n - k))) // IsNonCrossingFp P} := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod]
  rw [Finset.sum_coe_sort (antidiagonal n)
    (fun ij => Fintype.card {P : Finpartition (univ : Finset (Fin ij.1)) // IsNonCrossingFp P}
             * Fintype.card {P : Finpartition (univ : Finset (Fin ij.2)) // IsNonCrossingFp P})]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij => Fintype.card {P : Finpartition (univ : Finset (Fin ij.1)) // IsNonCrossingFp P}
             * Fintype.card {P : Finpartition (univ : Finset (Fin ij.2)) // IsNonCrossingFp P}) n]

/-- **The two sides of the first-return decomposition are equinumerous.** The non-crossing
partitions of `Fin (n+1)` and the antidiagonal-indexed pairs of non-crossing partitions of the two
windows have equal cardinality. Proved by `card LhsNc = card MidNc` (antisymmetry of the two
injections `fwdMid`/`glMid`) composed with `card MidNc = card Rhs` (the `antidiagonal ↔ range`
reindexing). -/
theorem card_lhs_eq_card_rhs (n : ℕ) :
    Fintype.card {P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P}
      = Fintype.card (Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
          {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
          {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P}) := by
  have hmid : Fintype.card {P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P}
      = Fintype.card (MidNc n) :=
    le_antisymm (Fintype.card_le_of_injective fwdMid fwdMid_injective)
                (Fintype.card_le_of_injective glMid glMid_injective)
  rw [hmid, card_midNc_eq, ← card_rhs_eq]

/-! ## The combinatorial recurrence (HARD)

The recurrence is now split into two parts that separate its *counting* content from its
*combinatorial* content:

* `nonempty_firstReturnEquiv` — the genuine, still-open obligation: the existence of a
  first-return bijection that decomposes a non-crossing partition of `Fin (n+1)` into a pair of
  independent non-crossing partitions of sizes `(i, j) ∈ antidiagonal n`. This is the entire
  combinatorial heart and the **sole outstanding `sorry`**.
* `nonCrossingCount_recurrence_of_equiv` — the counting half, **proved here (0 `sorry`)**: any
  such bijection already forces the Catalan convolution, by a pure cardinality computation
  (`Fintype.card_congr` ∘ `card_sigma` ∘ `card_prod`).

`nonCrossingCount_recurrence` is then a corollary of the two. -/

/-- **First-return bijection (now proved).** A non-crossing partition of the linearly ordered set
`Fin (n+1)` decomposes — via the classical "first return" of the block structure around a
distinguished point — into an independent pair of non-crossing partitions of an `i`-element and a
`j`-element interval, with `(i, j)` ranging over `antidiagonal n`. We record the decomposition as
a bijection (existence suffices for the count).

This is the genuine combinatorial content of `nonCrossing = Catalan`; the analogous decomposition
is *not* available in Mathlib in any form (Mathlib has no theory of non-crossing partitions, nor of
restricting a `Finpartition` of `Fin (n+1)` to the gaps cut out by a distinguished block). It is
discharged here by `card_lhs_eq_card_rhs` (the two sides are equinumerous, by antisymmetry of the
two injections `fwdMid`/`glMid`) fed to `Fintype.equivOfCardEq` — the existence of the bijection
without the dependent-`HEq` cast bookkeeping a natural equiv would demand. -/
theorem nonempty_firstReturnEquiv (n : ℕ) :
    Nonempty ({P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P} ≃
      Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
        {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
        {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P}) :=
  ⟨Fintype.equivOfCardEq (card_lhs_eq_card_rhs n)⟩

/-- **Counting half of the recurrence (proved, 0 `sorry`).** Any first-return bijection
splitting the non-crossing partitions of `Fin (n+1)` over `antidiagonal n` already forces the
Catalan convolution: it is a pure cardinality computation. This isolates the counting content
of `nonCrossingCount_recurrence` from its combinatorial content (`nonempty_firstReturnEquiv`),
and is the reusable bridge a future construction of the bijection plugs into. -/
theorem nonCrossingCount_recurrence_of_equiv (n : ℕ)
    (e : {P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P} ≃
      Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
        {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
        {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P}) :
    nonCrossingCount (n + 1)
      = ∑ ij ∈ antidiagonal n, nonCrossingCount ij.1 * nonCrossingCount ij.2 := by
  unfold nonCrossingCount
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_prod]
  exact Finset.sum_coe_sort (antidiagonal n)
    (fun ij => Fintype.card {P : Finpartition (univ : Finset (Fin ij.1)) // IsNonCrossingFp P} *
               Fintype.card {P : Finpartition (univ : Finset (Fin ij.2)) // IsNonCrossingFp P})

/-- **Catalan recurrence for non-crossing partitions.** The non-crossing partitions of
`Fin (n+1)` split into pairs of independent non-crossing partitions whose sizes `(i, j)` run
over `antidiagonal n`:
`nonCrossingCount (n+1) = ∑ (i,j) ∈ antidiagonal n, nonCrossingCount i * nonCrossingCount j`.

This is the same convolution that defines `catalan` (`catalan_succ'`). It is now a corollary of
the (still open) first-return bijection `nonempty_firstReturnEquiv` and the (proved) counting
reduction `nonCrossingCount_recurrence_of_equiv`. -/
theorem nonCrossingCount_recurrence (n : ℕ) :
    nonCrossingCount (n + 1)
      = ∑ ij ∈ antidiagonal n, nonCrossingCount ij.1 * nonCrossingCount ij.2 :=
  nonCrossingCount_recurrence_of_equiv n (nonempty_firstReturnEquiv n).some

/-! ## The counting theorem -/

/-- **Non-crossing partitions are counted by the Catalan numbers.**
`nonCrossingCount n = catalan n` for every `n`. Strong induction: the base case is
`nonCrossingCount_zero`, and the step matches `nonCrossingCount_recurrence` against
`catalan_succ'` term-by-term over `antidiagonal n`, rewriting each factor by the inductive
hypothesis (both indices in an `antidiagonal n` pair are `< n+1`). -/
theorem nonCrossingCount_eq_catalan (n : ℕ) : nonCrossingCount n = catalan n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using nonCrossingCount_zero
    | m + 1 =>
      rw [nonCrossingCount_recurrence, catalan_succ']
      refine Finset.sum_congr rfl ?_
      intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      have h1 : ij.1 < m + 1 := by omega
      have h2 : ij.2 < m + 1 := by omega
      rw [ih ij.1 h1, ih ij.2 h2]

/-! ## Unconditional verification for `n ≤ 3` (independent of the open bijection)

`nonCrossingCount_eq_catalan` above is proved *modulo* the still-open first-return bijection
`nonempty_firstReturnEquiv`. The following corollary discharges the conjecture
`nonCrossingCount n = catalan n` **unconditionally** for every `n ≤ 3` — i.e. without
assuming that bijection at all. For `n ≤ 3` every partition of `Fin n` is non-crossing
(`nonCrossingCount_eq_card_of_n_le_three`), so the count is literally the Bell number
`Fintype.card (Finpartition (Fin n))`, evaluated by kernel `decide`; and the Bell and Catalan
numbers agree exactly up to `n = 3`. This is the regime *just before* the first divergence
isolated by `nonCrossingCount_four_lt` (`Bell 4 = 15 > 14 = catalan 4`), so together they pin
the conjecture on both sides of its first nontrivial test. -/
set_option maxRecDepth 8000 in
theorem nonCrossingCount_eq_catalan_of_le_three {n : ℕ} (hn : n ≤ 3) :
    nonCrossingCount n = catalan n := by
  interval_cases n
  · rw [nonCrossingCount_zero, catalan_zero]
  · rw [nonCrossingCount_eq_card_of_n_le_three (by norm_num),
        show catalan 1 = 1 by simp [catalan_succ']]
    decide
  · rw [nonCrossingCount_eq_card_of_n_le_three (by norm_num),
        show catalan 2 = 2 by
          simp [catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
                Finset.sum_range_succ, catalan_zero]]
    decide
  · rw [nonCrossingCount_eq_card_of_n_le_three (by norm_num),
        show catalan 3 = 5 by
          simp [catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
                Finset.sum_range_succ, catalan_zero]]
    decide

#check @nonCrossingCount_zero
#check @not_mem_part_across_firstBlockMax
#check @part_side_of_firstBlockMax
#check @restrict_top_recovers_part_zero
#check @glueLabel_zero_of_pos
#check @glueLabel_offsetEmb_left
#check @glueLabel_offsetEmb_right
#check @mem_part_zero_glueFp_left
#check @firstBlockMax_glueFp_val
#check @restrictFp_glueFp_left
#check @restrictFp_glueFp_right
#check @card_lhs_eq_card_rhs
#check @nonCrossingCount_eq_catalan
#check @nonCrossingCount_eq_catalan_of_le_three

-- Axiom audit: the full theorem depends only on the foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms nonCrossingCount_eq_catalan

end BallotProblemOQ04OQ02OQ01
