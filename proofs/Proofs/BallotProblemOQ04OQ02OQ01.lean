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

**Sorry count**: 1 (`nonempty_firstReturnEquiv` — the first-return bijection). The numeric
recurrence `nonCrossingCount_recurrence` and its counting reduction
`nonCrossingCount_recurrence_of_equiv` are now **proved (0 `sorry`)**; the open content is
exactly the existence of the bijection, with all cardinality arithmetic discharged.

**Axiom count**: 0 literal `axiom` declarations; the proved results use only the foundational
`propext`/`Classical.choice`/`Quot.sound` (the latter via `.some` on the bijection's
`Nonempty`). Because a `sorry` remains, the gallery status of this entry is `formalized`, not
`verified`.

The outstanding bijection is the natural target for proof search: it is *known* mathematics
(the non-crossing-partition Catalan decomposition) requiring a delicate but standard
construction, exactly the regime where automated formalization is appropriate.
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

/-- **First-return bijection (the sole open obligation).** A non-crossing partition of the
linearly ordered set `Fin (n+1)` decomposes — via the classical "first return" of the block
structure around a distinguished point — into an independent pair of non-crossing partitions of
an `i`-element and a `j`-element interval, with `(i, j)` ranging over `antidiagonal n`. We
record the decomposition as a bijection (existence suffices for the count).

This is the genuine combinatorial content of `nonCrossing = Catalan`; the analogous
decomposition is *not* available in Mathlib in any form (Mathlib has no theory of non-crossing
partitions, nor of restricting a `Finpartition` of `Fin (n+1)` to the gaps cut out by a
distinguished block). **Outstanding `sorry`** (HARD, bijection-level). -/
theorem nonempty_firstReturnEquiv (n : ℕ) :
    Nonempty ({P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P} ≃
      Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
        {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
        {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P}) := by
  sorry

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
#check @nonCrossingCount_eq_catalan
#check @nonCrossingCount_eq_catalan_of_le_three

end BallotProblemOQ04OQ02OQ01
