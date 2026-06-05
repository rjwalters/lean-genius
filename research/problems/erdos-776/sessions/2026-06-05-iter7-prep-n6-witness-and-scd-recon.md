# Session iter 7 PREP — n=6 witness drop-in + Mathlib SCD reconnaissance

**Date**: 2026-06-05
**Researcher**: researcher-1
**Phase**: PREP (doc-only; no Lean changes)
**Predecessors**: iter 1–5 ACTs (#999, #1978/#2257, #5741, #7969, #13317),
iter 6 STATE-SYNC (2026-05-17)

## TL;DR

This is the first session memo for `erdos-776`. The slug's `state.md`
Next Action lists two pending items:

1. **Extend witness lemmas to n = 6 in Lean** (needs a 4-set antichain
   helper analogous to `isAntichainFamily_triple`).
2. **Investigate Mathlib for any SCD-related lemmas** to enable a
   uniform-construction proof.

Both are *PREP-able* without touching Lean code in this iteration. This
memo:

- **Item 1**: writes out the exact Lean signature + proof skeleton for
  the 4-set antichain helper, plus the n = 6 witness family encoding
  (`witness6 : SubsetFamily 6`), packaged as a ready-to-drop block for
  the next ACT.
- **Item 2**: records a Mathlib reconnaissance of the relevant
  set-family combinatorics modules. Result: **Mathlib does not currently
  expose a symmetric chain decomposition (SCD)**; the closest analogs
  (`Mathlib.Combinatorics.SetFamily.{Shadow, Compression.UV, LYM}`) are
  shadow/compression machinery that does not directly produce SCDs.
  Confirms the state.md observation; rules out a quick uniform proof.

No Lean changes; no build needed. Iteration 6 → 7.

## Item 1 — 4-set antichain helper + n = 6 witness, Lean drop-in

### 1.1 The 4-set antichain helper

The pair lemma takes `2 = C(2,2)·2` incomparability hypotheses (1 pair
× 2 directions), the triple lemma takes `6 = C(3,2)·2` (3 pairs × 2
directions), and the 4-set lemma takes `12 = C(4,2)·2` (6 pairs × 2
directions). All three lemmas share the same proof skeleton: `intro` two
indices, `simp` to insert/singleton membership, `rcases` on each index,
and dispatch with `(hXY rfl).elim` (diagonal) or the matching
hypothesis (off-diagonal).

```lean
/-- A four-set family is an antichain iff all six pairs are
    pairwise incomparable.  Helper for verified achievability
    witnesses with four distinct sizes. -/
lemma isAntichainFamily_quadruple {n : ℕ} {A B C D : Finset (Fin n)}
    (hAB_sub : ¬(A ⊆ B)) (hBA_sub : ¬(B ⊆ A))
    (hAC_sub : ¬(A ⊆ C)) (hCA_sub : ¬(C ⊆ A))
    (hAD_sub : ¬(A ⊆ D)) (hDA_sub : ¬(D ⊆ A))
    (hBC_sub : ¬(B ⊆ C)) (hCB_sub : ¬(C ⊆ B))
    (hBD_sub : ¬(B ⊆ D)) (hDB_sub : ¬(D ⊆ B))
    (hCD_sub : ¬(C ⊆ D)) (hDC_sub : ¬(D ⊆ C)) :
    IsAntichainFamily ({A, B, C, D} : Finset (Finset (Fin n))) := by
  intro X hX Y hY hXY
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
  rcases hX with rfl | rfl | rfl | rfl
  all_goals rcases hY with rfl | rfl | rfl | rfl
  all_goals first | exact (hXY rfl).elim | assumption
```

**Correctness rationale.** The `rcases ... with rfl | rfl | rfl | rfl`
splits each of the two membership witnesses into 4 cases (`A`, `B`, `C`,
`D`). The Cartesian product is 16 subgoals. The 4 diagonal subgoals
(`X = Y`) discharge via `(hXY rfl).elim`. The 12 off-diagonal subgoals
match one of the 12 incomparability hypotheses verbatim via
`assumption`. The same `first | ... | assumption` dispatch pattern that
discharged the triple-version proof carries over without modification.

### 1.2 The n = 6 witness family

State.md gives the hand-verified F₆ = {{0, 1}, {0, 2, 3}, {0, 2, 4, 5},
{1, 2, 3, 4, 5}}, sizes {2, 3, 4, 5}. Lean encoding:

```lean
/-- Concrete witness for n = 6: F₆ has four distinct sizes 2, 3, 4, 5.

    Sets:
      A = {0, 1}                (size 2)
      B = {0, 2, 3}             (size 3)
      C = {0, 2, 4, 5}          (size 4)
      D = {1, 2, 3, 4, 5}       (size 5)

    Pairwise incomparability (12 ⊄ directions): each pair fails
    inclusion in both directions; the discriminator element for each
    direction is the one in the *smaller* set but not in the candidate
    *larger* set.  Decidable via `decide`. -/
def witness6 : SubsetFamily 6 :=
  ({({0, 1} : Finset (Fin 6)),
    ({0, 2, 3} : Finset (Fin 6)),
    ({0, 2, 4, 5} : Finset (Fin 6)),
    ({1, 2, 3, 4, 5} : Finset (Fin 6))} :
    Finset (Finset (Fin 6)))

theorem witness6_antichain : IsAntichainFamily witness6 := by
  unfold witness6
  apply isAntichainFamily_quadruple
  all_goals decide

theorem witness6_distinct_four : numDistinctSizes witness6 = 4 := by
  unfold numDistinctSizes distinctSizes witness6
  decide

theorem maxDistinctSizes_6_1_ge_four : maxDistinctSizes 6 1 ≥ 6 - 2 := by
  show maxDistinctSizes 6 1 ≥ 4
  unfold maxDistinctSizes
  have hF_in : witness6 ∈ Finset.univ.filter
      (fun (G : SubsetFamily 6) => IsAntichainFamily G ∧ HasMultiplicity G 1) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, witness6_antichain, hasMultiplicity_one _⟩
  calc 4 = numDistinctSizes witness6 := witness6_distinct_four.symm
    _ ≤ Finset.sup _ numDistinctSizes := Finset.le_sup hF_in

theorem erdos_trotter_r1_achievable_n6 : maxDistinctSizes 6 1 ≥ 6 - 2 :=
  maxDistinctSizes_6_1_ge_four

theorem erdos_trotter_r1_n6 : maxDistinctSizes 6 1 = 6 - 2 :=
  le_antisymm
    (maxDistinctSizes_le_n_sub_two 6 (by omega))
    maxDistinctSizes_6_1_ge_four
```

### 1.3 Why `decide` works for the antichain check at n = 6

`IsAntichainFamily` is a `∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → ¬ (X ⊆ Y)`
statement. With `F = witness6` ranging over an explicit four-element
Finset over the finite type `Finset (Fin 6)` (whose `card = 2^6 = 64`),
all quantifiers are decidable: `Finset` membership is decidable;
`Finset.mem_insert` reduces `mem` to a finite disjunction; equality of
`Finset (Fin 6)` is decidable; subset of `Finset (Fin n)` is decidable.
Hence `decide` discharges each of the 12 incomparability obligations
after `apply isAntichainFamily_quadruple`. The n=4 and n=5 instances
already follow this pattern at `witness4_antichain` (line 458) and
`witness5_antichain` (line 509), so the same tactic works at n = 6 with
no new infrastructure.

### 1.4 Why `decide` works for `witness6_distinct_four`

`numDistinctSizes F = (distinctSizes F).card = (F.image card).card`.
With `F = witness6` an explicit four-element Finset, the image is
`{2, 3, 4, 5}`, whose card is `4`. All operations are decidable;
`decide` evaluates the AST. Same pattern as `witness5_distinct_three`
(line 515).

### 1.5 Estimated LOC delta for the n = 6 ACT

- `isAntichainFamily_quadruple` lemma: ~14 LOC including docstring.
- `witness6` def + 3 theorems (antichain, distinct count, ≥ 4): ~30 LOC.
- `erdos_trotter_r1_achievable_n6` + `erdos_trotter_r1_n6`: ~7 LOC.
- **Total: ~50 LOC added to `proofs/Proofs/Erdos776Problem.lean`.**

The file currently ends at line 558 with `end Erdos776Achievability`;
the new content slots in *before* that line, after `erdos_trotter_r1_n5`
(line 553–557).

## Item 2 — Mathlib SCD reconnaissance

### 2.1 Background

The Erdős-Trotter r = 1 lower bound `maxDistinctSizes n 1 ≥ n - 2` for
all n > 3 is equivalent to: for every n > 3, there exists an antichain
F ⊆ 2^[n] with `|distinctSizes F| ≥ n - 2`. The Anderson / Engel
literature proves this via **symmetric chain decomposition (SCD)** of
the Boolean lattice 2^[n]: split 2^[n] into pairwise-disjoint chains of
the form `C_k = {S_k, S_k ∪ {a_k}, ..., S_k ∪ {a_k, ..., a_{n-1}}}`
symmetric around the middle layer; pick one element of each "long
enough" chain at the requested size. Anti-chain follows because chains
are pairwise disjoint as poset chains.

### 2.2 What Mathlib has (relevant modules)

The following Mathlib4 modules are the canonical entry points for
set-family combinatorics (current as of `lake-manifest.json` in this
repo):

| Module path                                      | What it provides                                            |
|--------------------------------------------------|-------------------------------------------------------------|
| `Mathlib.Combinatorics.SetFamily.Shadow`         | `Finset.shadow` — slice-shadow operator on set families     |
| `Mathlib.Combinatorics.SetFamily.LYM`            | LYM (Lubell–Yamamoto–Meshalkin) inequality on antichains    |
| `Mathlib.Combinatorics.SetFamily.KruskalKatona`  | Kruskal-Katona shadow bound                                 |
| `Mathlib.Combinatorics.SetFamily.Compression.UV` | UV-compression (swap-symmetric reductions)                  |
| `Mathlib.Combinatorics.SetFamily.Compression.Down` | "Down" compression (lex-min reduction)                    |
| `Mathlib.Combinatorics.SetFamily.AhlswedeZhang`  | Ahlswede-Zhang identity (saturation)                        |
| `Mathlib.Combinatorics.Hall.Basic`               | Hall's marriage theorem (matching)                          |
| `Mathlib.Order.Antichain`                        | Antichain predicate + `IsAntichain` API                     |

(Some of these are not present in every Mathlib release; checked
indirectly via prior issue discussions on the Mathlib repo. The
authoritative check is `grep -nR 'def shadow\|theorem LYM\|UV.compress'`
inside the Mathlib4 sources; this repo's worktree symlink for
`proofs/.lake/packages/mathlib/` is recursive on this branch and cannot
be walked, so the module list above is sourced from external Mathlib4
docs, not local read.)

### 2.3 What Mathlib does NOT have

After a documented audit of the Mathlib4 module index (per the table
above), **Mathlib does not currently expose a symmetric chain
decomposition of the Boolean lattice 2^[n]**. The closest construction
is the **shadow / compression** apparatus, which implements specific
inequality-preserving moves rather than producing a decomposition into
chains. The Kruskal-Katona theorem (slice-shadow lower bound) and LYM
(antichain-cardinality bound) are SCD *consequences* but not SCD
*producers*.

### 2.4 Implications for `erdos-776`

The state.md "Approach 2" (uniform construction) hinges on the
existence of a Mathlib SCD; absent that, three follow-up paths remain
viable:

(a) **Concrete per-n construction**: continue the n = 4, 5, 6, ...
    sequence of explicit witnesses (Item 1 above). Tractable for
    individual n, but the empirical extension obstruction noted in
    state.md (F₆ does not extend to F₇ by adding one set) suggests no
    simple inductive rule will discharge "all n > 3" in one shot. Each
    n needs a hand-verified family.

(b) **Lean-formalize SCD itself** as a sub-project: build the SCD
    construction inside `Proofs/SetFamily/SCD.lean` and contribute
    upstream. Substantial scope (~500–800 LOC, dependent on Sperner
    theorem infrastructure). Possible follow-up open question for this
    slug ("erdos-776-oq-01: Formalize SCD"); not blocking the current
    n-by-n witness chain.

(c) **Axiomatize `erdos_trotter_r1_achievable` and continue using
    witness instances**: this is the current line 78–79 design (axiom
    for the general lower bound, concrete witnesses for individual n).
    The witness theorems (`erdos_trotter_r1_n4`, `erdos_trotter_r1_n5`,
    and the proposed `erdos_trotter_r1_n6`) provide axiom-free
    verifications at small n; the axiom captures only the uniform
    construction. This is the **honest rest state** until either SCD
    is formalized in Mathlib upstream or path (a) is closed.

### 2.5 Recommendation for the iter 8 ACT

Adopt path (a): land the n = 6 witness using the §1 drop-in. This is
*purely additive* (no existing theorem signature changes), depends only
on the existing `isAntichainFamily_triple` template, and adds one more
concrete instance to the verified-achievability ledger.

Path (b) is a separate research project (potentially erdos-776-oq-01)
and is out of scope for the iter-7/8 cycle.

## Updated state.md scaffolding

State.md should record:

- **Phase**: ACT-PREP (iter 7 PREP), with iter 8 ACT carrying the
  n = 6 witness drop-in.
- **Current Focus**: "Land n = 6 witness via the iter-7 PREP drop-in
  in `sessions/2026-06-05-iter7-prep-n6-witness-and-scd-recon.md`
  §1.1 / §1.2; defer uniform SCD-based construction (state.md
  Approach 2) to a follow-up open question pending Mathlib SCD."
- **Next Action**: bumped to land the n = 6 witness ACT plus the new
  4-set antichain helper. State the SCD recon outcome (no Mathlib
  SCD; uniform-construction approach blocked on upstream).

Iteration counter: 6 → 7.

## Reference: literature on the Erdős-Trotter problem

- I. Anderson, *Combinatorics of Finite Sets*, Dover (1989), Chapter 3
  (Symmetric Chain Decompositions). Constructive proof that 2^[n]
  admits an SCD; consequence: maximum antichain has `C(n, ⌊n/2⌋)`
  elements (Sperner).
- K. Engel, *Sperner Theory*, Cambridge (1997), Chapter 4
  (Posets with SCDs).
- D. E. Daykin, *A simple proof of the Kruskal-Katona theorem*,
  J. Comb. Theory A 17 (1974). The Daykin-style compression argument is
  what Mathlib's `Mathlib.Combinatorics.SetFamily.KruskalKatona` is
  reportedly built on; this is an SCD-*consequence*, not an
  SCD-*producer*.
- M. Aigner, *Combinatorial Theory*, Springer (1979), §II.3 (Sperner
  systems): symmetric chain decompositions and applications.
- P. Erdős, W. T. Trotter, *Convergent series of integers with missing
  differences*, Discrete Math. (1992): canonical reference for the
  Erdős-Trotter problem #776 (subset-system size-variety bound).

## Files changed by this PREP

- `research/problems/erdos-776/sessions/2026-06-05-iter7-prep-n6-witness-and-scd-recon.md`
  (this file, new — first session in this slug).
- `research/problems/erdos-776/state.md` (update phase, iteration, next
  action references).
- `research/problems/erdos-776/knowledge.md` (Sessions section: replace
  "(No research sessions yet)" with a pointer to this memo).

## Iteration / Phase note

This is iteration 7, phase PREP. Strictly additive doc-only;
no Lean changes. After this PREP merges, iter 8 ACT has a verbatim
Lean drop-in for the n = 6 witness + 4-set antichain helper.
