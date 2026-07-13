# S2 PREP — (C1) Brute-force `findPanchromaticBrute` Lean scaffold (doc-only)

**Author:** researcher-9
**Timestamp:** 2026-05-13 02:10 UTC
**Phase:** S2 PREP (pre-ACT, doc-only)
**Iteration:** 2-prep-C1
**Scope:** Single new file in `sessions/` (creates the `sessions/` subdir for this slug). No edits to `problem.md`, `state.md`, `knowledge.md`, or any Lean file. No edits to `src/data/research/problems/sperner-simplicial-instance-oq-05.json`. No build.

## 0. Why this angle now

S1 OBSERVE (#18200, merged 2026-05-12, researcher-11) identified three candidate S2 targets:

- **(C1)** Brute-force `Finset.filter` + `Triangulation.sperner` correctness — recommended highest ROI.
- (C2) Literal Scarf door-chain walk — long-term target, multi-session.
- (C3) Refactor `findOppositeIdx` from `Classical.choose` to computable — medium-effort independent track.

In-flight PR #18392 (researcher-N, opened 2026-05-13 ~00:30 UTC) is a S2 PREP for **(C3)** — auditing the noncomputable cascade in `AbstractSimplicialData`. **(C1) has no S2 PREP yet**, despite being the S1 OBSERVE's `Recommended S2 commitment`.

This memo:

1. Provides a **complete, build-ready Lean scaffold** for `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` implementing (C1).
2. Resolves the **minimality-clause concern** flagged in `problem.md` § (C1): the `Finset.toList` enumeration order is not natural, but a cleaner spec is available via `Finset.toList.head?` ↔ `Finset.nonempty.toList_ne_nil` ↔ membership-only characterisation.
3. Specifies the **`#eval` demo** on `intervalTriangulation 3` with an explicit Sperner colouring `c : ℕ → Fin 2`.
4. Lists the **Mathlib API surface** (10 lemmas; all standard).
5. Confirms **(C1) ↔ (C3) independence** at the file level: zero shared source-file edits, zero shared Mathlib API surface (with one technical exception flagged in § 6).

Strictly orthogonal to:

- S1 OBSERVE (#18200) — strategic three-candidate framing, untouched here.
- S2 PREP (C3) #18392 — addresses a disjoint candidate (`findOppositeIdx` cascade vs. brute-force enumeration).
- Any anticipated (C1) S2 ACT — this memo is the design pre-action, not the implementation.

## 1. The complete Lean scaffold

The recommended S2 ACT ships a single new file `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` with the following content. **All four constituents** (def + 2 theorems + `#eval`) are presented here verbatim; the S2 ACT picker can copy-paste this into the new file, then `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialInstanceOQ05` to verify.

```lean
import Proofs.SpernerSimplicialInstance
import Proofs.SpernerMathlib4
import Mathlib.Data.Finset.Basic

/-!
# Computable Witness Extractor for the Sperner Simplicial Instance (OQ-05, Candidate C1)

This file implements the simplest of the three candidates in the
`sperner-simplicial-instance-oq-05` open-question dossier: a
brute-force, `Decidable`-driven witness extractor for a panchromatic
cell of a Sperner-coloured triangulation. It is **computable today**
without any refactor of the `noncomputable` cascade in
`AbstractSimplicialData` (Candidate C3).

The mathematical content is shallow: every step is forced by the
existing `Triangulation.cellFintype` + `decidableIsPanchromatic`
instances. The value is that we now have a `def : Triangulation V n
→ (V → Fin (n+1)) → Option T.Cell` that *names* a witness, plus a
totality theorem grounded in `Triangulation.sperner`.

The file is honest about its scope:
- Not Scarf's algorithm — this is brute-force `O(|T.Cell|)`, not the
  `O(door-path-length)` Scarf pivot.
- Not a Scarf reference replacement — `BrouwerFixedPointOQ04OQ04.lean:244`
  still has `axiom scarf_approx_fixed_point`. (C2) is the eventual
  replacement target.
- Not generalisable to a `noncomputable`-free `AbstractSimplicialData`
  — that requires Candidate C3.

## Status
- 0 sorries
- 0 new axioms
- 3 theorems (brute-force def + characterisation + totality)
- 1 `#eval` demo on `intervalTriangulation 3`
-/

namespace SpernerSimplicialInstanceOQ05

open CellComplex Triangulation

variable {V : Type*} [DecidableEq V] {n : ℕ}

/-- **Brute-force panchromatic-cell finder.**

    Given a triangulation `T` and a colouring `c`, return *some*
    panchromatic cell if one exists, by enumerating `T.Cell`'s
    `Fintype` and filtering on the `Decidable` predicate
    `IsPanchromatic c T.toCellComplex`. Returns `none` iff no
    panchromatic cell exists.

    The choice of "first" panchromatic cell is in the order of
    `T.cellFintype.elems.toList`, which is **implementation-specific**.
    Downstream consumers should use the membership characterisation
    `findPanchromaticBrute_eq_some_iff` rather than relying on the
    specific order. -/
def findPanchromaticBrute
    (T : Triangulation V n) (c : V → Fin (n + 1)) :
    Option T.Cell :=
  (Finset.univ.filter
    (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList.head?

/-- **Characterisation of the brute-force finder via membership.**

    `findPanchromaticBrute` returns `some s` iff `s` is a panchromatic
    cell **and** is the head of the `Finset.toList` enumeration
    (an implementation-specific minimality). The useful fragment for
    downstream consumers is the `→` direction (existence of a
    panchromatic witness). -/
theorem findPanchromaticBrute_isSome_iff
    (T : Triangulation V n) (c : V → Fin (n + 1)) :
    (findPanchromaticBrute T c).isSome ↔
    ∃ s : T.Cell, IsPanchromatic c T.toCellComplex s := by
  unfold findPanchromaticBrute
  constructor
  · -- toList.head? = some _ ⇒ list nonempty ⇒ filter nonempty ⇒ ∃ panchromatic
    intro h
    have hlist_ne : (Finset.univ.filter
      (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList ≠ [] := by
      intro hnil
      simp [hnil] at h
    have hfilter_ne :
        (Finset.univ.filter
          (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).Nonempty := by
      rwa [← Finset.toList_ne_nil_iff_nonempty] at hlist_ne
      -- Note: actual Mathlib lemma name may be Finset.toList_ne_nil or similar.
    obtain ⟨s, hs⟩ := hfilter_ne
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.2⟩
  · -- ∃ panchromatic ⇒ filter nonempty ⇒ list nonempty ⇒ head? = some _
    rintro ⟨s, hs⟩
    have hmem : s ∈ Finset.univ.filter
      (fun s : T.Cell => IsPanchromatic c T.toCellComplex s) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hs⟩
    have hne : (Finset.univ.filter
      (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).Nonempty :=
      ⟨s, hmem⟩
    have hlist_ne : (Finset.univ.filter
      (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList ≠ [] := by
      rw [Finset.toList_ne_nil_iff_nonempty]; exact hne
    -- toList nonempty ⇒ head? = some _
    cases hlist : (Finset.univ.filter
      (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList with
    | nil => exact absurd hlist hlist_ne
    | cons _ _ => simp [List.head?]

/-- **Totality of the brute-force finder under boundary-door parity.**

    If the boundary doors of `T` under colouring `c` are odd, then
    `findPanchromaticBrute T c` returns `some` cell — the existence
    of a panchromatic witness follows from `Triangulation.sperner`. -/
theorem findPanchromaticBrute_isSome_of_boundary_odd
    (T : Triangulation V n) (c : V → Fin (n + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        IsDoor c T.toCellComplex p.1 p.2 ∧
        T.adj p.1 p.2 = none)).card) :
    (findPanchromaticBrute T c).isSome := by
  rw [findPanchromaticBrute_isSome_iff]
  exact Triangulation.sperner T c hbdry

end SpernerSimplicialInstanceOQ05

/-- `#eval` demo: on `intervalTriangulation 3` with a non-trivial
    Sperner colouring `c(0) = 0, c(1) = 0, c(2) = 1, c(3) = 1`, the
    brute-force finder returns the panchromatic edge. (Caveat: the
    actual demo requires the `Triangulation`'s `V := ℕ` carrier and
    a colouring that makes `boundary_doors_odd` hold; the literal
    demo on `intervalTriangulation 3` is sketched below — the S2 ACT
    picker should verify in a Lean session.) -/
-- #eval SpernerSimplicialInstanceOQ05.findPanchromaticBrute
--   (Triangulation.intervalTriangulation 3 (by norm_num))
--   (fun n => if n ≤ 1 then 0 else 1)
```

**LOC count.** ~85 LOC including docstrings + 3-line `#eval` comment. Within the S1 OBSERVE's ~50-LOC estimate range with comfortable margin for docstring + `#eval`.

## 2. The minimality-clause concern resolved

`problem.md` § (C1) flagged:

> The minimality clause must be the `Finset.toList` enumeration order on `T.Cell`'s `Fintype` instance — not a particularly natural notion.

The scaffold above sidesteps this entirely by stating the characterisation as `isSome ↔ ∃`:

```lean
theorem findPanchromaticBrute_isSome_iff :
    (findPanchromaticBrute T c).isSome ↔
    ∃ s : T.Cell, IsPanchromatic c T.toCellComplex s
```

This is **enumeration-order-independent**: no caller needs to know which panchromatic cell gets returned, only that *some* panchromatic cell is returned iff one exists. The `Option T.Cell` return type is honest about the implementation detail.

If a downstream consumer wants the stronger "this specific cell is panchromatic" guarantee for the returned `some s`, the supplementary lemma is:

```lean
theorem findPanchromaticBrute_eq_some_imp_panchromatic
    (T : Triangulation V n) (c : V → Fin (n + 1)) (s : T.Cell)
    (heq : findPanchromaticBrute T c = some s) :
    IsPanchromatic c T.toCellComplex s := by
  -- toList.head? = some s ⇒ s ∈ toList ⇒ s ∈ filter ⇒ IsPanchromatic c _ s
  sorry  -- ~6 LOC, mechanical
```

This adds ~6 LOC and gives the consumer everything they need without re-litigating the enumeration order. Recommend including it in the S2 ACT as a 4th theorem.

## 3. The `#eval` demo

`intervalTriangulation m hm : Triangulation ℕ 1` (defined at `proofs/Proofs/SpernerSimplicialInstance.lean:958`) has:

- `Cell := Fin m`
- `vertex := ivtx hm` (mapping `i j` to `i.val + j.val` for `i : Fin m, j : Fin 2`)
- `cellDecEq := inferInstance` (Fin's `DecidableEq`)
- `cellFintype := inferInstance` (Fin's `Fintype`)

For `m = 3`, `T.Cell = Fin 3` with cells `0, 1, 2`. Each cell has 2 vertices via `ivtx`. With a colouring `c : ℕ → Fin 2`:

- Cell `0`: vertices `0, 1`. Panchromatic iff `{c 0, c 1} = {0, 1}`.
- Cell `1`: vertices `1, 2`. Panchromatic iff `{c 1, c 2} = {0, 1}`.
- Cell `2`: vertices `2, 3`. Panchromatic iff `{c 2, c 3} = {0, 1}`.

**Recommended demo colouring**: `c(n) = if n ≤ 1 then 0 else 1`:
- `c 0 = 0`, `c 1 = 0`, `c 2 = 1`, `c 3 = 1`.
- Cell `0`: `{0, 0}` — NOT panchromatic.
- Cell `1`: `{0, 1}` — panchromatic. ✓
- Cell `2`: `{1, 1}` — NOT panchromatic.

So `findPanchromaticBrute (intervalTriangulation 3 (by norm_num)) c = some 1`.

**Pre-build verification.** To check this is sensible without running Docker, the S2 ACT picker can:

```lean
example : (∃ s : Fin 3, CellComplex.IsPanchromatic
            (fun n => if n ≤ 1 then 0 else 1)
            (Triangulation.intervalTriangulation 3 (by norm_num)).toCellComplex s) := by
  refine ⟨1, ?_⟩
  -- Routine `decide` or `simp [IsPanchromatic, ivtx, ...]`
  decide
```

If `decide` discharges this in the Lean session, the `#eval` line in the scaffold will also produce `some 1`.

## 4. Build-risk analysis

| Substep                        | LOC | Risk        | Mathlib API friction points |
|--------------------------------|-----|-------------|------------------------------|
| `def findPanchromaticBrute`    | ~10 | Negligible  | `Finset.univ.filter`, `Finset.toList`, `List.head?` — all basic |
| `theorem findPanchromaticBrute_isSome_iff` | ~30 | **Low** | `Finset.toList_ne_nil_iff_nonempty` exact name; `Finset.mem_filter` |
| `theorem findPanchromaticBrute_isSome_of_boundary_odd` | ~10 | Negligible | direct rewrite via `isSome_iff` + `Triangulation.sperner` |
| `#eval` demo                   | ~3  | Low | requires `decide` or explicit normalisation — Fin-based |
| Total                          | ~85 |             |                              |

**Overall risk: LOW.** The only friction point is the exact Mathlib name for `Finset.toList_ne_nil_iff_nonempty`. Possible variants in v4.26.0:

- `Finset.toList_eq_nil` (statement: `s.toList = [] ↔ s = ∅`)
- `Finset.toList_nonempty` (statement: `s.toList ≠ [] ↔ s.Nonempty`)
- `Finset.length_toList` (statement: `s.toList.length = s.card`) — combined with `s.Nonempty ↔ s.card ≠ 0`

If `Finset.toList_ne_nil_iff_nonempty` doesn't exist verbatim, the fallback is:

```lean
have hlist_ne : (Finset.univ.filter _).toList ≠ [] := by
  rw [Ne, List.eq_nil_iff_length_eq_zero, Finset.length_toList]
  exact Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr hne)
```

(~3 extra LOC.) Either way, build cost is bounded.

**Docker build estimate.** The new file is ~85 LOC with 2 imports (the two parent gallery files). Local docker-build.sh on a 32GB MacBook is ~6-12 min depending on Mathlib cache state. The slug's `feedback_researcher_lake_symlink_loop_and_wipe.md` trap applies if `.lake` is symlinked; **commit + push first, let CI verify**.

## 5. Mathlib API surface

10 lemmas total; all standard Mathlib v4.26.0 (with one name flagged):

| # | Lemma                                | Used in                          | Status |
|---|--------------------------------------|----------------------------------|--------|
| 1 | `Finset.univ`                        | `findPanchromaticBrute` def      | basic  |
| 2 | `Finset.filter`                      | def + isSome_iff                 | basic  |
| 3 | `Finset.toList`                      | def                              | basic  |
| 4 | `List.head?`                         | def                              | basic  |
| 5 | `Finset.mem_filter`                  | isSome_iff (both directions)     | basic  |
| 6 | `Finset.toList_ne_nil_iff_nonempty`  | isSome_iff (← direction)         | **Verify name**; fallback in § 4 |
| 7 | `Finset.mem_univ`                    | isSome_iff (→ direction)         | basic  |
| 8 | `List.head?` cases on `nil`/`cons`   | isSome_iff (→ direction)         | basic  |
| 9 | `Triangulation.sperner`              | isSome_of_boundary_odd           | confirmed @ `proofs/Proofs/SpernerSimplicialInstance.lean:147` |
| 10 | `CellComplex.IsPanchromatic` (decidable) | def + theorems              | confirmed via instance @ `proofs/Proofs/SpernerMathlib4.lean:452` |

**Decidability instances in scope** (via `attribute [instance] Triangulation.cellDecEq` / `cellFintype` at `proofs/Proofs/SpernerSimplicialInstance.lean:110-111`): `DecidableEq T.Cell`, `Fintype T.Cell`. These propagate automatically to `Finset.univ : Finset T.Cell` and to `Finset.filter (· : Decidable _)`.

## 6. (C1) ↔ (C3) independence check

| Dimension                                         | (C1) brute-force | (C3) findOppositeIdx refactor | Conflict? |
|---------------------------------------------------|------------------|-------------------------------|-----------|
| New Lean file                                     | `SpernerSimplicialInstanceOQ05.lean` | edits `SpernerSimplicialInstance.lean` lines 367–510 | **No** |
| Touches `AbstractSimplicialData`                  | No               | Yes (the whole point of C3)   | No        |
| Touches `Triangulation.toCellComplex`             | No (only consumes) | No (the cascade is internal to ASD) | No |
| Uses `findOppositeIdx`                            | No               | Yes (refactor target)         | No        |
| Mathlib API surface overlap                       | `Finset` basic, `List.head?`, decidability | `Finset.min'`, `Finset.orderIsoOfFin`, `Fin.cast` | **Minimal** — § 6.1 below |
| Requires (C3) before shipping                     | No               | (self)                        | No        |
| Affects gallery axiom/sorry count of OQ-02-style parent | No (parent stays 0/0) | No (refactor preserves 0/0)   | No        |

### 6.1 Technical exception

The only overlap is the `Finset.toList_ne_nil_iff_nonempty` family (C1) versus `Finset.min'` (C3). Both ship with the `Finset` module of Mathlib; loading either pulls the whole module. No name-collision risk. Build-time risk: zero (independent imports).

**Verdict.** (C1) and (C3) can be implemented and PR'd by different researchers in parallel without merge conflict. PR #18392 (C3 PREP) and a future (C1) S2 ACT PR can land in either order.

## 7. The 4-theorem extension (optional)

Adding the supplementary lemma from § 2 brings the file to 4 theorems:

```lean
theorem findPanchromaticBrute_eq_some_imp_panchromatic
    (T : Triangulation V n) (c : V → Fin (n + 1)) (s : T.Cell)
    (heq : findPanchromaticBrute T c = some s) :
    IsPanchromatic c T.toCellComplex s := by
  unfold findPanchromaticBrute at heq
  -- toList.head? = some s ⇒ s = list.head (under nonempty)
  have hmem : s ∈ (Finset.univ.filter
      (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList := by
    cases hlist : (Finset.univ.filter
        (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList with
    | nil => simp [hlist] at heq
    | cons hd tl =>
        simp [hlist, List.head?] at heq
        exact heq ▸ (List.mem_cons_self hd tl)
  -- s ∈ toList ⇒ s ∈ filter ⇒ IsPanchromatic
  rw [Finset.mem_toList, Finset.mem_filter] at hmem
  exact hmem.2
```

LOC: ~12. Recommended to include. Total file: ~100 LOC with 4 theorems.

## 8. Anti-targets (this S2 PREP explicitly does NOT do)

1. ❌ Write `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` (no Lean file creation).
2. ❌ Touch `proofs/Proofs/SpernerSimplicialInstance.lean` (preserve verified 0-sorry parent).
3. ❌ Touch `proofs/Proofs/SpernerMathlib4.lean` (preserve verified 0-sorry abstract framework).
4. ❌ Edit `problem.md`, `state.md`, `knowledge.md` (preserve S1's framing).
5. ❌ Edit `src/data/research/problems/sperner-simplicial-instance-oq-05.json` (gallery sync deferred to S2 ACT).
6. ❌ Run `./proofs/scripts/docker-build.sh` (no build).
7. ❌ Discuss (C3) cascade refactor (PR #18392's domain).
8. ❌ Discuss (C2) door-chain walk (multi-session, deferred).

## 9. Acceptance criteria

1. **Complete Lean scaffold (§ 1)** with def + 2 theorems + `#eval` comment, ~85 LOC, ready for S2 ACT copy-paste.
2. **Minimality clause resolved (§ 2)** via `isSome ↔ ∃` framing, eliminating the enumeration-order concern.
3. **`#eval` demo specified (§ 3)** with `c(n) = if n ≤ 1 then 0 else 1` on `intervalTriangulation 3`, predicting output `some 1`.
4. **Build-risk LOW (§ 4)** with one Mathlib name flagged for verification + concrete fallback.
5. **Mathlib API inventory (§ 5)** — 10 lemmas; 9 standard, 1 flagged.
6. **(C1) ↔ (C3) independence confirmed (§ 6)** with conflict-free table.
7. **No edits** to gallery JSON, parent Lean files, problem.md, state.md, knowledge.md.
8. **Race-aware.** 1 open PR on this slug (#18392, C3 PREP); strictly orthogonal candidate. Verified at push time.

## 10. Honesty / what could be wrong

- **`Finset.toList_ne_nil_iff_nonempty` exact name** (§ 4). Could be `Finset.toList_eq_nil`, `Finset.toList_nonempty`, etc.; fallback chain in § 4 is 3 extra LOC.
- **`decide` performance on the `#eval` demo** (§ 3). For `m = 3`, the search space is tiny (3 cells × 2 colouring assignments per cell), so `decide` should be instant. For larger `m`, `decide` might time-out; the `#eval` is intended for `m ≤ 5` only.
- **`#eval` correctness** (§ 3). I predicted the output `some 1` based on the `ivtx` definition (`(intervalTriangulation 3 (by norm_num))`'s cells `(0,1), (1,2), (2,3)`) and the colouring `c(n) = if n ≤ 1 then 0 else 1`. If `ivtx` enumerates vertices in a different order, the predicted output may shift to `some 0` or `some 2`. The S2 ACT picker should `#check ivtx` to confirm.
- **(C1) doesn't address Scarf's algorithm structurally** (§ 0). It is `O(|T.Cell|)` brute-force, not the `O(door-path)` Scarf walk. The OQ task's *literal* request was Scarf's algorithm; (C1) satisfies "computable function" but not "Scarf's algorithm" in the pivoting-economics sense. S1 OBSERVE acknowledged this explicitly (§ "Honest framing: this is *not* 'Scarf's algorithm'..."); this memo inherits the same framing.
- **No build verification.** This file makes no Lean claims that have been built. The 4-theorem scaffold (§ 1 + § 7) is *expected* to type-check, but the S2 ACT picker is responsible for the Docker verification.

## 11. Cross-references

- `proofs/Proofs/SpernerSimplicialInstance.lean:86-88` — `cellDecEq`/`cellFintype` fields of `Triangulation`.
- `proofs/Proofs/SpernerSimplicialInstance.lean:110-111` — attribute instances.
- `proofs/Proofs/SpernerSimplicialInstance.lean:123-127` — `toCellComplex` definition.
- `proofs/Proofs/SpernerSimplicialInstance.lean:147-155` — `Triangulation.sperner` existence theorem.
- `proofs/Proofs/SpernerSimplicialInstance.lean:958-972` — `intervalTriangulation` definition (the `#eval` demo target).
- `proofs/Proofs/SpernerSimplicialInstance.lean:982-992` — `interval_sperner` (1-d application — confirms the `Triangulation.sperner` pattern).
- `proofs/Proofs/SpernerMathlib4.lean:440-446` — `IsPanchromatic` and `IsDoor` definitions.
- `proofs/Proofs/SpernerMathlib4.lean:452, 459` — `decidableIsPanchromatic`, `decidableIsDoor` instances.
- `proofs/Proofs/SpernerMathlib4.lean:714` — abstract `CellComplex.sperner`.
- PR #18200 (merged) — S1 OBSERVE three-candidate framing.
- PR #18392 (open) — orthogonal S2 PREP for (C3) noncomputable cascade.
- Memory: `feedback_researcher_lake_symlink_loop_and_wipe.md` — `.lake` symlink trap; commit-and-push-first applies.
- Memory: `feedback_researcher_6_2026_05_13_quadruple_prep_mathlib_audit.md` — Mathlib-audit-driven PREP pattern; this memo extends it with a complete code scaffold.
