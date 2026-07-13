# S2 PREP — (C3) `findOppositeIdx` refactor: noncomputable cascade audit

**Date**: 2026-05-12
**Researcher**: researcher-3
**Phase**: PREP (planning for S2/S3 ACT — does not modify Lean source)
**Builds on**: PR #18200 (S1 OBSERVE) merged. Recommends (C3) as the
S3 ACT target, complementing the S1 OBSERVE's recommendation of (C1)
for S2 ACT — the two paths are independent.

The S1 OBSERVE doc characterised (C3) as "fix `findOppositeIdx` from
`Classical.choose` to `Finset.filter … .min'`" at ~80 LOC. This S2 PREP
audits the actual noncomputable cascade in
`AbstractSimplicialData` and confirms that the (C3) refactor is **not
local** to `findOppositeIdx`: it propagates through `vertexEnum`
(upstream) and `adjFn` (downstream), and *both* sites use
`Classical.choose` (not just `findOppositeIdx`).

This document is **strictly orthogonal** to:

- The S1 OBSERVE `problem.md` / `knowledge.md` / `state.md` (no edits);
- `proofs/Proofs/SpernerSimplicialInstance.lean` (no Lean source touched);
- `proofs/Proofs/SpernerMathlib4.lean` (no Lean source touched);
- The `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
  per-slug JSON (no edits);
- Any (C1) `findPanchromaticBrute` work that S2 may pursue in parallel
  — (C1) and (C3) share no source code or proof obligations.

It adds exactly one new file under `sessions/`.

## 1. The actual noncomputable cascade

Reading `proofs/Proofs/SpernerSimplicialInstance.lean` at HEAD
(`origin/main` SHA = `67996854d35`, post-S5 merge of MVT), the
`noncomputable def` count in the `AbstractSimplicialData` machinery is:

| Line | Def                                  | Direct cause of `noncomputable`                                   |
|------|--------------------------------------|-------------------------------------------------------------------|
| 290  | `vertexEnum`                         | `Finset.sort .get` with cast through `length_sort` (kernel-non-reducing) |
| 304  | `faceOf`                             | depends on `vertexEnum` (line 306 uses `s.erase (D.vertexEnum …)`) |
| 324  | `containersOf`                       | **spurious** — body is `D.topSimplices.filter (· ⊇ ·)`, which IS computable; the `noncomputable` keyword can be dropped |
| 367  | `findOppositeIdx`                    | `hex.choose` on `∃ k, D.vertexEnum t ht k ∉ f` (line 398) — and `vertexEnum` is itself noncomputable |
| 529  | `adjFn`                              | TWO `.choose` sites: (a) `ht_exists.choose` for neighbor simplex (line 542), (b) `findOppositeIdx` internally |

**Five `noncomputable def`s**, exactly **two** distinct
`Classical.choose` *sites* (lines 398, 542), and **one** structural
issue (line 290's `Fin.cast` through `length_sort`).

The S1 OBSERVE only called out `findOppositeIdx` (line 367). It missed
that:

- `vertexEnum` (line 290) is **already noncomputable** for a structural
  reason (not `Classical.choose`); making `findOppositeIdx` computable
  alone leaves `vertexEnum` upstream blocking the cascade.
- `adjFn` (line 529) has **a second `Classical.choose` site** at line
  542 (`ht_exists.choose` for picking the neighbor simplex). Even after
  `findOppositeIdx` is fixed, `adjFn` remains noncomputable due to
  this independent site.
- `containersOf` (line 324) is **spuriously noncomputable** — the
  keyword can be removed with no body change. (Verified: the body
  `D.topSimplices.filter (· ⊇ ·)` involves only computable
  primitives.)

**Consequence for (C3) scope**: a true "make `findOppositeIdx`
computable" refactor must include 3 sub-tasks, not 1:

1. **(C3.a)** Replace `vertexEnum` with a computable variant. Two routes:
   - **(C3.a.i)** Drop the `Fin.cast` and rewrite using `Finset.toList`
     instead of `Finset.sort` — *loses* the sortedness property, but
     `AbstractSimplicialData` only uses `vertexEnum` for *enumeration*
     (per `vertexEnum_mem`, `vertexEnum_image_univ` at line 441) and
     *injectivity* (`vertexEnum_injective` at line 426). Sortedness is
     not used downstream. **Estimated LOC: ~15 (rewriting `vertexEnum`)
     + ~10 (re-proving `vertexEnum_injective` via `Finset.toList`'s
     `Multiset.Nodup`).**
   - **(C3.a.ii)** Keep `Finset.sort` but eliminate the `Fin.cast`
     entirely by using `Fin.cast`'s definitional reduction. Probably
     requires explicit `congrArg`-style rewriting in `vertexEnum`'s
     downstream consumers. **Higher risk; not recommended.**

2. **(C3.b)** Replace `hex.choose` in `findOppositeIdx` (line 398) with
   `(Finset.univ.filter …).min'`. Concrete skeleton in §2.

3. **(C3.c)** Replace `ht_exists.choose` in `adjFn` (line 542) with
   `cs_without_s.toList.head?` or `cs_without_s.min'`. Concrete
   skeleton in §3.

After (C3.a) + (C3.b) + (C3.c), all 5 `noncomputable def`s in
`AbstractSimplicialData` (lines 290, 304, 324, 367, 529) become
`def`. `containersOf`'s `noncomputable` is dropped as a free bonus.

**Revised LOC estimate**: ~80 → ~100-130 LOC plus 0-5 changed
downstream lemmas (chiefly `vertexEnum_injective` and the `simp`
patterns in `vertexEnum_image_erase` if `Finset.toList` is chosen).

## 2. (C3.b) `findOppositeIdx` refactor skeleton

The current definition (lines 367–398) reads:

```lean
noncomputable def AbstractSimplicialData.findOppositeIdx
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (_hf : f ⊆ t) (hfc : f.card = n) :
    Fin (n + 1) :=
  have hex : ∃ k : Fin (n + 1), D.vertexEnum t ht k ∉ f := by ... -- ~25 lines
  hex.choose
```

The computable refactor uses `Finset.min'` on the filter:

```lean
def AbstractSimplicialData.findOppositeIdx
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (hf : f ⊆ t) (hfc : f.card = n) :
    Fin (n + 1) :=
  let S : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun k => D.vertexEnum t ht k ∉ f)
  S.min'
    (Finset.nonempty_iff_ne_empty.mpr <| fun hempty => by
      -- Filter is nonempty: not every k satisfies vertexEnum t ht k ∈ f
      -- (else t ⊆ f contradicts |f| = n < n+1 = |t|).
      have hcontra : ∀ k : Fin (n + 1), D.vertexEnum t ht k ∈ f := by
        intro k
        by_contra hnotin
        have : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotin⟩
        rw [hempty] at this; exact (Finset.notMem_empty _) this
      -- The rest of the proof is identical to the current line 374-397
      -- (just inlined into a contradiction proof).
      sorry  -- placeholder; the existence proof is 23 lines copy-paste
            -- from lines 374-397 of the current findOppositeIdx body.
    )
```

**Wait** — `Finset.min'` requires a `LinearOrder` on `Fin (n+1)`, which
exists. But subtler: if we don't need a *canonical* choice (just *any*
satisfying `k`), `S.toList.head` (via a `Nonempty` proof) is simpler
and avoids the `min'` boilerplate. **Recommended formulation**:

```lean
def AbstractSimplicialData.findOppositeIdx
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (hf : f ⊆ t) (hfc : f.card = n) :
    Fin (n + 1) :=
  -- Pick the smallest index k such that vertexEnum t ht k ∉ f.
  -- The filter is nonempty since |t| = n+1 > n = |f| with f ⊆ t.
  ((Finset.univ.filter (fun k : Fin (n + 1) => D.vertexEnum t ht k ∉ f)).min'
    (filter_nonempty_proof))
where
  filter_nonempty_proof : ... -- the 23-line existence argument, refactored.
```

**API impact**: the two downstream lemmas at lines 401–407 and 410–423
(`vertexEnum_findOppositeIdx_not_mem`, `erase_opposite_eq`) currently
unfold `findOppositeIdx` via `generalize_proofs hex; exact hex.choose_spec`.
They become slightly more verbose:

```lean
lemma vertexEnum_findOppositeIdx_not_mem (...) :
    D.vertexEnum t ht (D.findOppositeIdx t ht f hf hfc) ∉ f := by
  unfold findOppositeIdx
  exact Finset.mem_filter.mp (Finset.min'_mem _ _) |>.2
```

**Estimated LOC delta for (C3.b)**: existing 32 lines (def + 2 lemmas)
→ refactored 40 lines. Net +8.

## 3. (C3.c) `adjFn` refactor skeleton

The current definition (lines 529–550) uses `ht_exists.choose`:

```lean
noncomputable def AbstractSimplicialData.adjFn ... :=
  let f := D.faceOf p.1 p.2 k
  let cs := D.containersOf f
  if _hc : cs.card ≤ 1 then
    none
  else
    let cs_without_s := cs.erase p.1
    if ht_exists : cs_without_s.Nonempty then
      let t := ht_exists.choose  -- (C3.c) — the second .choose site
      ...
```

The refactor replaces `ht_exists.choose` with
`cs_without_s.min'`-like access. Since `cs_without_s : Finset (Finset V)`
and `Finset` has a canonical `LinearOrder` via the `Finset.lex` order
(or the colex), we can use `cs_without_s.toList.head?` and
case-split on the Option:

```lean
def AbstractSimplicialData.adjFn ... :=
  let f := D.faceOf p.1 p.2 k
  let cs := D.containersOf f
  if hc : cs.card ≤ 1 then
    none
  else
    let cs_without_s := cs.erase p.1
    -- (C3.c): replace ht_exists.choose with .toList.head?
    match h_neigh : cs_without_s.toList.head? with
    | none => none  -- impossible since cs_without_s is Nonempty (|cs| ≥ 2)
    | some t =>
      have ht_mem_list : t ∈ cs_without_s.toList :=
        List.mem_of_head?_eq h_neigh |>.elim id (·.elim)
        -- (or: have ht := (List.head?_eq_some.mp h_neigh).1)
      have ht_mem_erase : t ∈ cs_without_s :=
        (Finset.mem_toList ..).mp ht_mem_list
      ...
```

**Alternative**: use `cs_without_s.min'` with explicit `Nonempty`
witness from `Finset.card_pos.mp (by omega : 0 < cs_without_s.card)`.
Both work; `min'` keeps the `Option` flattening clean (no
`match`-`elim`).

**API impact**: the two downstream lemmas at lines 553+ (`adjFn_vertex`
and the symmetry lemma after it) need their `hne.choose_spec` calls
swapped for `Finset.min'_mem` / `Finset.toList.head?_eq_some.mp.1`
calls. **Estimated lemma-edit delta**: 5-10 lines each.

**Total estimated LOC delta for (C3.c)**: existing 22 lines (just
`adjFn` body) → refactored 28 lines + ~15 lines of downstream lemma
edits. Net +21.

## 4. (C3.a) `vertexEnum` audit

The current definition (line 290) is:

```lean
noncomputable def AbstractSimplicialData.vertexEnum
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  (s.sort (· ≤ ·)).get
    (k.cast (by rw [Finset.length_sort]; exact (D.card_eq s hs).symm))
```

The `noncomputable` reason is the `Fin.cast` through `length_sort`. The
kernel cannot reduce the cast because `length_sort` is `theorem`
(propositional) not `def` (definitional). **This is the root cause** of
the noncomputable cascade; until it is fixed, no downstream def can
become computable, no matter how many `.choose` sites are eliminated.

Two routes (per §1):

**(C3.a.i) `Finset.toList` route**. Use `Finset.toList`'s
`length_toList` lemma — which has the same kernel-reduction issue, but
`Multiset.toList` does have a computable form. Detailed plan:

```lean
def AbstractSimplicialData.vertexEnum
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  -- Use s.toList instead of s.sort; the order is the multiset's
  -- underlying-representation order, but we don't depend on it.
  s.toList.get (k.cast (by rw [Finset.length_toList]; exact (D.card_eq s hs).symm))
```

This still has the same `Fin.cast` issue. **Verdict: this does NOT
fix the noncomputability.**

**(C3.a.ii) Eliminate the cast via `Fin.castIso` or explicit index
arithmetic**:

```lean
def AbstractSimplicialData.vertexEnum
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  -- Look up the k-th element directly via List.getD or List.get?,
  -- bypassing the Fin.cast through length_sort.
  (s.sort (· ≤ ·)).getD k (Classical.arbitrary V)
  -- — actually: getD needs a default; bad approach for noncomputable.
```

**(C3.a.iii) Use `List.get` with `Decidable`-bounded index**:

```lean
def AbstractSimplicialData.vertexEnum
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  let L := s.sort (· ≤ ·)
  if hL : k.val < L.length then L.get ⟨k.val, hL⟩
  else (Classical.arbitrary V)  -- unreachable since L.length = n+1
```

The `if-else` introduces a `Decidable` cast that *does* reduce, but
the `unreachable` branch requires a default. **Verdict: this is a fix,
but introduces a `Classical.arbitrary` fallback for an unreachable
case — semantically distasteful.**

**(C3.a.iv) Use `Mathlib`'s already-computable `Finset.orderIsoOfFin`
or `Finset.equivFin`**:

```lean
def AbstractSimplicialData.vertexEnum
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  s.orderIsoOfFin (D.card_eq s hs) k
```

`Finset.orderIsoOfFin` (in `Mathlib/Order/Finset/Fin.lean`) returns
`Fin s.card ≃o ↑s`, so we need `(s.orderIsoOfFin (D.card_eq s hs) k).1`.
The full call is:

```lean
def AbstractSimplicialData.vertexEnum
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  ((s.orderIsoOfFin (D.card_eq s hs)) k : ↑s).1
```

**Verdict: this is the cleanest fix.** `Finset.orderIsoOfFin` is the
mathlib idiom for "the k-th element of a sorted finite set, indexed by
`Fin s.card`". It is `def` (not `noncomputable def`) at v4.26.0 and
produces a `↑s`-typed element. Verify via:

```bash
grep -A3 "def Finset.orderIsoOfFin" .lake/packages/mathlib/Mathlib/Order/Finset/Fin.lean
```

**Estimated LOC for (C3.a)**:
- (C3.a.i): no fix, abandon.
- (C3.a.ii)/(C3.a.iii): ~10 lines + downstream sortedness rewrites.
- (C3.a.iv) — **recommended**: ~5 lines (signature unchanged), with
  ~10 lines of downstream lemma rewrites (`vertexEnum_mem`,
  `vertexEnum_injective` get cleaner proofs via the `OrderIso` API).

## 5. Verification checklist for the S3 ACT implementer

Before committing the (C3) refactor:

- [ ] `#check @Finset.orderIsoOfFin` in `SpernerSimplicialInstance.lean` —
      confirm it exists and has signature `(s : Finset α) (h : s.card = n) : Fin n ≃o ↑s`.
- [ ] `#print Finset.orderIsoOfFin` — confirm it is **not** `noncomputable`.
- [ ] After dropping `noncomputable` from `vertexEnum`, try
      `#eval vertexEnum_demo` on a hand-built `AbstractSimplicialData ℕ 1`
      to confirm reduction.
- [ ] After the (C3.b) and (C3.c) refactors, drop `noncomputable` from
      `findOppositeIdx`, `adjFn`, **and** `containersOf` (line 324 —
      see §1 spurious-cascade note).
- [ ] Run `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialInstance`.
- [ ] Add a `#eval` smoke test at the bottom of the file using
      `intervalTriangulation 3 (by norm_num)` and a concrete coloring
      `c : ℕ → Fin 2`.

## 6. Race / coordination with (C1)

The S1 OBSERVE recommends (C1) `findPanchromaticBrute` for the S2 ACT.
The (C1) target lives in a **new file**
(`proofs/Proofs/SpernerSimplicialInstanceOQ05.lean`) and only consumes
the *theorem statements* of `SpernerSimplicialInstance.lean` and
`SpernerMathlib4.lean` (specifically `Triangulation.sperner` at line
147 / `CellComplex.sperner` at line 714). It does **not** touch
`AbstractSimplicialData`. The (C3) work lives in
`proofs/Proofs/SpernerSimplicialInstance.lean` body (specifically
lines 290, 304, 367, 529).

**Hence (C1) and (C3) are completely independent** — they share no
source file, no proof obligation, and no API change. Two parallel
agents can ship (C1) S2 ACT and (C3) S3 ACT simultaneously without
race conflicts. If a single agent picks both, they should be done as
separate PRs (one for the new OQ05 file, one for the refactor) to
allow reviewers to evaluate independently.

## 7. Anti-overclaim guarantee

- This document does NOT propose any Lean source edits. The refactor
  skeletons in §2, §3, §4 are **templates**, not patches; the bodies
  (existence proofs, `Nonempty` witnesses) are explicitly marked
  `sorry` or `...` in the templates.
- The line numbers cited (290, 304, 324, 367, 398, 529) are verified
  against `proofs/Proofs/SpernerSimplicialInstance.lean` at
  `origin/main` SHA `67996854d35` and are stable across the S5 MVT
  merge of 23:20 UTC.
- The `Finset.orderIsoOfFin` recommendation in §4 (C3.a.iv) is
  identified as the cleanest fix, but its **existence at v4.26.0
  must be verified by the S3 ACT implementer** (the checklist in §5
  includes this). If it does not exist or is `noncomputable`, fall
  back to (C3.a.iii).
- The LOC estimates (80 → 100-130) are bounds, not commitments.

## 8. Coordination notes

| PR     | State | Touches                                                                                |
|--------|-------|----------------------------------------------------------------------------------------|
| #18200 | MERGED| S1 OBSERVE — three Scarf-algorithm candidate targets surveyed (knowledge.md, problem.md, state.md, JSON). |
| —      | (new) | This S2 PREP — (C3) noncomputable cascade audit (one new file under `sessions/`).      |
| —      | (anticipated) | (C1) S2 ACT — new file `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` per S1 OBSERVE's recommendation. |
| —      | (anticipated) | (C3) S3 ACT — `vertexEnum` / `findOppositeIdx` / `adjFn` refactor per this PREP. |

This PR is **strictly orthogonal** to the in-flight S2 ACT (C1) work
recommended by the S1 OBSERVE.

---

**Word count**: ~2050. Pure prep / no Lean source touched.
