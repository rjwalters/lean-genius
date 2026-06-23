# S18c-orbit-precursor-3 — Permutation-Stabilizer Count (PREP)

**Iteration**: S18c-orbit-precursor-3 (Part 33 candidate, doc-only PREP)
**Author**: researcher-6
**Date**: 2026-05-12
**Branch**: `research/four-square-distribution-oq-01-s18c-perm-stab-prep-*`
**Status**: design memo — no Lean changes in this PR, no edits to
existing `s18*` notes, `problem.md`, `knowledge.md`, `state.md`, or the
gallery JSON.

## 0. Why a PREP (not S18c-orbit-precursor-3 ACT)

The existing `s18c-orbit-precursor-signflip-stabilizer.md` (Part 31,
researcher-11, PR #18139) closes with:

> **Next step.** S18c-orbit: invoke `MulAction.orbit_card_dvd_of_finite`
> (Mathlib v4.26.0) and case-analyse on the zero/coincidence pattern of
> `v` to conclude `8 ∣ |Orbit_{(ℤ/2)⁴ ⋊ S₄} v|` … Requires a
> permutation-side stabilizer count (`Stab_S₄ v` as a function of the
> multiplicity pattern of `(|v 0|, |v 1|, |v 2|, |v 3|)`) which is the
> natural next precursor; the present `signFlipStabilizer_card` is the
> (ℤ/2)⁴-side half.

This PREP locks the **Mathlib-bridge** approach for the permutation
stabilizer so the next researcher who picks up Part 33 can ship a
~30 LOC ACT (not the ~100-200 LOC case-analytic alternative
state.md hints at).

The decisive new finding: **Mathlib v4.26.0 already proves the formula
we want**, packaged as `DomMulAct.stabilizer_card'` in
`Mathlib.GroupTheory.Perm.DomMulAct`. No case enumeration is required;
the multiplicity-pattern combinatorics are subsumed by the
Mathlib lemma.

## 1. Goal of the eventual S18c-orbit-precursor-3 ACT

Add a single lemma to `proofs/Proofs/FourSquareDistributionOQ01.lean`
inside `namespace S18c`, anchored after `applyPerm_eq_iff` (currently
line 2697) and before the `end S18c` closer:

```lean
/-- **(S18c-orbit-precursor-3, Part 33)** Permutation-stabilizer
    cardinality formula.

    For any `v : Fin 4 → ℤ`, the cardinality of the permutation
    stabilizer

      `{ σ : Equiv.Perm (Fin 4) // applyPerm σ v = v }`

    equals the product, over each distinct value `i ∈ image v`, of the
    factorial of the number of coordinates where `v` takes that value:

      `|Stab_S₄ v| = ∏ i ∈ (Finset.univ.image v), (multiplicity of i)!`.

    Combined with Part 31's `signFlipStabilizer_card` and Mathlib's
    orbit-stabilizer theorem, this yields the per-orbit cardinality
    needed for the 8-divisibility argument
    (`orbitCard_dvd_eight_of_pos_target_decl`). -/
lemma permStabilizer_card (v : Fin 4 → ℤ) :
    Fintype.card { σ : Equiv.Perm (Fin 4) // applyPerm σ v = v } =
      ∏ i ∈ Finset.univ.image v, (Fintype.card { j : Fin 4 // v j = i })!
```

Net delta target: +30 LOC including docstring and proof body (~10 LOC
of actual tactics). 0 sorries, 0 axioms, no edits outside the lemma
insertion point.

## 2. Mathlib bridge

The key Mathlib citation is

```
-- Mathlib.GroupTheory.Perm.DomMulAct, line 122 at rev
-- 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 (v4.26.0)
theorem stabilizer_card' :
    Fintype.card {g : Perm α // f ∘ g = f} =
      ∏ i ∈ Finset.univ.image f, (Fintype.card ({a // f a = i}))! := by ...
```

verified live on 2026-05-12 via the GitHub Contents API. Type
variables are `α` (the domain, here `Fin 4`) and `ι` (the codomain,
here `ℤ`); the statement requires `[Fintype α] [DecidableEq α]
[DecidableEq ι]` — all available for `(Fin 4, ℤ)`.

A second hit, `stabilizer_card` (no prime), requires the codomain `ι`
to be finite too, which fails for `ℤ`. The prime form is the only
applicable one.

## 3. Bridge to the local convention

The local action convention in `proofs/Proofs/FourSquareDistributionOQ01.lean`
(Part 30, line 2634) reads:

```lean
def applyPerm (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  v ∘ σ.symm
```

So locally `applyPerm σ v = v ↔ v ∘ σ.symm = v`. Mathlib's
`stabilizer_card'` is over `{g // f ∘ g = f}`. The bridge is the
substitution `g := σ.symm`:

- Map `α : {σ // applyPerm σ v = v} → {g // v ∘ g = v}` by `α σ = σ.symm`.
- Map `β` in the reverse direction by `β g = g.symm`.
- Both `α.left_inv` and `α.right_inv` are `Equiv.symm_symm`.

The bijection is a `Finset.image` (or `Equiv.subtypeEquivRight` after
the predicate-equality rewrite is done first).

In Lean 4, the cleanest formulation is:

```lean
have hcard : Fintype.card { σ : Equiv.Perm (Fin 4) // applyPerm σ v = v } =
              Fintype.card { g : Equiv.Perm (Fin 4) // v ∘ g = v } := by
  apply Fintype.card_congr
  refine Equiv.mk
    (fun ⟨σ, hσ⟩ => ⟨σ.symm, ?_⟩)
    (fun ⟨g, hg⟩ => ⟨g.symm, ?_⟩) ?_ ?_
  · -- applyPerm σ v = v ↔ v ∘ σ.symm = v (definitional unfold)
    show v ∘ σ.symm = v
    exact hσ
  · show applyPerm g.symm v = v
    show v ∘ (g.symm).symm = v
    rw [Equiv.symm_symm]; exact hg
  · rintro ⟨σ, _⟩; ext1; exact σ.symm_symm
  · rintro ⟨g, _⟩; ext1; exact g.symm_symm
```

Then apply `DomMulAct.stabilizer_card'` to the right-hand side. The
total expected proof body is ~10 LOC after one-line lemmas.

A leaner alternative is to invert the relation in the conclusion of
`stabilizer_card'` itself — note the product `∏ i ∈ image v` is symmetric
in `v` (depends only on the function `v`, not on `σ` vs `σ.symm`), so
once the subtype bijection is established, the LHS rewrites match
verbatim.

## 4. Multiplicity-pattern sanity check (not needed by the proof, but
useful for cross-validation)

For `v : Fin 4 → ℤ`, the 5 possible multiplicity patterns of
`(v 0, v 1, v 2, v 3)` (unordered):

| Pattern                 | image v count | multiplicities | ∏ (mult)!     | |Stab_S₄ v| |
|-------------------------|---------------|----------------|---------------|-------------|
| All distinct (a,b,c,d)  | 4             | 1,1,1,1        | 1·1·1·1 = 1   | 1           |
| One pair (a,a,b,c)      | 3             | 2,1,1          | 2·1·1 = 2     | 2           |
| Two pairs (a,a,b,b)     | 2             | 2,2            | 2·2 = 4       | 4           |
| Triple + single (a,a,a,b)| 2             | 3,1            | 6·1 = 6       | 6           |
| All equal (a,a,a,a)     | 1             | 4              | 24            | 24          |

Cross-check against the formula `|Orbit_S₄| = 24 / |Stab_S₄|`:

- All distinct: 24/1 = 24 (i.e. every permutation gives a new tuple)
- One pair: 24/2 = 12
- Two pairs: 24/4 = 6
- Triple + single: 24/6 = 4
- All equal: 24/24 = 1

Combined with sign-flip orbit cardinality `2^(# nonzero coords)`
(Part 31 + Part 32):

| Coord pattern        | # nonzero | sign orbit | mult pattern  | S₄ orbit | combined |
|----------------------|-----------|------------|---------------|----------|----------|
| (a, 0, 0, 0), a ≠ 0  | 1         | 2          | 3+1           | 4        | 8        |
| (a, b, 0, 0), a,b ≠ 0, a ≠ b | 2 | 4         | 2+1+1         | 12       | 48       |
| (a, b, 0, 0), a = b ≠ 0 | 2     | 4          | 2+2           | 6        | 24       |
| (a, b, c, 0), distinct nonzero | 3 | 8     | 1+1+1+1+(0 multi) → wait, careful below |
| …                    |           |            |               |          |          |

Subtlety: the multiplicity pattern depends on **all four values**
including any zero. So `(a, b, c, 0)` with `a, b, c` distinct nonzero
has multiplicity pattern `{1, 1, 1, 1}` (four distinct values: `a, b,
c, 0`). |Stab_S₄| = 1, |Orbit_S₄| = 24. Combined with sign orbit = 8,
combined = 192. Divisible by 8. ✓

Every entry in this combined column is divisible by 8 — this is the
8-divisibility claim being targeted, but the proof of *that* claim is
not in scope of Part 33; it requires Part 33 + a case-by-case
divisibility argument (probably Part 34).

## 5. Order of operations

S18c-orbit-precursor-3 ACT preconditions:

1. **Part 32 (PR #18216) is merged.** ✓ (merged 2026-05-12 23:19 UTC).
2. **No conflicting in-flight S18c PR on this slug.**
   - `git branch -r | grep four-square-distribution-oq-01 | grep s18c` at PREP push time
     shows: `s18-canonical-bridge-1778545163` (PR #17701, stale 24 h),
     `s11-atomic-axiom-decomp-1778269036` (PR #17388, stale 4 d).
   - Neither edits `namespace S18c` Part 33-region (lines 2697 onwards
     in current `FourSquareDistributionOQ01.lean`); both target
     S11/S18 boundary, far earlier in the file.
3. **Mathlib pin tolerates `DomMulAct.stabilizer_card'`.**
   Confirmed at rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
   (v4.26.0). The lemma has been in Mathlib since well before pin.

Build expectation: `./proofs/scripts/docker-build.sh
Proofs.FourSquareDistributionOQ01` (worktree-local). The new lemma
adds one import: `Mathlib.GroupTheory.Perm.DomMulAct`. Build cost
should be marginal (DomMulAct is a small file).

## 6. Tactical risks (sorted by likelihood)

### 6.1 `applyPerm` vs `f ∘ g` direction mismatch

The local `applyPerm σ v := v ∘ σ.symm` has the `.symm`. Mathlib's
`stabilizer_card'` has no `.symm`. The bridge step in §3 inverts via
`σ ↔ σ.symm`. If the bridge is omitted, the cardinality formula still
holds (because `σ ↦ σ.symm` is a bijection on `Equiv.Perm (Fin 4)`),
but the intermediate Lean steps must explicitly construct the
bijection. Risk: forgetting the bridge gives an off-by-`Equiv.symm`
type-mismatch error.

### 6.2 Import-cost of `Mathlib.GroupTheory.Perm.DomMulAct`

The current file imports `Mathlib.Tactic` (umbrella) plus several
algebra/data files; `Mathlib.GroupTheory.Perm.DomMulAct` is a
lightweight file (~150 LOC) but pulls in
`Mathlib.GroupTheory.GroupAction.Defs` and
`Mathlib.GroupTheory.Perm.Basic`. Low risk — both are already
transitively imported.

### 6.3 `Fintype` and `Decidable` instances on
`{ σ : Equiv.Perm (Fin 4) // applyPerm σ v = v }`

The proposition `applyPerm σ v = v` is decidable for `v : Fin 4 → ℤ`
because `DecidableEq ℤ` is in scope and `Fin 4 → ℤ` has `DecidableEq`
via `Pi.decidableEq`. `Fintype.card` on the subtype is well-defined
once `DecidableEq`-on-the-predicate is available. Mathlib's
`stabilizer_card'` derives the `Fintype` instance internally; the
bridge step inherits it.

If the proof needs an explicit instance, use
`@Fintype.subtype _ _ (fun σ => decEq (applyPerm σ v) v)` or
`Subtype.fintype _ (fun σ => Equiv.Perm (Fin 4)) _`.

### 6.4 `Finset.univ.image v` vs `Set.range v`

Mathlib's `stabilizer_card'` indexes over `Finset.univ.image f`. For
`f : Fin 4 → ℤ`, `Finset.univ.image f = (Finset.univ : Finset (Fin 4)).image f`
— a `Finset ℤ`. This is the right form for our target signature.

### 6.5 `applyPerm σ v = v ↔ v ∘ σ.symm = v` unfolding

The local lemma `applyPerm_eq_iff` (line 2689) reads:
`applyPerm σ v = v ↔ ∀ i, v (σ.symm i) = v i`. For the bridge, we need
the slightly cleaner form `v ∘ σ.symm = v` (which is `funext`-equivalent).
A one-step rewrite `show v ∘ σ.symm = v` followed by `exact hσ` resolves
the definitional gap.

### 6.6 No existing parent file uses `DomMulAct` namespace

`grep -r "DomMulAct" proofs/` returns no hits. The lemma will be the
file's first interaction with Mathlib's DomMulAct machinery. Style
risk only — no semantic risk.

## 7. Anti-targets (S18c-orbit-precursor-3 PREP & ACT)

PREP-time (this PR):
1. **No Lean changes.** No `proofs/Proofs/**` edits.
2. **No edits to `problem.md`** — formal scope unchanged.
3. **No edits to `knowledge.md`** — Mathlib alignment survey unchanged.
4. **No edits to `state.md`** — phase remains `ACT (S18c-orbit-precursor-2)`
   pending merge of Part 33 ACT.
5. **No edits to `s18-eight-divisibility-spec.md`** — that file is the
   parent spec; Part 33's role within it is documented in §3.8 there.
6. **No edits to `s18c-orbit-precursor-signflip-stabilizer.md`** — that
   is researcher-11's Part 31 note.
7. **No edits to the gallery JSON** (`src/data/proofs/four-square-distribution-oq-01/meta.json`
   or `src/data/research/problems/four-square-distribution-oq-01.json`).

ACT-time (the eventual Part 33 PR):
1. **No edits outside the `namespace S18c` insertion point.** Other
   namespaces (e.g. existing Parts 1-32) remain untouched.
2. **No edits to `meta.json` `axiomCount` or `theoremCount`** in the
   same PR as the lemma — the meta drift will be picked up by the
   audit cycle; mechanics handle it. Per memory
   `[Mechanic — seeker-init meta.sorries missing]`, do NOT pre-bump.
3. **No alias / deprecated stub** for any earlier
   `permStabilizer_card`-shaped declaration. None exists.
4. **No change of action convention** — `applyPerm σ v := v ∘ σ.symm`
   is locked in Part 30 and is downstream-compatible.

## 8. Acceptance criteria for the eventual S18c-orbit-precursor-3 ACT

Binary criteria for the Part 33 ACT PR:

1. New lemma `S18c.permStabilizer_card` exists in
   `proofs/Proofs/FourSquareDistributionOQ01.lean` with signature
   matching §1 verbatim (modulo whitespace).
2. Body is `≤ 30 LOC` (including docstring); no `sorry`; no `axiom`.
3. New `import` line for `Mathlib.GroupTheory.Perm.DomMulAct` (or
   inherited transitively if `Mathlib.Tactic` already pulls it).
4. Docker build of `Proofs.FourSquareDistributionOQ01` clears
   (or build-pending acceptable per S2 precedent).
5. No edits outside the `namespace S18c` insertion range.
6. PR title: `research(four-square-distribution-oq-01): S18c-orbit-precursor-3 — permStabilizer_card via Mathlib DomMulAct`.
7. PR body cites this PREP, Part 31's note, and the Mathlib lemma path.
8. Optional `sessions/` note: not required (this PREP doc serves the
   role).

## 9. Verification log (this PREP — read-only, no edits)

| Check                                                                              | Outcome |
|------------------------------------------------------------------------------------|---------|
| `wc -l proofs/Proofs/FourSquareDistributionOQ01.lean`                              | 2801 LOC |
| `namespace S18c` opens at line                                                     | 2446 |
| Part 30 `applyPerm` def at line                                                    | 2634 |
| Part 30 `applyPerm_eq_iff` at line                                                 | 2689 |
| Part 31 `signFlipStabilizer_card` at line                                          | 2536 |
| Part 32 `signFlipOrbit_card_ge_two` at line                                        | 2745 |
| Mathlib `DomMulAct.stabilizer_card'` at file/line                                  | `Mathlib/GroupTheory/Perm/DomMulAct.lean:122` |
| Mathlib `DomMulAct.stabilizer_card` (no prime) at file/line                        | `Mathlib/GroupTheory/Perm/DomMulAct.lean:99` |
| Mathlib `DomMulAct.stabilizerMulEquiv` at line                                     | 77 |
| Open PRs on `four-square-distribution-oq-01` at PREP push time                     | 2 (PR #17701 S18 stale 24h; PR #17388 S11 stale 4d) |
| Open PRs on `s18c` at PREP push time                                               | 0 |
| Recent merged research PR on slug                                                  | #18216 (Part 32, 2026-05-12 23:19 UTC) |
| Race check: open PR with "permStabilizer" or "perm-stab" in title                  | 0 |

## 10. Honesty / no-edit guarantee

This PR is **doc-only**:

- 1 new file: `research/problems/four-square-distribution-oq-01/s18c-orbit-precursor-perm-stab.md`
- 0 edits to existing files
- 0 edits to Lean files
- 0 edits to `meta.json` of any proof
- 0 edits to `state.md`, `problem.md`, `knowledge.md`, or earlier
  `s18*` notes

Diff against #17701 / #17388 is empty (mutually orthogonal — those
PRs target S11/S18 boundary, far from Part 33's insertion site at
line ~2697). Rebase risk: zero.

## 11. References

- Parent slug spec: `s18-eight-divisibility-spec.md` §3.8 ("(ℤ/2)⁴ ⋊ S₄
  orbit decomposition").
- Part 31 note: `s18c-orbit-precursor-signflip-stabilizer.md` (PR #18139).
- Part 32 (in-file) `signFlipOrbit_card_ge_two` (PR #18216).
- Mathlib `DomMulAct.stabilizer_card'`:
  `Mathlib/GroupTheory/Perm/DomMulAct.lean:122` at rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
