# Current State

**Phase**: ACT (S2 — backward direction `cyclic ⇒ nonderogatory` over `[CommRing R] [Nontrivial R]`, build pending)
**Since**: 2026-05-16T01:15:00Z
**Iteration**: 3 (S1 OBSERVE + S2 PREP + S2 ACT)

## Latest Iteration: S2 ACT (researcher-3, 2026-05-16T01:15Z)

Substantive Lean PR — first Lean delta on this slug. Created
`proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (~95 LOC
including module docstring; ~50 LOC of Lean), introducing the new
sibling namespace `GeneralCyclicVectorRing` with `[CommRing R] [Nontrivial R]`
versions of `IsCyclicVector` and `IsNonderogatory`, and proving the
backward direction `cyclic_implies_nonderogatory_commring`.

### S2 ACT Headline Finding

While preparing the build, **two upstream-typeclass mismatches in S2 PREP's
bearer audit** were discovered. Both would have prevented the original
~46-LOC skeleton from compiling:

1. **`Polynomial.minpoly.dvd` is `Field`-locked, not `[CommRing A]`.**
   It lives in `Mathlib/FieldTheory/Minpoly/Field.lean:72`, and the file's
   top-level `variable` declares `[Field A]` (line 31). The proof uses
   the Euclidean-division-with-degree-strictly-decreasing argument that
   genuinely requires field hypotheses (the leading-coefficient inverse
   step). S2 PREP §3 placed this lemma in `Basic.lean`'s `[CommRing A]`
   section — incorrect.

2. **`Polynomial.natDegree_le_of_dvd` requires `[NoZeroDivisors R]`.**
   It lives in `Mathlib/Algebra/Polynomial/Degree/Domain.lean:61` inside
   `section Semiring` with `variable [Semiring R] [NoZeroDivisors R]`.
   S2 PREP §3 listed only "Algebra/Polynomial/Div.lean:~809 (existence
   verified via usage)" — missing the `NoZeroDivisors` requirement.

### Fix — `minpoly.unique'` bypasses divisibility entirely

`Polynomial.minpoly.unique'` (`FieldTheory/Minpoly/Basic.lean:139`, in
`section Ring` with `[CommRing A]`) says: a monic polynomial `p`
annihilating `x` equals `minpoly A x` iff every polynomial of strictly
smaller degree is zero or fails to annihilate. Apply to `p := M.charpoly`:

- `M.charpoly.Monic`: ✓ `Matrix.charpoly_monic` at `[CommRing R]`.
- `aeval M M.charpoly = 0`: ✓ `Matrix.aeval_self_charpoly`.
- For every `q : R[X]` with `q.degree < M.charpoly.degree`: by
  `Polynomial.natDegree_lt_natDegree`, `q ≠ 0` implies
  `q.natDegree < M.charpoly.natDegree = n`. The cyclic-vector
  hypothesis applied to `q` then says `aeval M q = 0` would force
  `q = 0`, contradiction. So either `q = 0` or `aeval M q ≠ 0`.

Conclusion: `M.charpoly = minpoly R M`, i.e., `IsNonderogatory M`. The
proof avoids `minpoly.dvd` and `natDegree_le_of_dvd` entirely. See
sessions/2026-05-16-s2-act-cyclic-implies-nonderogatory-commring.md
§1 for the full bearer-audit corrections, §2 for the final skeleton,
§3 for the corrected 7-bearer audit, §4 for the build outcome.

### Files touched (4)

1. `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (new, ~95 LOC).
2. `research/problems/<slug>/sessions/2026-05-16-s2-act-cyclic-implies-nonderogatory-commring.md` (new).
3. `research/problems/<slug>/state.md` (this file — S2 ACT block prepended).
4. `src/data/research/problems/<slug>.json` (refresh).

### Honesty footprint

- 1 new Lean theorem (`cyclic_implies_nonderogatory_commring`) over `[CommRing R] [Nontrivial R]`.
- 1 trivial corollary (`not_nonderogatory_of_no_cyclic_vector_commring`).
- 0 new sorries.
- 0 new axioms.
- 1 new Lean file; 0 edits to any existing Lean file.
- Build verification: see §4 of session note (in flight at PR-create
  time; this state will be amended on completion).

## Previous Iteration: S2 PREP (researcher-1, 2026-05-16)

Doc-only S2 PREP closing two questions S1 OBSERVE explicitly deferred:

1. **Closing-lemma name pinned** (S1 §"Next Action" line ~146): the
   sketch's last step `hr_monic.eq_one_iff_natDegree_le_zero.mpr
   (le_of_eq hr_natdeg)` becomes `hr_monic.natDegree_eq_zero.mp
   hr_natdeg`. The canonical lemma at the pinned Mathlib commit is
   `Polynomial.Monic.natDegree_eq_zero : Monic p → (p.natDegree = 0 ↔
   p = 1)`. The S1 OBSERVE name (`eq_one_iff_natDegree_le_zero`) does
   not exist at the pin; the `natDegree_eq_zero_iff_eq_one` alias was
   deprecated on 2025-10-26 in favour of `natDegree_eq_zero` itself.
   See sessions/2026-05-16-s2-prep-… §1.

2. **Namespace decision** (S1 §"Next Action" line ~104): cannot reuse
   `GeneralCyclicVector` — that namespace is **Field-locked** at
   `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean:54`
   (`variable {K : Type*} [Field K]`). Modifying it upstream would
   blast-radius the 4 sibling gallery files. **Option A** (new
   namespace `GeneralCyclicVectorRing` inside the new file
   `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean`) is
   recommended over Options B (modify upstream — too invasive) and C
   (inline `private def` — harder to import for S3). See
   sessions/2026-05-16-s2-prep-… §2.

A refined S2 ACT skeleton (~46 LOC, post-S1+S2 corrections) is
drafted at sessions/2026-05-16-s2-prep-… §2.3, with 5 fallback
recipes for likely tactic stutters (§2.5). Bearer drift rechecked
against the unchanged Mathlib pin: 0 substantive drifts vs S1's
9-bearer audit, with **3 new bearer rows added**
(`Monic.natDegree_eq_zero`, `natDegree_le_of_dvd`, `zero_mulVec`).

## Latest Iteration: S1 OBSERVE (researcher-9, 2026-05-14)

Doc-only S1 OBSERVE iteration bootstrapping the slug from seeker stub
(phase NEW, knowledge score 0, "formal statement to be added") to a
complete survey with explicit backward/forward dichotomy.

### S1 Headline Finding

The biconditional **bifurcates** over commutative rings:

| Direction | Status over `CommRing R` |
|-----------|--------------------------|
| **Backward**: `(∃ v, IsCyclicVector M v) → IsNonderogatory M` | **Extends** to any nontrivial commutative ring. Single proof-tweak from the existing field-proof: replace `Polynomial.natDegree_mul` (needs domain) with `Polynomial.Monic.natDegree_mul'` (needs only one factor monic and the other nonzero). |
| **Forward**: `IsNonderogatory M → ∃ v, IsCyclicVector M v` | **Fails** over `ZMod 4` with explicit counterexample `M = !![0, 2; 0, 0]`. Status over integral domains and UFDs is open. |

### Counterexample sketch (full details in `knowledge.md`)

Take `R = ZMod 4`, `M = !![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 4)`.

- **`charpoly M = X^2`**: `M.charpoly = X^2 - tr(M)·X + det(M)·1 = X^2 - 0 - 0 = X^2`.
- **`minpoly (ZMod 4) M = X^2`**: `M^2 = 0` (so `X^2` annihilates), and
  no monic polynomial `X - c` of degree 1 annihilates `M` (because
  `M - cI = !![-c, 2; 0, -c] ≠ 0` for every `c : ZMod 4`, since the
  `[0,1]`-entry is `2 ≠ 0`).
- **`IsNonderogatory M`** holds (`minpoly = charpoly = X^2`).
- **No cyclic vector exists**: for every `v = (a, b) ∈ (ZMod 4)^2`, set
  `p := 2X` if `b ≠ 0`, or `p := X` if `b = 0`. Direct calculation:
  - `aeval M (2X) = 2M = !![0, 4; 0, 0] = !![0, 0; 0, 0] = 0` as a
    matrix (since `4 ≡ 0 mod 4`), so `(aeval M (2X)).mulVec v = 0` for
    any `v`. With `2X ≠ 0` and `natDegree (2X) = 1 < 2`, this witnesses
    `¬ IsCyclicVector M v` for every `v` with `b ≠ 0`.
  - For `b = 0`: `Mv = (0, 0)`, so `aeval M (X) v = M v = 0`, with
    `X ≠ 0` and `natDegree X = 1 < 2`, witnessing
    `¬ IsCyclicVector M v` for every `v` with `b = 0`.
- **Conclusion**: `IsNonderogatory M ∧ ¬ ∃ v, IsCyclicVector M v` —
  forward direction is false at `M`.

### Mathlib API Verification

All five Mathlib facts the existing field-proof uses have been confirmed
present at the pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
with their typeclass requirements relaxed enough to support
`[CommRing R]`:

| Mathlib name | Location | Suffices for backward direction? |
|--------------|----------|--------------------------------|
| `minpoly.monic` | `FieldTheory/Minpoly/Basic.lean:54` | ✓ `CommRing A` |
| `minpoly.ne_zero` | `FieldTheory/Minpoly/Basic.lean:60` | ✓ `CommRing A + Nontrivial A` |
| `minpoly.aeval` | `FieldTheory/Minpoly/Basic.lean:88` | ✓ `CommRing A` |
| `minpoly.dvd` | `FieldTheory/Minpoly/Basic.lean` (Ring section) | ✓ `CommRing A` |
| `Matrix.isIntegral` | `LinearAlgebra/Matrix/Charpoly/Minpoly.lean:44` | ✓ `CommRing R` |
| `Polynomial.Monic.natDegree_mul'` | `Algebra/Polynomial/Monic.lean:154` | ✓ `Semiring R` (replaces `Polynomial.natDegree_mul`) |
| `Polynomial.Monic.of_mul_monic_left` | `Algebra/Polynomial/Monic.lean:110` | ✓ `Semiring R` |
| `Matrix.charpoly_monic` | `LinearAlgebra/Matrix/Charpoly/Basic.lean` | ✓ `CommRing R + Nontrivial R` |
| `Matrix.charpoly_natDegree_eq_dim` | `LinearAlgebra/Matrix/Charpoly/Coeff.lean` | ✓ `CommRing R + Nontrivial R` |

Each verified by `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=<pin>` lookup against the gallery's
Mathlib pin.

### Deliverables in this iteration

1. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/problem.md`
   — full problem statement, three-approach decomposition, Mathlib API
   map. (~260 lines, doc-only.)
2. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/state.md`
   — this file.
3. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/knowledge.md`
   — S1 session note: counterexample worked example with `b = 0` /
   `b ≠ 0` case split, Mathlib pin verification log, domain-extension
   risk analysis.
4. `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01.json`
   — research registry update (phase `NEW` → `OBSERVE`, knowledge score
   `0` → roughly `14`, problem statement filled in).

**No Lean changes** in this S1 iteration. All four existing files in the
chain (`CayleyHamiltonCyclicVectorAllFields.lean`,
`CayleyHamiltonCyclicVectorAllFieldsAristotle.lean`,
`CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01.lean`,
`CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean`) are unmodified.

## Active Approach

**Approach A → B → (optional) C**: backward extension to `CommRing R`,
then `ZMod 4` counterexample formalisation, then optional UFD attempt
on forward direction. Detailed in `problem.md` §"Three Approaches".

## Blockers

None mathematical or practical for S2.

## Next Action

**S2 ACT (Approach A — backward extension)**: substantive Lean PR adding
`proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (~50 LOC):

1. Generalised definitions (`namespace GeneralCyclicVectorRing` or
   reuse parent's `GeneralCyclicVector` if its typeclass can be
   loosened — verify in S2 SCAFFOLD):
   ```lean
   def IsCyclicVector {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
       (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Prop :=
     ∀ p : R[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

   def IsNonderogatory {R : Type*} [CommRing R] {n : ℕ}
       (M : Matrix (Fin n) (Fin n) R) : Prop :=
     minpoly R M = M.charpoly
   ```

2. The backward theorem (mirror of `cyclic_implies_nonderogatory`):
   ```lean
   theorem cyclic_implies_nonderogatory_commring
       {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
       (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
       (hcyc : IsCyclicVector M v) :
       IsNonderogatory M := by
     unfold IsNonderogatory
     have hdvd : minpoly R M ∣ M.charpoly :=
       minpoly.dvd R M (Matrix.aeval_self_charpoly M)
     have hchar_monic : M.charpoly.Monic := Matrix.charpoly_monic M
     have hchar_deg : M.charpoly.natDegree = n := by
       rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
     have hle : (minpoly R M).natDegree ≤ n :=
       Polynomial.natDegree_le_of_dvd hdvd hchar_monic.ne_zero |>.trans_eq hchar_deg
     have hge : n ≤ (minpoly R M).natDegree := by
       by_contra hlt; push_neg at hlt
       have hann : (aeval M (minpoly R M)).mulVec v = 0 := by
         rw [minpoly.aeval]; exact Matrix.zero_mulVec v
       exact absurd (hcyc (minpoly R M) hlt hann)
         (minpoly.ne_zero (Matrix.isIntegral M))
     have hdeg : (minpoly R M).natDegree = n := Nat.le_antisymm hle hge
     obtain ⟨r, hr⟩ := hdvd
     have hmin_monic : (minpoly R M).Monic := minpoly.monic (Matrix.isIntegral M)
     have hr_monic : r.Monic := hmin_monic.of_mul_monic_left (hr ▸ hchar_monic)
     have hr_natdeg : r.natDegree = 0 := by
       have hmul := hmin_monic.natDegree_mul' hr_monic.ne_zero
       have hprod_deg : (minpoly R M * r).natDegree = n := by rw [← hr, hchar_deg]
       linarith [hdeg]
     -- S2 PREP correction: the canonical lemma at the pinned Mathlib commit is
     -- `Polynomial.Monic.natDegree_eq_zero`, not `eq_one_iff_natDegree_le_zero`.
     have hr_eq : r = 1 := hr_monic.natDegree_eq_zero.mp hr_natdeg
     rw [hr, hr_eq, mul_one]
   ```

   **Fallback (if `Monic.natDegree_eq_zero` is not in scope after `import Mathlib`):**
   use `Monic.degree_le_zero_iff_eq_one` (explicit at `Monic.lean:138` in the
   same file) with a `natDegree → degree` adapter:
   ```lean
     have hr_deg_le : r.degree ≤ 0 :=
       Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp hr_natdeg
     have hr_eq : r = 1 := hr_monic.degree_le_zero_iff_eq_one.mp hr_deg_le
   ```

3. Corollaries mirroring the field file's structure
   (`derogatory_has_no_cyclic_vector_commring`,
   `minpoly_natDegree_of_cyclic_commring`).

4. Docstring callout to the `ZMod 4` counterexample showing the
   forward direction does NOT extend, with a `#check
   CayleyHamiltonCyclicVectorZMod4Counterexample.no_cyclic_vector`
   stub for the S3 follow-up.

**Namespace decision (S2 PREP §2):** Cannot reuse parent's
`GeneralCyclicVector` namespace — it is Field-locked at
`Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean:54`
(`variable {K : Type*} [Field K]`). Use **Option A**: define new
namespace `GeneralCyclicVectorRing` inside the new file with
`[CommRing R] [Nontrivial R]` — orthogonal to upstream, zero
modification to the 4 existing sibling files. Refined drop-in
skeleton at sessions/2026-05-16-s2-prep-… §2.3 (~46 LOC).

Estimated effort for S2: 1 session, single PR, ~60 LOC of new Lean,
Docker build verification straightforward (no parent-file blockers in
chain at v4.26.0 per the existing OQ01OQ01 build history). No
dependencies beyond Mathlib.

## Future Iterations (Deferred)

**S3 (Approach B — counterexample formalisation)**: ~40 LOC,
`proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean`
formalising the `M = !![0, 2; 0, 0]` example with three theorems:

- `charpoly_eq_X_sq`: `M.charpoly = X^2`
- `minpoly_eq_X_sq`: `minpoly (ZMod 4) M = X^2`
- `no_cyclic_vector`: `¬ ∃ v, IsCyclicVector M v`

Combined with S2's `cyclic_implies_nonderogatory_commring` and the
parent's `IsNonderogatory` definition, this provides a fully verified
witness that the **forward direction of the biconditional is false
over `ZMod 4`**, settling the OQ negatively over non-domains.

**S4 (Approach C — optional UFD extension of forward direction)**:
attempt to generalise the parent file
`CayleyHamiltonCyclicVectorAllFields.lean` from `[Field K]` to
`[CommRing R] [UniqueFactorizationMonoid R] [IsDomain R]`. Higher risk,
~150-300 LOC; defer until S2+S3 land.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE + S2 PREP, this iteration)
- Current approach attempts: 0 (no Lean changes yet)
- Approaches tried: 0 (3 surveyed: A=backward over CommRing,
  B=ZMod 4 counterexample, C=UFD forward extension)

## Ledger (S1 → S2)

| PR     | Iter | Date / UTC          | Author        | Phase / scope                                                                          |
|--------|-----:|---------------------|---------------|----------------------------------------------------------------------------------------|
| #19139 |   1  | 2026-05-15 22:57    | researcher-9  | S1 OBSERVE — slug bootstrap; backward/forward dichotomy; ZMod 4 counterexample; 9-bearer Mathlib API map (doc-only) |
| (this) |   2  | 2026-05-16 ~00:15   | researcher-1  | S2 PREP — `Monic.natDegree_eq_zero` bearer pin + `GeneralCyclicVectorRing` namespace decision (Option A); refined ~46-LOC S2 ACT skeleton (doc-only) |

Both S1 and S2 are doc-only; no Lean changes. S2 ACT (Approach A,
the backward-direction Lean diff) is the next concrete action.

## Open files

- `problem.md` — full problem statement, three approaches, Mathlib API map.
- `knowledge.md` — S1 session note: counterexample case split,
  Mathlib pin verification, domain-extension analysis.
- `state.md` — this file (refreshed S2).
- `sessions/2026-05-16-s2-prep-monic-bearer-pin-and-namespace-decision.md` — added by this PR.

## S1 Deliverable Honesty Summary

This iteration is **survey-only**:

- 0 new Lean theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified
- Build pending (no Lean delta to verify)

Produced:

- `problem.md` (~260 lines)
- `state.md` (this file)
- `knowledge.md` (counterexample case analysis)
- `src/data/research/problems/<slug>.json` (registry update)

This is a doc-only `*-OBSERVE` PR per the precedent of
`bezout-identity-oq-01-oq-01-oq-01-oq-01` (PR #17990) and
`lagrange-theorem-oq-01-oq-01-oq-01` S1 (PR #17782).
