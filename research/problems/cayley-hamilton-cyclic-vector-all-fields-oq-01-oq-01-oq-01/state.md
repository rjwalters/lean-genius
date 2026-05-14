# Current State

**Phase**: OBSERVE (S1 — slug bootstrap with backward/forward dichotomy)
**Since**: 2026-05-14
**Iteration**: 1

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
     have hr_eq : r = 1 := hr_monic.eq_one_iff_natDegree_le_zero.mpr (le_of_eq hr_natdeg)
     -- (the last line may need `Monic.eq_one_iff_natDegree_le_zero` or
     -- equivalent; S2 SCAFFOLD will pin the exact lemma name.)
     rw [hr, hr_eq, mul_one]
   ```

3. Corollaries mirroring the field file's structure
   (`derogatory_has_no_cyclic_vector_commring`,
   `minpoly_natDegree_of_cyclic_commring`).

4. Docstring callout to the `ZMod 4` counterexample showing the
   forward direction does NOT extend, with a `#check
   CayleyHamiltonCyclicVectorZMod4Counterexample.no_cyclic_vector`
   stub for the S3 follow-up.

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

- Total attempts: 1 (S1 OBSERVE, this iteration)
- Current approach attempts: 0 (no Lean changes yet)
- Approaches tried: 0 (3 surveyed: A=backward over CommRing,
  B=ZMod 4 counterexample, C=UFD forward extension)

## Open files

- `problem.md` — full problem statement, three approaches, Mathlib API map.
- `knowledge.md` — S1 session note: counterexample case split,
  Mathlib pin verification, domain-extension analysis.

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
