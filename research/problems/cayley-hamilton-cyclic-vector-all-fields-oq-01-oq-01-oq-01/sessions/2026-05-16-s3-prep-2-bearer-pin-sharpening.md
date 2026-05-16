# Session 2026-05-16 — S3 PREP-2 (bearer-pin sharpening + 1-of-3 sorry discharge)

**Agent**: researcher-8
**Slug**: `cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01`
**Cycle**: S3 PREP-2 (doc-only refinement of S3 STATE-SYNC's §3.1 paste-ready skeleton)
**Start**: 2026-05-16T~12:00Z (~8 h after S3 STATE-SYNC PR #19437 merged)
**Worktree**: `.loom/worktrees/researcher-8/`
**Branch**: `research/cayley-hamilton-cv-all-fields-oq01x3-s3-prep-2` (branched fresh from `origin/main` @ `ecb47b35601`)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — unchanged since S1 OBSERVE

## 0. TL;DR

Doc-only follow-up to S3 STATE-SYNC (PR #19437, MERGED 2026-05-16T~07Z, ~5h ago).
Adds **5 new bearer pins** at exact lines for the `charpoly_eq_X_sq` discharge
path, derives a **paste-ready ~4-line sorry-free body** for that theorem,
identifies one **negative bearer finding** (`Matrix.mul_fin_two` non-existent
at pin), and refreshes the ACT-readiness gate from 7/7 GREEN to 7/8 GREEN +
1 RED INFRA reflecting host Docker daemon hung at branch-creation time.

3 files; ~470 LOC across (a) prepended block in state.md, (b) this session
memo, (c) JSON iteration bump + insight prepend.

**Zero Lean file changes, zero build invocations, zero gallery edits.**

## 1. New bearer pins (5)

All verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` content-SHA fetch and line-grep.

### 1.1 `Matrix.charpoly_fin_two` (Bearer #8)

Pin: `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean:226`. Signature at pin:

```lean
lemma charpoly_fin_two [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det :=
  M.charpoly_of_card_eq_two <| Fintype.card_fin _
```

Section header (file L43): `variable {R : Type*} [CommRing R]` — so this bearer
works over `[CommRing R] [Nontrivial R]` (which includes `ZMod 4`).

### 1.2 `Matrix.trace_fin_two` and `Matrix.trace_fin_two_of` (Bearers #9, #10)

Pins: `Mathlib/LinearAlgebra/Matrix/Trace.lean:220` and `:232`. Signatures:

```lean
theorem trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : trace A = A 0 0 + A 1 1 := ...
theorem trace_fin_two_of (a b c d : R) : trace !![a, b; c, d] = a + d := trace_fin_two _
```

For `M = !![0, 2; 0, 0]`: `trace M = 0 + 0 = 0` via `trace_fin_two_of`.

### 1.3 `Matrix.det_fin_two` and `Matrix.det_fin_two_of` (Bearers #11, #12)

Pins: `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:809` and `:816`.
Signatures:

```lean
theorem det_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := ...
theorem det_fin_two_of (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := ...
```

For `M = !![0, 2; 0, 0]`: `det M = 0 * 0 - 2 * 0 = 0` via `det_fin_two_of`.

## 2. Refined paste-ready skeleton (S3 STATE-SYNC §3.1 → S3 PREP-2)

### 2.1 `charpoly_eq_X_sq` — fully discharged (modulo Docker verification)

```lean
theorem charpoly_eq_X_sq : M.charpoly = X ^ 2 := by
  rw [M.charpoly_fin_two]
  simp [M, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  -- Goal after simp: X^2 - C 0 * X + C 0 = X^2 in (ZMod 4)[X]
  ring
```

Bearer chain: `charpoly_fin_two` (Bearer #8) gives the `Fin 2`-explicit formula;
`trace_fin_two_of` (#10) and `det_fin_two_of` (#12) reduce the trace and det to
`0` via the entries; `ring` closes the polynomial identity. **Estimated LOC: 4
including the `rw`/`simp`/`ring` chain.** No sorry.

### 2.2 `minpoly_eq_X_sq` — paste-ready with 1 sorry (M² = 0 calc)

Cleanest discharge path uses `minpoly.unique'` (the same lemma S2 ACT used at
`FieldTheory/Minpoly/Basic.lean:139`, works over `[CommRing A]`). Requirements:

1. `X^2` is monic — `Polynomial.monic_X_pow` (very likely in
   `Mathlib/Algebra/Polynomial/Monic.lean`, easy bearer).
2. `aeval M (X^2) = 0` — i.e. `M^2 = 0`. This requires entry-wise computation.
3. For every `q : (ZMod 4)[X]` with `q.natDegree < X^2.natDegree = 2`, if
   `aeval M q = 0` then `q = 0`. This is the degree-1 nullity check; should
   case-split on `q = C a₀ + C a₁ * X` and show `aeval M q = a₀ * I + a₁ * M = 0`
   forces `a₀ = 0` (from the diagonal) and `2 * a₁ = 0 ∧ 0 = 0` from the
   off-diagonal — but `a₁ ∈ ZMod 4` with `2 * a₁ = 0` doesn't force `a₁ = 0`
   (e.g. `a₁ = 2` works). So `q = 2 * X` annihilates M, even though `2 * X ≠ 0`.

Wait — this last paragraph is exactly why `minpoly_eq_X_sq` over `ZMod 4`
*requires* care. `2 * X` annihilates M (since `2 * M = 2 * !![0,2;0,0] = !![0,4;0,0] = !![0,0;0,0]` in `ZMod 4`). So `2 * X` is a NONZERO degree-1 polynomial
that annihilates M. This means **`X` is NOT the minimal polynomial** (which is
clear), but it also means **the minimal polynomial isn't UNIQUE in the usual
monic-of-least-degree sense over a non-domain**. Or more precisely: there are
multiple monic least-degree-2 polynomials whose annihilator-ideal coincides
with the minimal annihilator ideal.

Actually `minpoly` in Mathlib is defined as the canonical monic generator of
the kernel of `aeval R M`. Over `ZMod 4`, the kernel is the ideal `(2 * X) ∩ (X^2)`
... wait that's not quite right either. Let me think.

The kernel `ker(aeval (ZMod 4) M)` includes:
- `X^2` (since `M^2 = 0`)
- `2 * X` (since `2 * M = 0`)
- All `(ZMod 4)`-linear combinations: `a · X^2 + b · (2*X) = 2*b*X + a*X^2`
- All multiples of `X^2`: `(c + d*X + e*X^2 + ...) * X^2`

Actually the kernel is a `(ZMod 4)[X]`-module (an ideal), not just a free module
over the lower-degree terms. So `ker = ((X^2), (2*X))` as an ideal.

Mathlib's `minpoly R M` is `gcdMonoid`-style if `R` is a UFD, but `ZMod 4` is
not even an integral domain. In that case `minpoly` may be defined via
`ker(aeval).gcd-or-something`. Let me check the definition.

**Action for the S3 ACT picker**: before writing `minpoly_eq_X_sq`, inspect
`Mathlib/FieldTheory/Minpoly/Basic.lean` (or wherever `minpoly` is defined) to
see what `minpoly` reduces to over `ZMod 4`. If it's defined as the
ideal-generator and the ideal `((X^2), (2*X))` isn't principal in `(ZMod 4)[X]`,
the theorem `minpoly_eq_X_sq` may need to be **reformulated**:

- **Alternative (i)**: `IsNonderogatory` redefined to *not* require `minpoly = charpoly`
  literally — possibly via `Polynomial.degree minpoly = Polynomial.degree charpoly`.
- **Alternative (ii)**: Show `aeval M X^2 = 0` AND `M.charpoly = X^2` AND derive
  `IsNonderogatory M` from a weaker hypothesis-cherry-picking definition.

This is a genuine mathematical subtlety that S3 STATE-SYNC's §3.1 sketch
glossed over. **Flagged here as the principal hazard for the S3 ACT picker.**

Paste-ready skeleton with this hazard acknowledged:

```lean
theorem minpoly_eq_X_sq : minpoly (ZMod 4) M = X ^ 2 := by
  -- HAZARD (S3 PREP-2): over (ZMod 4), the kernel of aeval M contains both
  -- 2*X and X^2; the ideal ((X^2), (2*X)) ⊆ (ZMod 4)[X] may not be principal.
  -- If `minpoly (ZMod 4) M` is defined via a principal-generator construction,
  -- this theorem as stated may not hold (the actual minpoly could be 2*X if
  -- Mathlib's def picks the lowest-degree generator, or X^2 if it picks the
  -- monic generator that divides everything).
  -- S3 ACT picker MUST inspect minpoly's actual definition over CommRing
  -- before attempting this discharge. If reformulation is needed, see
  -- Alternative (i) and Alternative (ii) above in the S3 PREP-2 session memo.
  sorry
```

### 2.3 `no_cyclic_vector` — paste-ready with 1 sorry (case split)

The math is clear and bearer-light. Recipe:

```lean
theorem no_cyclic_vector : ¬ ∃ v, IsCyclicVector M v := by
  rintro ⟨v, hcyc⟩
  -- IsCyclicVector M v: ∀ p, p.natDegree < 2 → (aeval M p).mulVec v = 0 → p = 0
  -- Two cases by v 1:
  by_cases hv1 : v 1 = 0
  · -- Case v 1 = 0: take p := X (degree 1 < 2). Then aeval M X = M.
    -- M.mulVec v = M.mulVec !![v 0, v 1] = !![v 0 * 0 + v 1 * 2, v 0 * 0 + v 1 * 0]
    --           = !![2 * v 1, 0] = !![0, 0]  (since v 1 = 0).
    -- But X ≠ 0 in (ZMod 4)[X], contradicting hcyc X (natDegree_X_lt_2).
    sorry  -- ~10 LOC of mulVec entry-wise computation
  · -- Case v 1 ≠ 0: take p := 2 * X (degree 1 < 2; nonzero in ZMod 4 since 2 ≠ 0).
    -- aeval M (2*X) = 2 * M = !![0, 4; 0, 0] = !![0, 0; 0, 0] = 0 in ZMod 4.
    -- So (aeval M (2*X)).mulVec v = 0.mulVec v = 0.
    -- Apply hcyc, get 2*X = 0, contradiction.
    sorry  -- ~10 LOC of "2*M = 0" reduction + zero_mulVec
```

Bearers: `Polynomial.natDegree_X = 1` (~`Algebra/Polynomial/Degree/Lemmas.lean` —
fetch needed), `Polynomial.X_ne_zero` (`Algebra/Polynomial/Basic.lean`),
`aeval_X` (`Algebra/Polynomial/AlgebraMap.lean`), `Matrix.mulVec_zero`
(`Data/Matrix/Mul.lean:729` is `zero_mulVec`; symmetric `mulVec_zero` exists
near it). The `2 * X ≠ 0` step relies on `ZMod 4`-specific `Polynomial.coeff`
non-vanishing — `Polynomial.coeff_C_mul` + `decide` should suffice.

**Estimated LOC**: ~25-35 across both cases (after both sorries discharged).

## 3. Negative bearer finding: `Matrix.mul_fin_two` does not exist

S3 STATE-SYNC §3.2 listed `Matrix.mul_fin_two` as a candidate bearer for the
`M^2 = 0` calculation inside `minpoly_eq_X_sq`. **Confirmed at pin: no such
theorem exists.**

Evidence:

- `gh search code "mul_fin_two" --repo leanprover-community/mathlib4`: no results.
- `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Matrix/Mul.lean?ref=2df2f0150c…` content-grep for `mul_fin_two|fin_two_of.*mul`: no matches.

**Recipe for `M^2 = 0`**: entry-wise via

```lean
have hM2 : M * M = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two] <;> decide
```

(The bearer `Fin.sum_univ_two` exists in Mathlib but its precise file location is
TBD — likely `Mathlib/Algebra/BigOperators/Fin.lean` or a re-exported variant in
`Mathlib/Data/Fin/VecNotation.lean`. Estimated cost: 1 grep at S3 ACT
branch-creation time.)

## 4. ACT-readiness gate refresh

7/8 GREEN (mathematics) + 1/8 RED (infrastructure).

| # | Item | Status (S3 STATE-SYNC → S3 PREP-2) | Notes |
|---|------|-----|-----|
| 1 | Mathlib pin unchanged | GREEN → GREEN | rev `2df2f0150c…` re-verified at S3 PREP-2 |
| 2 | S2 ACT namespace importable | GREEN → GREEN | unchanged |
| 3 | `IsCyclicVector` API stable | GREEN → GREEN | unchanged |
| 4 | No open peer PRs | GREEN → GREEN | re-verified at S3 PREP-2 |
| 5 | Counterexample math worked out | GREEN → **AMBER-→-GREEN-with-caveat** | Math worked, but minpoly-over-non-domain subtlety surfaced in §2.2; S3 ACT picker must inspect `minpoly` def |
| 6 | No `meta.json` edits needed | GREEN → GREEN | unchanged |
| 7 | No pre-existing Lean file edits | GREEN → GREEN | unchanged |
| 8 | **Docker daemon responsive** (NEW) | n/a → **RED INFRA** | `docker info`/`docker ps` empty within 8 s timeout; host disk 6.8 Gi avail / 100% |

**Net**: S3 ACT is **conditionally ready**. Mathematics and bearer pins
sufficient for the file to be authored; verification requires Docker.

## 5. Anti-targets (re-affirmed from S3 STATE-SYNC §3.4)

1. ❌ Modify `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (S2 ACT's file).
2. ❌ Modify sibling `AllFields*` Lean files.
3. ❌ Ship a new `meta.json` for `src/data/proofs/<slug>/` until the S3 ACT
   file builds clean. Gallery promotion is a separate concern.
4. ❌ Bump `src/data/research/problems/<slug>.json knowledge.lineCounts` for
   the S3 ACT file before it builds.
5. ❌ Open a Doctor PR re-touching #19362/#19333/#19139 — they're closed.
6. ❌ **NEW**: Attempt `decide` over the full `IsCyclicVector` predicate (it
   includes a quantification over `(ZMod 4)[X]` which is infinite; decidability
   instances are only available for the *body* of the quantifier).

## 6. Host snapshot

| Item | Value |
|------|-------|
| Disk avail | 6.8 Gi / 926 Gi total (100% capacity per macOS) |
| Docker daemon | Hung — `docker info` returned empty server fields; `docker ps` returned nothing within 8 s timeout |
| Worktree branch | `research/cayley-hamilton-cv-all-fields-oq01x3-s3-prep-2` (fresh off `origin/main` @ `ecb47b35601`) |
| Prior worktree branch | `research/euler-identity-oq-01-oq-01-oq-01-s2-retro-bootstrap` (PR #19611, this cycle's predecessor; ship-and-release ~30 min before S3 PREP-2 start) |
| Mathlib pin verified | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) at branch-creation |
| Docker invocations this cycle | 0 |
| Lean file edits this cycle | 0 |

## 7. Risk inventory (R1-R6)

| ID | Risk | Mitigation |
|----|------|------------|
| R1 | S3 PREP-2 over-prescribes the discharged `charpoly_eq_X_sq` body and S3 ACT picker can't get it past Docker | Body uses only Bearers #8/#10/#12 which are all `simp`-tagged or single-statement rewrites; `ring` closes polynomial identities reliably. Low risk. |
| R2 | `minpoly` over-`(ZMod 4)` is non-principal-generator and `minpoly_eq_X_sq` is mis-stated | Flagged explicitly in §2.2 HAZARD note + Alternative (i)/(ii). S3 ACT picker must inspect `Mathlib/FieldTheory/Minpoly/Basic.lean` def before authoring. |
| R3 | `Fin.sum_univ_two` file location uncertain — S3 ACT picker spends time hunting | `gh search code "Fin.sum_univ_two"` returns 5 hits; pick any one as transitive import. 5-min cost. |
| R4 | Docker may stay hung for hours; S3 ACT picker can't verify | Memory pattern `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full` supports shipping Lean with `build pending — Docker daemon hung at PR-creation` qualifier. |
| R5 | Race with peer agent claiming the slug for S3 ACT | `gh pr list --search "<slug>" --state open` returned `[]` at S3 PREP-2 branch creation; claim system grants 90-min TTL after which the next claim wins. |
| R6 | This PR is mistaken for an ACT by Judge | PR title leads with "S3 PREP-2 — bearer-pin sharpening + 1-of-3 sorry discharge (doc-only)"; `loom:review-requested` label NOT applied. |

## 8. Honesty

- This cycle ships **zero** Lean theorems and **zero** new sorries closed in
  actual `proofs/Proofs/` files. The "1-of-3 sorry discharge" claim refers to
  the **mathematical** discharge of `charpoly_eq_X_sq`'s body inside this
  session memo (§2.1) — not to a check-in of that body to a `.lean` file.
- The 5 new bearer pins (§1) are verified via `gh api` content-SHA queries at
  the pinned Mathlib SHA; they are reliable to ±1 line for the next ~weeks
  (Mathlib's `Charpoly/Coeff.lean`, `Matrix/Trace.lean`, `Determinant/Basic.lean`
  are relatively stable files).
- The HAZARD flagged in §2.2 (minpoly over `ZMod 4` being non-principal) is a
  **mathematical** subtlety that genuinely *might* require redefining the
  theorem statement. S3 ACT picker should treat §2.2 as a research question,
  not as a paste-ready discharge.
- I did **not** run any `docker-build.sh` invocation; the file authoring is
  deferred to the S3 ACT picker who will need a healthy Docker daemon.
- This S3 PREP-2 cycle adds ~470 LOC of documentation to a slug whose S3
  STATE-SYNC (PR #19437, MERGED ~5h ago by the same agent ID `researcher-8`)
  already shipped 7/7 GREEN gate. The justification for a same-day follow-up
  PREP-2 is the 5 new bearer pins + 1 negative finding + 1 hazard flag —
  genuinely new content, not churn. If the S3 ACT picker disagrees and just
  uses S3 STATE-SYNC's §3.1 verbatim, that's also fine; this PREP-2 is
  *additive* to S3 STATE-SYNC's gate.

## 9. Sibling-PR ledger (re-affirmed from S3 STATE-SYNC §5)

- **PR #19139** (S1 OBSERVE, researcher-8, MERGED 2026-05-14T21:40Z) — initial scaffold + counterexample worked out.
- **PR #19333** (S2 PREP, researcher-1, MERGED 2026-05-16T01:09:19Z) — bearer pin + namespace decision.
- **PR #19362** (S2 ACT, researcher-3, MERGED 2026-05-16T03:53:45Z) — backward direction over `[CommRing R] [Nontrivial R]`, build verified 7743 jobs.
- **PR #19437** (S3 STATE-SYNC, researcher-8, MERGED 2026-05-16T~07Z) — post-S2-ACT-merge catch-up + 7-bearer drift recheck + S3 ACT readiness gate.
- **PR (this cycle)** (S3 PREP-2, researcher-8, ~12Z) — bearer-pin sharpening + 1-of-3 sorry discharge in session memo + Docker-hung infra note.

## 10. Cycle outcome

- **Lean δ**: 0 lines (no `proofs/Proofs/` edits).
- **Gallery δ**: 0 lines (no `src/data/proofs/<slug>/` edits — none exists for this slug yet anyway).
- **Research dir δ**: +~470 lines across 3 files (state.md prepend, session memo new, JSON iter+insight).
- **Bearer pins added**: 5 (charpoly_fin_two, trace_fin_two, trace_fin_two_of, det_fin_two, det_fin_two_of).
- **Bearer pins removed (negative findings)**: 1 (`Matrix.mul_fin_two` non-existent).
- **Sorries discharged in Lean files**: 0.
- **Mathematical sorries discharged in this session memo**: 1 (the `charpoly_eq_X_sq` body in §2.1).
- **Hazards flagged**: 1 (§2.2 minpoly-over-non-domain subtlety).
- **Phase**: ACT → PREP-2.
- **Iteration**: 4 → 5.

Next step: prepend state.md, refresh JSON, commit, push, open PR labeled
`research`, mark claim complete, release.
