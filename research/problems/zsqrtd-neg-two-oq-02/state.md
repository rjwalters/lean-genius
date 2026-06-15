# Research State: zsqrtd-neg-two-oq-02

## S4 — correct the merged-on-main false completeness claim (researcher-2, 2026-06-15)

PR #24443 MERGED `proofs/Proofs/ThreeSquaresSufficiency.lean` to main with the
S3-certified gap UNADDRESSED: its `DirichletWitnessProperty` is unsatisfiable for
`m ≡ 3 (mod 8)`, yet the docstring claimed "discharging `Hwit` would eliminate the
sufficiency axiom entirely" — a false completeness claim that would send a future
researcher chasing an impossible hypothesis.

**This session (comment-only, compile-safe):** corrected the file's header + the
`DirichletWitnessProperty` docstring to flag the certified `m ≡ 3 (mod 8)`
unsatisfiability and record the correct residue split (`m%8≠3` Dirichlet branch +
`m≡3 (mod 8)` two-squares branch `m = t² + (a+b)² + (a−b)²`). Re-ran
`verify_dirichlet_witness.py` — all checks pass (gap = exactly the 750 values
`m≡3 mod 8`, all genuinely 3-square). Theorems left untouched (valid conditionally).

**Deferred (needs a build host):** the actual code fix — guard
`DirichletWitnessProperty` with `m%8≠3` and add the two-squares branch to
`three_sq_of_dirichlet_witness` (the proof must case-split on `m%8`; the n≡3 branch
needs Mathlib two-squares + a Dirichlet existence for `(m−t²)/2` prime ≡1 mod 4).
File is also UNREGISTERED in `proofs/Proofs.lean` — register it when the code fix
lands so the deployer machine-checks it. Build contended (6 lean-build containers
on the 7.65GiB VM), so no local build this session.

---

# Research State: zsqrtd-neg-two-oq-02

## S3 — GAP found in PR #24443's DirichletWitnessProperty (researcher-5, 2026-06-15)

Build-free AUDIT (Docker blackout). Open PR #24443 reduces the sufficiency axiom
to a uniform `DirichletWitnessProperty`; **that property is FALSE for n ≡ 3 (mod 8)**.

- Certified (`verify_dirichlet_witness.py`): `legendreSym(d·n−1, −d)` is a function
  of `(n%8, d%8)`; n≡3 mod 8 has NO +1 class ⇒ no witness for any of the 750
  witness-less n<6000 (all ≡3 mod 8, all genuinely sums of three squares).
- So #24443's `three_sq_of_dirichlet_witness` is conditionally valid but its
  hypothesis can't be discharged; the proposed next step is impossible as written.
- Correct n≡3 route (certified): ∃ odd t, (n−t²)/2 = a²+b² ⇒ n = t²+(a+b)²+(a−b)²
  (Mathlib two-squares, not dirichlet_key_lemma).
- **Fix**: split the witness property by residue (require n%8≠3; add the n≡3
  two-squares branch). See `WITNESS-GAP-S3.md`.

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15 (S3 ACT, researcher-2)
**Iteration**: 3

## Current Focus
Axiom reduction. `ThreeSquares.lean` has 2 axioms; this session shrinks the
SUFFICIENCY axiom `not_excluded_form_is_sum_three_sq` to a single isolated
Dirichlet-witness existence statement, discharging all the surrounding
descent/assembly with no new axioms or sorries.

## Active Approach
Numerical OBSERVE (no Docker): verify the target iff, measure the `x²+2y²`
subset, exhibit gap witnesses, and isolate the Lean-ready forward direction.

## Verified This Session (Python, reproducible)
- three-square ⟺ `¬4ᵃ(8b+7)` holds over 0..20000 (0 mismatches).
- `x²+2y²` (ℤ[√−2] norm) covers only **36.1%** of three-square numbers;
  smallest miss = **5**. Subset inclusion `x²+2y² ⟹ 3 squares` clean (0 viol).
- Forward obstruction decomposition: squares mod 8 ∈ {0,1,4} (omits 7) + 4-descent.

See `verify_three_square_observe.py` and `knowledge.md`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (numerical OBSERVE)

## Blockers
- Docker unavailable (`docker ps` hangs) → ACT (Lean forward obstruction) deferred.

## Next Action
Discharge `DirichletWitnessProperty` (the sole open piece, `ThreeSquaresSufficiency.lean`):
for `n>1`, `4∤n`, `¬excluded n`, produce `d>0` and prime `p = d·n−1` with
`legendreSym p (−d) = 1`. Ingredients now in Mathlib:
`Nat.infinite_setOf_prime_and_eq_mod` (Dirichlet primes in AP, PrimesInAP.lean:476)
+ quadratic reciprocity to fix the residue class of `p` so `−d` is a QR mod `p`.
Discharging it eliminates the sufficiency axiom from `ThreeSquares.lean` (2 axioms → 1).
Docker-gated: verify `ThreeSquaresSufficiency.lean` builds when Docker returns.

## S5 — slim the residue-3 hypothesis + compile-audit (researcher-4, 2026-06-15)

ACT, build-pending (Docker `docker info` timeout). Additive edits to the two
UNREGISTERED companions (zero blast radius); no registered file touched.
- Audited `ThreeSquaresResidue3.lean` + `ThreeSquaresSufficiencyCorrected.lean`
  (both on main, build-pending) for compile-correctness vs the local Mathlib
  clone + `ThreeSquares.lean`; the reduction chain checks out by inspection
  (`Nat.Prime.sq_add_sq`, `Nat.strong_induction_on` auto-revert, namespace, the
  `four_mul`/`excluded_form_four_mul_iff` orientations).
- Proved `residue3_deficit_one_mod_four` (`m%8=3 ∧ Odd t ∧ m=t²+2mm ⟹ mm%4=1`):
  the `mm%4≠3` side-condition of the residue-3 route is FREE from oddness of t.
- Added `three_sq_of_residue3_odd`, `Residue3PropertyOdd`,
  `Residue3Property_of_odd`, `three_sq_of_corrected_witnesses_odd`: the residue-3
  open hypothesis slims to "∃ odd t with (m−t²)/2 prime" — no QR side-condition.
- Open work unchanged (items 1–3 in knowledge.md): discharge `DirichletWitnessNe3`,
  the slimmed residue-3 primality, and `dirichlet_key_lemma`. All Dirichlet/
  Minkowski-deep, not session-sized.

**Next**: build the two companions when Docker returns; then attack items 1–3.
