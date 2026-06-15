# Knowledge Base: sqrt2-minpoly-oq-01-oq-02

**Question**: Prove `minpoly ℚ (√(p/q)) = q X² − p` (monic form `X² − p/q`) for non-square
positive rationals `p/q`, plus the irrationality corollary.

**Source**: open question on `sqrt2-minpoly-oq-01` (parent proves `minpoly ℚ (√n) = X² − n`
for all non-perfect-square naturals `n`).

---

## Status: ACT — content drafted, build-pending (Docker host saturated)

New file `proofs/Proofs/Sqrt2MinpolyOQ01OQ02.lean` (0 sorries, 0 axioms), UNREGISTERED.

## Key finding (the reduction)

The parent's Part VII theorem `minpoly_sqrt_of_not_sq` (natural-number radicand) ports to
rational radicands **near-verbatim**. The only naturality used in the parent proof is:
1. `(√n)² = n` via `Real.sq_sqrt` — works for any real `≥ 0`, in particular `(r : ℝ)` for
   `r : ℚ`, `0 ≤ r`.
2. irrationality of `√n` — replaced by the hypothesis `Irrational (√r)`, which is itself
   characterized (`irrational_sqrt_rat_iff`) as "`r` is not the square of a rational".

Every other step (monic, degree ≤ 2 via `minpoly.dvd` + `natDegree_le_of_dvd`, degree ≥ 2
from irrationality, equal-monic-degree-2-divisor conclusion) is generic over ℚ coefficients
and copied unchanged.

## Declarations added

- `irrational_sqrt_rat_of_not_square (r hr hns)`: `0 ≤ r`, `¬∃s, s²=r` ⟹ `Irrational (√r)`.
  Proof: if `√r = ↑a` then `a² = r` (square both sides, `Real.sq_sqrt`), contradicting `hns`.
- `irrational_sqrt_rat_iff (r hr)`: the full iff. mpr is the lemma above; mp uses
  `Real.sqrt_sq_eq_abs` (`r = s² ⟹ √r = |s| ∈ ℚ`).
- `minpoly_sqrt_rat (r hr hirr)`: **main**, `minpoly ℚ (√r) = X² − C r`.
- `minpoly_sqrt_rat_of_not_square`: convenience taking the non-square hypothesis directly.
- `minpoly_sqrt_div_integer_form (p q : ℤ) (hq : 0<q) …`: the headline integer form
  `C q * minpoly = C q * X² − C p`, via `mul_sub` + `← C_mul` + `q·(p/q)=p` (`field_simp`).
- `example`: recovers parent `minpoly ℚ (√2) = X² − 2` through the rational theorem.

## Why no build this session

Docker VM has ~7.65 GiB total RAM (host 96GB); 4–5 concurrent `lean-build` containers were
running all session. Building a 6th risks OOMing all peers (see memory
`project-docker-7gb-vm-is-the-real-oom-constraint`). Proof is a high-confidence verbatim port
of an already-compiling theorem, so shipped build-pending. Aristotle not used (no sorries).

## Next steps

1. Docker-up session: `./proofs/scripts/docker-build.sh Proofs.Sqrt2MinpolyOQ01OQ02`, fix any
   API drift (likely candidates: `norm_cast` on `((|s|:ℚ):ℝ)=|↑s|`, the `push_cast` in
   `hXn_aeval`), then register in `proofs/Proofs.lean` (alongside the other Sqrt2Minpoly OQs).
2. Create gallery entry `src/data/proofs/sqrt2-minpoly-oq-01-oq-02/` once verified.
3. Possible follow-up OQ: drop the `0 ≤ r` hypothesis is impossible (`√` of negative is 0 in
   Lean's `Real.sqrt`); instead generalize to `minpoly ℚ (√d)` for `d` an algebraic integer in
   a real quadratic field — but that is the `Zsqrtd` territory already partly covered elsewhere.
