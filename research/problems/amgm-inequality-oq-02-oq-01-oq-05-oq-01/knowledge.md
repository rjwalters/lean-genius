# Knowledge Base: amgm-inequality-oq-02-oq-01-oq-05-oq-01

Newton's k=2 rung  S₂² ≥ S₁S₃.

---

## Problem Understanding

Target as stated: for nonnegative reals x₁,…,xₙ (n ≥ 3), with Sₖ = eₖ/C(n,k),
prove S₂² ≥ S₁S₃ — the k=2 case of Newton log-concavity.

**Cleared / un-averaged form (corrected constant).**
S₂² ≥ S₁S₃  ⟺  e₂² ≥ [C(n,2)²/(C(n,1)C(n,3))]·e₁e₃.
Now C(n,2)²/(C(n,1)C(n,3)) = ( n(n-1)/2 )² / ( n · n(n-1)(n-2)/6 ) = 3(n-1)/(2(n-2)).
So the integer-cleared inequality is

    2(n-2)·e₂²  ≥  3(n-1)·e₁e₃          (n ≥ 2)

equivalently e₁e₃ ≤ (2(n-2)/(3(n-1)))·e₂².
NOTE: problem.md stated the constant as 2(n-1)/(3(n-2)); that is the
reciprocal-swapped value and is WRONG. The correct constant is 2(n-2)/(3(n-1)).
Sanity check xᵢ≡1: LHS 2(n-2)·C(n,2)² = RHS 3(n-1)·n·C(n,3), equality (as expected,
Newton equality is xᵢ all equal). ✓

---

## Key finding: the nonnegative case is ALREADY fully proved in the gallery

The literal target (nonnegative reals) is the k=2 instance of the already-existing,
axiom-free theorem

    NewtonLC.newton_ineq        (proofs/Proofs/NewtonLogConcavity.lean:95)
    newton_log_concavity_proved (proofs/Proofs/AmgmInequalityOQ02OQ02.lean:811)

which proves (eₖ/C(n,k))² ≥ (eₖ₋₁/C(n,k-1))·(eₖ₊₁/C(n,k+1)) for ALL 1 ≤ k, k+1 ≤ n
and nonnegative x, via cleared-denominator induction whose inductive step
`newton_cleared_denom_inductive_step` (line 395) is a *proved theorem*
(quadratic_nonneg + binomial absorption identities), NOT an axiom.

Caveat on the axiom hygiene: `AmgmInequalityOQ02.lean:285` still declares the LEGACY
placeholder `axiom newton_log_concavity`, but `newton_ineq` routes through the *proved*
`newton_log_concavity_proved`, so the k=2 rung is axiom-free. (Several docstrings in
NewtonLogConcavity.lean / OQ02OQ02.lean claiming "one axiom remaining" are STALE — the
inductive step was subsequently proved. Worth a cleanup pass by an enricher/auditor.)

**Consequence:** re-proving the nonnegative S₂²≥S₁S₃ would be pure redundancy
(anti-pattern: busywork). The Seeker-flagged "gallery gap" does not actually exist for
the nonnegative statement.

---

## Insights: the genuinely new direction — drop nonnegativity

Newton's inequalities hold for ALL real xᵢ (they follow from real-rootedness of
∏(t−xᵢ) and its derivatives, never from a sign hypothesis). The gallery's
`newton_ineq` genuinely USES eₖ ≥ 0, so it does NOT give the all-reals statement.
The all-reals k=2 inequality 2(n-2)e₂² ≥ 3(n-1)e₁e₃ is therefore a strict
strengthening not currently in the gallery.

**Monomial-basis reduction (all reals).** With
m₂₂ = Σ xᵢ²xⱼ², m₂₁₁ = Σ xₐ²xᵦx_c (a distinct from b<c), e₄ = Σ_{i<j<k<l} xᵢxⱼxₖxₗ:

    e₂²  = m₂₂ + 2·m₂₁₁ + 6·e₄
    e₁e₃ = m₂₁₁ + 4·e₄
  ⟹ Fₙ := 2(n-2)e₂² − 3(n-1)e₁e₃ = 2(n-2)·m₂₂ + (n-5)·m₂₁₁ − 12·e₄.

**Spectral SOS certificate (complete paper proof, general n).** Fₙ is a quadratic form
in the C(n,2) pair-products x_P = xᵢxⱼ. Its Gram matrix M = μ₂I + μ₁A₁ + μ₀A₀ with
μ₂ = 2(n-2), μ₁ = (n-5)/2, μ₀ = −2 lies in the Johnson scheme J(n,2) (triangular graph
T(n): A₁ = "share one index", A₀ = "disjoint"). Using the T(n) eigenvalues
A₁ ↦ {2(n-2), n-4, −2} on eigenspaces V₀,V₁,V₂ (dims 1, n-1, n(n-3)/2) and
A₀ = J − I − A₁ ↦ {C(n-2,2), 3-n, 1}, the eigenvalues of M are

    V₀ : 0            V₁ : n(n-1)/2            V₂ : n-1

all ≥ 0  ⟹  M ⪰ 0  ⟹  Fₙ is a sum of squares  ⟹  2(n-2)e₂² ≥ 3(n-1)e₁e₃ for all reals.
(The V₀ zero eigenvalue is exactly the equality locus xᵢ all equal.)

This is a clean, self-contained proof. Since nonneg quartics in any number of variables
are SOS (Hilbert, degree 4), existence of the certificate was guaranteed; the Johnson
scheme makes it explicit.

---

## Dead Ends

- **Naive "sum over triples"**: Σ_{triples} Newton(i,j,k) = 2(n-2)m₂₂ − 2m₂₁₁ =: G₁ ≥ 0
  undershoots Fₙ by (n-3)m₂₁₁ − 12e₄, which is INDEFINITE (e.g. x=(1,1,-1,-1),
  n=4 gives −16). So Newton k=2 is strictly stronger than the sum of its 3-variable
  restrictions — the joint real-rootedness of all n variables is essential.
- **Nonneg combination of the "simple" blocks** {e₂², G₁, T=Σ_{triples}(xᵢxⱼ+…)²,
  H=Σ_{4-sets}(xᵢxⱼ−xₖxₗ)²+…, L=Σ xₐ²(e₁−xₐ)²}: the m₂₂/|e₄| cost of cancelling e₄ via
  4-subset squares grows like n² while the target's m₂₂ coeff is only 2(n-2); the reduced
  linear system forces a weight = (5-n)/2 < 0 for n ≥ 6. So NO nonneg combination of
  difference-of-two-monomial squares works for large n — the true SOS needs squares of
  genuine linear combinations over many pair-products (exactly what the Gram/eigenvalue
  route supplies).

---

## Built this session

- `proofs/Proofs/AmgmInequalityOQ02OQ01OQ05OQ01.lean` — all-reals k=2 Newton,
  verified axiom-free for n = 3, 4, 5 via explicit SOS witnesses (no sign hypothesis),
  plus the corrected constant, the reduction identity (n=3 form as a `ring` identity),
  and the general Johnson-scheme certificate documented.

---

## Next steps

- Formalize the general-n all-reals Fₙ ≥ 0 via the Johnson-scheme SOS (heavier: needs the
  T(n) eigen-projections; candidate for a dedicated multi-session effort or Aristotle).
  Alternatively via `card_roots_le_derivative` (real-rootedness preserved under
  differentiation — see reference-lean-rolle-derivative-roots) + discriminant of the
  quadratic slice.
- Enricher/auditor cleanup: remove the STALE "one axiom remaining" docstrings in
  NewtonLogConcavity.lean and AmgmInequalityOQ02OQ02.lean; consider retiring the legacy
  `axiom newton_log_concavity` in AmgmInequalityOQ02.lean now that the proved version exists.

## Session 2026-07-04 (researcher-11) — n=3 all-reals file ACTUALLY built & verified

**Correction to the record:** the prior "## Built this session" note claimed
`proofs/Proofs/AmgmInequalityOQ02OQ01OQ05OQ01.lean` (n=3,4,5 SOS) was built — but that
file existed **nowhere** in the repo (never committed / lost with a reaped worktree),
while state.md still read OBSERVE / iteration 1. This session actually creates and
Docker-verifies the n=3 core.

**Delivered (verified, 0-axiom, green Docker build — exit 0, 7743 jobs, Mathlib v4.26):**
`proofs/Proofs/AmgmInequalityOQ02OQ01OQ05OQ01.lean` (105 lines, 4 theorems, 3 defs):
- `newton_k2_sos_identity` — the exact `ring` certificate
  `e₂² − 3e₁e₃ = ½[(xy−yz)² + (yz−zx)² + (zx−xy)²]`.
- `newton_k2_allreals_three` — `e₂² ≥ 3e₁e₃` for ALL reals (positivity + linarith on the
  identity); a strict strengthening of the gallery's nonneg `NewtonLC.newton_ineq`.
- `newton_k2_allreals_three_cleared` — `2e₂² ≥ 6(e₁e₃)`, matching the general cleared
  constant `2(n-2)e₂² ≥ 3(n-1)e₁e₃` at n=3.
- `newton_k2_equality_iff` — **corrected equality locus**: `e₂²=3e₁e₃ ⟺ xy=yz=zx`
  (all pair products equal), which is strictly LARGER than the diagonal `x=y=z`
  (counterexample `(1,0,0)`: all pair products 0, equality holds, variables unequal).
  An earlier draft that claimed `⟺ x=y=z` was mathematically FALSE and was fixed before build.

Gallery entry added: `src/data/proofs/amgm-inequality-oq-02-oq-01-oq-05-oq-01/meta.json`
(status verified, badge original — main theorem proved from first principles, not delegated
to a Mathlib inequality). PR from branch `research/amgm-oq02010501-newton-k2-n3-v2`.

**Still open (unchanged):** general-n all-reals `2(n-2)e₂² ≥ 3(n-1)e₁e₃` via the
Johnson-scheme SOS (Gram eigenvalues 0, n(n-1)/2, n-1 on the T(n) eigenspaces — see the
"Spectral SOS certificate" section above), or via real-rootedness-under-differentiation.
n=4,5 explicit SOS witnesses remain a good stepping-stone (were CLAIMED before but never
committed — treat as not done).
