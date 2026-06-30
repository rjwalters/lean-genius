# Hilbert #13 — OQ-03: minimal requirements on the inner functions

**Problem.** In the Kolmogorov–Arnold superposition
`f(x) = Σ_q Φ_q( Σ_p coeff_{p,q} · φ_p(x_p) )`, what are the *minimal requirements on the inner
functions* `φ_p` for a representation of every continuous `f` to be possible?

## Session 1 (researcher-2, 2026-06-27) — phase OBSERVE → ACT

### Strategy
Following the model of the verified sibling `hilbert-13-oq-02` (which isolated covering-dimension
invariance), this open question is fuzzy at the level of full *sufficiency* (that is Sternfeld's
deep "basic embedding" theory). So instead of attempting the sufficiency characterisation, I
isolated and formalized the **necessary core** that any admissible inner family must satisfy:
**point separation / injectivity**.

### Key idea (the provable kernel)
Bundle the inner data into a single **feature map** `Ψ : (Fin n → ℝ) → (Fin Q → ℝ)`,
`Ψ(x)_q = Σ_p coeff_{p,q} · φ_p(x_p)`. The outer functions `Φ_q` see the domain point `x`
*only through* `Ψ(x)`. Hence:

1. **Collapse lemma** (`eq_of_feature_eq`): if `Ψ x = Ψ y`, then `f x = f y` for *every*
   representable `f`. The outer layer is powerless to separate points the inner layer merges.
2. **Necessity of injectivity** (`feature_injective_of_universal`): if every continuous function
   is representable through `Ψ` and continuous functions separate the domain's points, then `Ψ`
   must be injective.
3. **Descent to each inner function** (`inner_injective_of_feature_injective`): for the concrete
   KA feature map, injectivity of `Ψ` forces *each* `φ_p` to be injective (use two cube points
   differing only in coordinate `p`).
4. **Headline** (`inner_functions_must_be_injective`): a single inner family `(φ, coeff)` that
   represents every continuous function on `ℝⁿ` must have every `φ_p` injective.

Point separation on `Fin n → ℝ` is supplied by the coordinate projections (`separates_of_pi`),
using only the product topology — no metric/instance diamond needed.

### Honest boundary
Injectivity is **necessary but NOT sufficient**. Sternfeld (1985) proved the true admissibility
threshold is a strictly stronger *uniform* separation condition; mere injectivity can force the
outer functions to lose continuity. The file documents this in a closing remark and makes **no**
sufficiency claim. So this result pins the *floor* of the requirements, not the exact threshold.

### Artifact
`proofs/Proofs/Hilbert13OQ03.lean` — namespace `Hilbert13OQ03`, `import Mathlib`.
Target: **0 axioms, 0 sorries** (5 theorems + 2 defs).

### Verification status: UNVERIFIED
Both verification channels were down this session:
- Docker build host: containerd metadata corruption (`write .../meta.db: input/output error`);
  `docker images` empty (cached `lean4-arm64:v4.26.0` image gone). Needs an operator Docker
  restart — this is NOT an ENOSPC problem (disk had ~568Mi free).
- Aristotle MCP: `404 Not Found` on `aristotle.harmonic.fun/api/v1/project` (smoke test failed).

The proof was manually reviewed lemma-by-lemma for Mathlib API correctness
(`Function.ne_iff`, `continuous_apply`, `Finset.sum_congr`, `eq_or_ne`, ite-simp reductions).
Gallery `meta.json` deliberately **not** created yet — a "verified/0-axiom" gallery claim should
wait until a real build confirms compilation.

### Next steps
- Re-run `./proofs/scripts/docker-build.sh Proofs.Hilbert13OQ03` once the Docker host is restored;
  if green, add `src/data/proofs/hilbert-13-oq-03/{meta.json,annotations.json}` mirroring oq-02
  and flip status to `verified`.
- Possible follow-up (NOT this session, depth guard ok at depth 1): formalize the *sufficiency*
  gap qualitatively — a counterexample showing an injective-but-not-uniformly-separating inner
  family whose outer reconstruction must be discontinuous.
