# Knowledge: fair-games-theorem-oq-02-oq-04

## Session 2026-04-22 (Session 1) — COMPLETED

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms)

### What I Did
- Claimed problem, read parent OQ01 and OQ02 proofs for API/structure context
- Wrote `FairGamesTheoremOQ02OQ04.lean` (345 lines) with concrete examples, structural properties, and new alternative formula theorem
- Fixed API differences between main repo and worktree Lean (pow_lt_one → pow_lt_one₀, explicit struct-field omega)
- Built successfully with docker-build.sh; 0 sorries, 0 axioms
- Created gallery entry meta.json, committed, pushed, opened PR rjwalters/lean-genius#11322

### Key Findings
- `BiasedGamblersRuin` is defined in FairGamesTheoremOQ01.lean with `r = q/p`, `p + q = 1`
- `pow_lt_one₀` (not `pow_lt_one`) is the correct Mathlib 4.26 lemma name in this worktree
- Omega cannot see struct field projections like `B.hN`; must use `have := B.hN; omega`
- `div_lt_div_right` exists but `div_lt_div_iff₀` + `mul_lt_mul_of_pos_right` is more reliable
- `field_simp` with nonzero witnesses closes the alt-formula algebraic identity completely
- `rw [show favorableGame.k = 2 from rfl, ...]` needed for norm_num on concrete games

### Files Modified
- `proofs/Proofs/FairGamesTheoremOQ02OQ04.lean` (new)
- `src/data/proofs/fair-games-theorem-oq-02-oq-04/meta.json` (new)
- `src/data/research/problems/fair-games-theorem-oq-02-oq-04.json`

### Next Steps
- None; problem completed and PR submitted

## Key Facts

### Parent Results (fair-games-theorem-oq-02)
- Unbiased walk: $P(\text{step}=+1) = P(\text{step}=-1) = 1/2$
- Ruin probability (fair): $P(\text{reach } 0 \mid S_0 = k) = (N-k)/N$
- Proved via martingale: $S_n$ is a martingale, OST gives $E[S_\tau] = k \Rightarrow P(\text{reach }N) = k/N$

### Biased Walk Formula
- Biased walk: $P(\text{step}=+1) = p$, $P(\text{step}=-1) = q = 1-p$, with $p \neq 1/2$
- **Geometric martingale**: $M_n = (q/p)^{S_n}$ is a martingale
  - Verification: $E[M_{n+1}|\mathcal{F}_n] = p(q/p)^{S_n+1} + q(q/p)^{S_n-1} = (q/p)^{S_n}[p(q/p) + q(p/q)] = (q/p)^{S_n}[q + p] = M_n$ ✓
  - Wait: $p(q/p) + q(p/q) = q + p^2/q \neq 1$ unless $p=q$. 
  - Correct derivation: $E[M_{n+1}|\mathcal{F}_n] = (q/p)^{S_n}[p(q/p) + q/(q/p)] = (q/p)^{S_n}[q + qp/q]$... 
  - Standard: $(q/p)^{S_n}$ is a martingale by direct check: $p \cdot (q/p)^{k+1} + q \cdot (q/p)^{k-1} = (q/p)^k[p(q/p) + q(p/q)] = (q/p)^k \cdot 1$. ✓ (since $p(q/p) + q(p/q) = q + p = 1$)

### Ruin Probability Derivation
- Let $r = q/p$. By OST: $E[r^{S_\tau}] = r^k$
- $S_\tau \in \{0, N\}$: $P(S_\tau=0) \cdot 1 + P(S_\tau=N) \cdot r^N = r^k$
- Setting $u = P(S_\tau=0)$: $u + (1-u)r^N = r^k \Rightarrow u = (r^k - r^N)/(1 - r^N)$
- For $r \neq 1$: $P(\text{ruin at }0) = \frac{(q/p)^k - (q/p)^N}{1 - (q/p)^N}$
- Alternative form: $\frac{1-(p/q)^{N-k}}{1-(p/q)^N}$ (dividing by $(q/p)^N$)

## Open Questions
- What is the correct Lean 4 definition for the biased random walk?
- Does Mathlib have `Real.rpow` inequalities for $q/p$ when $p \neq 1/2$?
- How does `fair-games-theorem-oq-02` define the walk? Is it parameterized by $p$?

## References
- Feller, W. *Probability Theory*, Vol 1, §XIV.1 — biased ruin formula
- Parent proof: `proofs/Proofs/FairGamesTheoremOQ02.lean`
- `Mathlib.Probability.ProbabilityMassFunction` — PMF for biased coin
