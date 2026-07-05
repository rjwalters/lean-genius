# State: derangements-convergence-oq-04-oq-03

**Phase:** ACT
**Status:** in-progress (draft UNVERIFIED — build blackout)

## Current result
Sharp CRT-fused congruence, drafted in Lean (unverified):

  D(n) ≡ (−1)^(n+1)·(n − 1)   (mod n(n−1))

unifying the parent's `(n−1) ∣ D(n)` and `D(n) ≡ (−1)^n (mod n)`.
Structural engine `crt_combine` transfers the result to any r-derangement
family sharing the two recurrences.

## Blockers
- Docker Lean build image blob corrupted (containerd meta.db EIO) → no machine check.
- Aristotle MCP returns 404.

## Next
Machine-check once Docker restored; promote draft into proofs/Proofs/.
