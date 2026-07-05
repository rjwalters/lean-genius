# Knowledge Base: chebyshev-pnt-bridge-oq-01-oq-04

Multinomial Kummer carry bound and π(kn).

---

## Problem Understanding

Generalize the binomial fact `p^{v_p(C(2n,n))} ≤ 2n` (parent `chebyshev-pnt-bridge-oq-01`)
to the central multinomial `C(kn; n,…,n)` with `k` blocks. The pool proposed the
"obvious" analogue `p^{v_p} ≤ kn`.

---

## Insights

### KEY FINDING — the proposed bound `p^{v_p} ≤ kn` is FALSE for every k ≥ 3.
The binomial proof works only because each Kummer carry digit
`⌊2n/p^i⌋ − 2⌊n/p^i⌋ ∈ {0,1}`. For `k` blocks the per-digit carry lies in
`{0,1,…,k−1}`, so `v_p` can reach `(k−1)·log_p(kn)`.

Explicit counterexamples (numerically checked, k≤7, n≤14, all p ≤ N):
- **k=3, n=2** (N=6): `C(6;2,2,2) = 90 = 2·3²·5`, so `3^{v_3} = 9 > 6`.
- **k=4, n=1** (N=4): `C(4;1,1,1,1) = 24 = 2³·3`, so `2^{v_2} = 8 > 4`.
The bound fails at essentially every n once k ≥ 3.

### Corrected bound: `p^{v_p(C(kn;n,…,n))} ≤ (kn)^{k-1}`.
From `v_p ≤ (k−1)·⌊log_p(kn)⌋`. Verified numerically (0 failures; worst observed
`v_p/log_p(N) ≈ 3.47 < k−1`). The Chebyshev π(kn) lower bound survives:
`C(kn;n,…,n) ≤ (kn)^{(k-1)·π(kn)}` and `≥ k^{kn}/poly`, giving
`π(kn) ≳ (kn)·log k / ((k−1)·log(kn))`; recovers the parent bound at k=2.

### Carry-digit identity (proved, drafted)
With `d = p^i`: `⌊kn/d⌋ − k·⌊n/d⌋ = ⌊k·(n mod d)/d⌋ ∈ [0, k−1]`, since
`k·(n mod d) < k·d`.

---

## Built (draft, UNVERIFIED — build-independent session)

`research/problems/.../lean/MultinomialKummerBound.lean`:
- `naive_multinomial_bound_false` — refutes `∀ p n k, p^{v_p} ≤ kn` (native_decide witness).
- `carry_digit_le` — per-digit bound `≤ k−1` (full proof drafted).
- `central_multinomial_factorization` — `v_p(mult) = v_p((kn)!) − k·v_p(n!)` (drafted via `Nat.multinomial_spec`).
- `pow_factorization_central_multinomial_le` — the corrected bound `p^{v_p} ≤ (kn)^{k-1}` (top-level assembly complete).
- `central_multinomial_val_le_log` — **one remaining sorry**; Legendre-sum grind, full blueprint in file.

Companion (already verified in gallery): `Erdos729LegendreMultinomial.lean` — multinomial
Legendre/Kummer identity `(p-1)·v_p(mult) + s_p(N) = Σ s_p(aᵢ)`.

---

## Dead Ends / Blockers

- **Aristotle**: 404 ("Resource not found") — could not verify or delegate. Same blackout
  as prior sessions.
- **Docker build**: historically down (containerd EIO) — could not compile `native_decide`
  or the drafted proofs locally. File lives under `research/problems/.../lean/` (not globbed
  by the lakefile), so it cannot break the gallery build.

---

## Next Steps

1. Prove `central_multinomial_val_le_log` (blueprint in file) — hand to Aristotle when 404 lifts.
2. Verify the drafted file once a build tool is restored.
3. Derive the explicit `π(kn)` lower-bound corollary.
