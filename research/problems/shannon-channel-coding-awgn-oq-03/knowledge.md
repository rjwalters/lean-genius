# Knowledge Base: shannon-channel-coding-awgn-oq-03

## Status: COMPLETED (Shannon–Hartley half verified & merged)

`ShannonChannelCodingAWGNOQ03.lean` (#30994, VERIFIED, 0-axiom, 0-sorry, 11 thm)
formalizes the bandlimited **Shannon–Hartley** capacity
`C = B·log₂(1 + P/N)` bits/s:

- `shannonHartley_eq_awgn` — bridge identity to the per-use AWGN capacity.
- `shannonHartley_eq_two_B_bits_per_use` — Nyquist assembly (2B uses/s).
- nonnegativity, zero-power, zero-bandwidth, positivity.
- monotone in `B` and `P` (+ strict), antitone in noise `N`.
- `shannonHartley_le_snr_linear` — low-SNR linear bound via `log(1+x) ≤ x`.

## Genuinely open (out of shipped scope)

The title also names **parallel Gaussian channels via water-filling** (vector AWGN
capacity). This is NOT formalized. It needs:
`C = Σᵢ ½log₂(1 + Pᵢ/Nᵢ)` maximised over `Σᵢ Pᵢ ≤ P`, with optimum
`Pᵢ = max(0, ν − Nᵢ)` — an argument requiring concavity of `x ↦ log(1+x/N)` and
KKT/Lagrangian convex-optimization. Recommend a **dedicated slug**.

(Entry was already `status: completed`; this session restored stale stub
metadata — `currentState.focus`/`nextAction` and empty `knownResults` — and fixed
the pool tracker, which had re-served the finished problem. No new math.)
