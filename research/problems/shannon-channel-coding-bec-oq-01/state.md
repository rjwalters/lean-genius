# State — shannon-channel-coding-bec-oq-01 (q-ary Erasure Channel Capacity)

**Status**: COMPLETE (verified, 0 axioms / 0 sorries) pending merge.
**Researcher**: researcher-12
**Date**: 2026-06-18

## Result

Generalized the parent binary erasure channel to an arbitrary input alphabet
of size `q`. New file `proofs/Proofs/ShannonChannelCodingBECOQ01.lean`
(276 LOC, 14 theorems/lemmas, 2 defs, 0 axioms, 0 sorries) proving

    C(QEC(p)) = (1 − p) · log q     (qec_capacity)

for the q-ary erasure channel `qec : DMChannel α (Option α)` over any finite
input type `α` with `Fintype.card α = q`.

## Approach (single ACT cycle)

The parent finite-alphabet channel scaffold (`DMChannel`, `InputDist`,
`channelMI`, `channelCapacity`, `chain_rule`, `channelMI_le_log_card`) was
already polymorphic in the alphabet — the parent BEC entry only instantiated
it at `Bool`. The generalization therefore required NO new information-theory
infrastructure; it is the binary proof with `Bool` replaced by `α`:

1. `qec` — the channel; normalization by indicator-sum collapse.
2. `qec_ymarg_none` / `qec_ymarg_some` — output marginals.
3. `qec_conditional_entropy` — the erasure identity H(X|Y) = p·H(X) (the
   q-independent engine; un-erased terms vanish via log 1 = 0).
4. `qec_mi_eq` — I(X;Y) = (1 − p)·H(X) via the chain rule.
5. `qec_capacity` — converse from `entropy_le_log_card` (H(X) ≤ log q),
   achievability from `uniformInput` + `entropy_of_uniform_eq_log_card`.
6. `qec_eq_bec` (by rfl) + `qec_capacity_bool` / `_bits` — the BEC is the
   q = 2 instance; capacity (1 − p) log 2 = 1 − p bits, matching the parent.

The only alphabet-specific ingredient is the maximum-entropy value `log q`.

## Scope / honesty

Formalizes the discrete capacity exactly as stated (conditional-entropy
identity, mutual-information identity, converse, achievability). The
operational coding theorem (random codebooks, Fano converse) is not
formalized — consistent with the parent BEC/BSC/AWGN entries.

## Build

`./proofs/scripts/docker-build.sh Proofs.ShannonChannelCodingBECOQ01`
(cold fresh-worktree build; first attempt hit a transient git-clone failure
of a Mathlib dependency — retried).

## Open follow-ups

- Operational coding theorem for the erasure channel.
- Specialize α to GF(q) and connect to Reed–Solomon (MDS) erasure codes.
- q-ary symmetric channel capacity log q − h(p) − p log(q − 1).
