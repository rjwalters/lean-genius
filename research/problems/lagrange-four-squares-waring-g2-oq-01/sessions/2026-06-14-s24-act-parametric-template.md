# S24 ACT — Parametric counting+omega template (researcher-1, 2026-06-14)

## Goal

Picker #1 (well-grounded after 5 verified `k`-instances): collapse the
five per-`k` counting+omega lower-bound files into one parametric
theorem.

## What shipped

`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingTemplate.lean`:

- `IsSumOfKthPowers k s n := ∃ f : Fin s → ℕ, (∑ i, (f i)^k) = n`
- `waring_lower_template (k s N) (hk : 1 ≤ k) (hbound : N < 3^k)
   (hinfeas : ∀ n0 n1 n2, n0+n1+n2=s → n1+2^k*n2=N → False)
   : ¬ IsSumOfKthPowers k s N`
- Corollaries `g3_lower … g8_lower` (k = 3..8), each ~3 LOC.

Registered in `Proofs.lean`.

## Why one `Fin 3` template suffices for all k

Mahler witness `N = 2^k·⌊(3/2)^k⌋ − 1 < 3^k` ⇒ bound `f i < 3` is
uniform in k. Only `2^k` (value-2 coefficient) varies. Reduced system:
`n0+n1+n2 = s`, `n1 + 2^k·n2 = N`, infeasible by omega at each k.

## Proof = parametric generalization of verified G7

Mirrors the Docker-verified `…CountingG7.lean` (S22) step-for-step,
swapping literals (142, 2175, 2187, 128) for variables (s, N, 3^k, 2^k).
New tactics vs. literal-k siblings:
- bound omega closes on opaque atoms `3^k,(f i)^k,∑,N`;
- expand needs `0^k=0` (obtain ⟨m,rfl⟩; simp [pow_succ]) and `one_pow`;
- discharge factored into `hinfeas` (per-k omega in the corollary).

## Verification status — BUILD-PENDING

Docker daemon DOWN (2026-06-14 blackout). NOT machine-checked this
session. Shipped as DRAFT; the 5 standalone files remain build-verified
in place, so gallery coverage is unaffected if the template needs a fix.

## Next

1. Docker-verify; if clean, delete the 5 standalone files (~−650 LOC).
2. Close g(8) standalone draft #23330/#23377 (subsumed by `g8_lower`).
3. Upper bounds stay circle-method research-level.
