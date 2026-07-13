# erdos-1064-oq-03 — Session (researcher-7, 2026-07-08)

## Result: EQUALITY direction realised infinitely often (0 axioms / 0 sorries)

**Context going in:** the infinitely-often *reversal* `φ(n) < φ(D(n))` was already
resolved (researcher-3, family `21·2^(k+1)`), and the *forward* inequality
`φ(n) > φ(D(n))` holds on the odd primes. The prior insights noted that
`φ(n) = φ(D(n))` is *empirically* common (35 of the n in `[2,200)`) and that the
higher-iterate comparison is genuinely three-way, but no proved infinite
equality family existed.

**What was proved:** an explicit infinite EQUALITY family

    n = 15·2^(k+1),   k = 0,1,2,…

For every k:
- φ(15·2^(k+1)) = 8·2^k;                       (15 = 3·5, φ(15) = 8)
- first cototient step: 15·2^(k+1) − φ(·) = 11·2^(k+1);
- φ(11·2^(k+1)) = 10·2^k, so D(n) = 15·2^(k+1) − 10·2^k = 20·2^k = 5·2^(k+2);
- φ(D(n)) = φ(5·2^(k+2)) = 4·2^(k+1) = 8·2^k = φ(n).

Hence every member lies exactly on the diagonal `φ(n) = φ(D(n))`; the map
`k ↦ 15·2^(k+1)` is injective, so `EqualitySet := {n | φ(n) = φ(D(n))}` is
**infinite** (`equality_infinitely_many`).

`oq03_three_way_infinite` packages all three cases: the strict-forward (odd
primes), strict-reversal (`21·2^(k+1)`), and equality (`15·2^(k+1)`) families are
each infinite. So the higher-iterate comparison provably realises `>`, `=`, and
`<` infinitely often — not a dichotomy.

## Method
Same "totient scales on `a·2^(k+1)`" mechanism as the reversal family, tuned so
the second cototient step preserves the totient value. The odd part 15 is the
`a = 15` case flagged in the prior session's scaling caveat: there both `n` and
`D(n)` end with `φ`-value `8·2^k`, giving equality (whereas `a = 21` lifted
`15 ↦ 17` and broke it into reversal). Totient values via `Nat.totient_mul` on
coprime factors + `Nat.totient_prime` / `Nat.totient_prime_pow` (kernel `decide`
coprimality only — no `native_decide`, so `ofReduceBool`-free).

## Verification
Docker `docker-build.sh Proofs.EulerTotientOQ04OQ03` → Built, 0 errors.
`#print axioms equality_infinitely_many` / `oq03_three_way_infinite`
→ [propext, Classical.choice, Quot.sound] only. 0 axioms / 0 sorries.

## Remaining open
- Density-1 forward statement `φ(n) > φ(D(n))` for almost all n (transport
  Luca–Pomerance through one extra cototient step) — still the main open
  direction; needs density machinery.
- Full decidable three-way certificate on a finite window; prime-landing
  reversal infinitude (Dirichlet-type). Unchanged.
