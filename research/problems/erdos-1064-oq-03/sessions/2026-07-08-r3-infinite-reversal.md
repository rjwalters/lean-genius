# erdos-1064-oq-03 — Session (researcher-3, 2026-07-08)

## Result: infinitely-often reversal direction RESOLVED (0 axioms / 0 sorries)

**Open crux going in:** whether φ(n) < φ(D(n)) holds infinitely often for the
double cototient iterate D(n) = n − φ(n − φ(n)). Prior sessions had only finite
reversal witnesses (n = 39 prime-landing, n = 42 composite-landing).

**What was proved:** an explicit infinite reversal family

    n = 21·2^(k+1),   k = 0,1,2,…

For every k:
- φ(21·2^(k+1)) = 12·2^k;
- first cototient step: 21·2^(k+1) − φ(·) = 15·2^(k+1)  (the PARENT family member);
- φ(15·2^(k+1)) = 8·2^k, so D(n) = 21·2^(k+1) − 8·2^k = 17·2^(k+1);
- φ(D(n)) = φ(17·2^(k+1)) = 16·2^k  >  12·2^k = φ(n).

Hence every member is a reversal point; the map k ↦ 21·2^(k+1) is injective, so
`ReversalSet := {n | φ(n) < φ(D(n))}` is **infinite**
(`reversal_infinitely_many`). Members recover the earlier witnesses: k=0 → n=42,
k=1 → n=84 (both already in the empirical reversal list).

`oq03_both_directions_infinite` packages this with the odd-prime forward family:
OQ-03 goes both ways infinitely often, exactly mirroring the single-step
Erdős 1064.

## Method
One-extra-step transport of the Grytczuk–Luca–Wójtowicz single-step family
15·2^(k+1): prepend a cototient preimage (21·2^(k+1) whose first step lands on
15·2^(k+1)); the second step lifts the odd part 15 ↦ 17, raising φ(D(n)) above
φ(n). No density machinery. Totient values computed via `Nat.totient_mul` on
coprime factors + `Nat.totient_prime_pow` (kernel-`decide` coprimality only —
no `native_decide`, so `ofReduceBool`-free).

## Verification
Host `lake env lean Proofs/EulerTotientOQ04OQ03.lean` → EXIT 0.
`#print axioms reversal_infinitely_many` / `oq03_both_directions_infinite`
→ [propext, Classical.choice, Quot.sound] only. 0 axioms / 0 sorries.

## Remaining open
- Density-1 forward statement φ(n) > φ(D(n)) for almost all n (transport
  Luca–Pomerance through one extra step) — now the main open direction.
- Full three-way (>,=,<) classification / other reversal branches.
