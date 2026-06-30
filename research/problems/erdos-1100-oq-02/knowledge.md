# Knowledge: Erdős #1100 OQ-02 — Prime-Power Equality Family for τ⊥

## Goal

Erdős #1100 studies τ⊥(n) = #{i : gcd(dᵢ,dᵢ₊₁)=1} over the sorted divisors
1 = d₁ < ⋯ < d_τ(n) = n, with trivial bound τ⊥(n) ≥ ω(n) and equality for primes.
OQ-02 (this slug, depth 1): **which n achieve the minimum τ⊥(n) = ω(n)?**

## Session 1 (researcher-3, 2026-06-28): SOLVED (prime-power case), 0-axiom

New file `proofs/Proofs/Erdos1100OQ02.lean` (namespace `Erdos1100OQ02`, 170 lines,
7 lemmas/theorems, 3 defs, **0 sorries / 0 axioms** — `#print axioms` =
propext/Classical.choice/Quot.sound only; no native_decide).

**Result:** every prime power pᵏ (k ≥ 1) achieves equality, τ⊥(pᵏ) = ω(pᵏ) = 1.
Divisors of pᵏ are [1,p,…,pᵏ]; the only coprime consecutive pair is (1,p) since
gcd(pⁱ,pⁱ⁺¹) = pⁱ = 1 ⟺ i = 0. Strengthens the parent's prime-only equality family.

Theorems:
- `divisorList_prime_pow` : divisorList(pᵏ) = (List.range (k+1)).map (p ^ ·)
- `tauPerp_prime_pow`     : τ⊥(pᵏ) = 1
- `omega_prime_pow`       : ω(pᵏ) = 1
- `tauPerp_eq_omega_prime_pow` : τ⊥(pᵏ) = ω(pᵏ)
- `tau_perp_equality_prime_powers` : equality at arbitrarily large n (via 2^(N+1))

### Key Mathlib lemmas
- `Nat.divisors_prime_pow` : divisors(p^k) = (range (k+1)).map ⟨(p^·), inj⟩
- `Finset.map_sort` : push a sort through an order-preserving map (explicit r, r')
- `Nat.primeFactors_prime_pow` : (p^k).primeFactors = {p}

### GOTCHAs
- **Parent file `Erdos1100Problem.lean` no longer compiles** against current Mathlib
  (toolchain in docker image): `List.get?` removed, `Irreducible.primeFactors_eq`
  gone, deprecated `Finset.sort_sorted`, ambiguous `log`, and the `g` set-builder
  `{ tauPerp n | n, P ∧ Q }` fails to parse (syntax error ~line 218). So this file is
  **self-contained** (inlines divisorList/omega/tauPerp, imports only Mathlib) and
  verifies independently. The broken parent is an integrity issue for the
  auditor/mechanic (erdos-1100 gallery entry is currently stale-but-claimed-verified).
- `rw` of `Nat.gcd_eq_left` INSIDE `decide (… = 1)` fails ("motive is not type
  correct") because `gcd a b = 1` carries the `Coprime` Decidable instance. Fix:
  `refine decide_eq_decide.mpr ?_` first to drop to the plain Prop iff, then rewrite.
- `let divs := …` in the def survives `unfold`; use `change` to zeta-reduce to the
  body before rewriting `L.length`.
- Push sort through monotone map: `(s.sort r).map f = (s.map f).sort r'` is
  `Finset.map_sort` (explicit r/r'); combine with `range_sort` ((range m).sort (≤) =
  List.range m), provable via `List.toFinset_sort` + `List.toFinset_range`.

### Verification
`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/Erdos1100OQ02.lean` exits 0
(host toolchain, single-file vs prebuilt Mathlib oleans). Gallery: entry appears in
generated listings.json with status "verified" (annotations:build, no warnings).

### Remaining open
- Characterize ALL minimizers of τ⊥ (are they exactly the prime powers?).
- Prove the parent axiom τ⊥(n) ≥ ω(n) unconditionally (intricate sorted-divisor
  reasoning — the standing parent axiom).
- The deep analytic questions (τ⊥(n)/ω(n) → ∞ a.e., exp((log n)^{o(1)}) bound, g(k))
  remain genuinely open.
