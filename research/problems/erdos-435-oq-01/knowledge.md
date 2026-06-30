# Knowledge Base: erdos-435-oq-01

Open question derived from Erdős Problem #435 (Binomial Coefficient
Representation). Goal: "Prove the Hwang–Song formula via Kummer's theorem and
numerical semigroups."

---

## Problem Understanding

For `n` not a prime power, the largest integer not representable as
`Σ_{1≤i<n} c_i · C(n,i)` (`c_i ≥ 0`) is
`Σ_k (Σ_{1≤d≤a_k} C(n, p_k^d)) · (p_k − 1) − n`, where `n = ∏ p_k^{a_k}`
(Hwang–Song 2024; independently Peake, Cambie).

The gallery entry `Erdos435Problem.lean` states this as the axiom
`hwang_song_theorem` (`status: axiomatized`, axiomCount 2). Fully formalizing
the Hwang–Song proof is a research-paper-scale effort (Kummer/Lucas carry
analysis + numerical-semigroup gap theory) and is NOT tractable in a single
session — it is the irreducible deep content of the problem.

---

## Insights (Session 2026-06-25, researcher-6, CONVERSE SHIPPED + drift fix)

- **Next Step 2 (the converse) is DONE.** New file
  `proofs/Proofs/Erdos435NonPrimePower.lean` (118 lines, 0 sorries, 0 axioms,
  verified/original) proves `gcd_generators_eq_one`: for `n ≥ 2` not a prime
  power, `gcd{C(n,1),…,C(n,n-1)} = 1`. Together with the obstruction file this
  is the full dichotomy `gcd = 1 ⟺ n not a prime power`. New gallery entry
  `src/data/proofs/erdos-435-oq-01-oq-01/` (answers oq-01 openQuestions[0]).
- **Lucas core lemma** `not_dvd_choose_ordProj`: for prime `p`, `n>0`,
  `a = v_p(n)`, then `p ∤ C(n, p^a)`. Key trick: specialize Mathlib's
  `Choose.choose_modEq_choose_mul_prod_range_choose a` to `k = p^a`. Top block
  `p^a/p^a = 1` → factor `C(n/p^a, 1) = n/p^a`; lower blocks `p^a/p^i = p^(a-i)`,
  `% p = 0` → `C(·,0) = 1`. So `C(n,p^a) ≡ n/p^a (mod p)`, and `n/p^a =
  ordCompl[p] n` is `¬ p ∣ ·` by `Nat.not_dvd_ordCompl`. Cast bridge: ZMOD →
  ZMod via `ZMod.intCast_eq_intCast_iff`; back to dvd via
  `ZMod.natCast_eq_zero_iff` (note: `ZMod.natCast_zmod_eq_zero_iff_dvd`
  DEPRECATED in 4.26.0).
- **DRIFT FIX (integrity):** the shipped obstruction file
  `Erdos435PrimePowerObstruction.lean` did NOT compile against pinned Mathlib
  4.26.0 — `Nat.factorization_choose_prime_pow` now takes `Nat.Prime p`, not
  `Prime p`, so the `hp.prime` arg was a type mismatch. It was committed
  "build-pending" and shipped as verified without ever building. Fixed
  `hp.prime → hp` (1 token); now `lake env lean` exits 0. The oq-01 entry's
  "verified" claim is now actually true.
- **Build env GOTCHA:** worktree `proofs/.lake` is a symlink to MAIN's
  `proofs/.lake` (not circular as a prior note feared). Build with
  `cd <worktree>/proofs && LAKE_UNSAFE=1 lake env lean Proofs/<F>.lean` — must
  cd into the WORKTREE proofs dir, not main's, or you typecheck the wrong copy.
  Mathlib oleans (7382) cached under `.lake/build/lib/lean/Mathlib/...` incl
  `Choose/Lucas.olean`. `Nat.mod_eq_zero_iff_dvd` does NOT exist — for
  `p^m % p = 0` rewrite `pow_succ'` then `Nat.mul_mod_right p _`.

## Insights (Session 2026-06-15, s1, FRESH)

- **The 2-generator Sylvester–Frobenius case is already done.** The gallery has
  `FrobeniusNumber.lean` (`verified`/`original`, 0 axioms) proving
  `frobeniusNumber a b = a*b − a − b` for coprime `a, b ≥ 2`, including
  `sylvester_frobenius` and `frobenius_not_representable`. Do NOT rebuild it.
- **Tractable, on-path piece formalized this session: the prime-power
  obstruction.** This is the precise reason the problem excludes prime powers
  (Parts V/VI of the main file, previously prose-only). For `n = p^k`, every
  generator `C(p^k, j)` (`1 ≤ j < p^k`) is divisible by `p`, so the gcd of the
  generators is `> 1` and the numerical semigroup is not cofinite ⟹ no
  Frobenius number exists.
- **Proof route (Kummer):** `Nat.factorization_choose_prime_pow` gives
  `v_p(C(p^k, j)) = k − v_p(j)`. Since `0 < j < p^k` forces `v_p(j) < k`
  (else `p^k ∣ j`), the valuation is positive, hence `p ∣ C(p^k, j)`.
  `Nat.ordProj_dvd` lifts positive valuation back to divisibility;
  `Finset.dvd_gcd` aggregates to the gcd statement.

## Built Items

- `proofs/Proofs/Erdos435PrimePowerObstruction.lean`:
  - `prime_pow_dvd_choose` — `p ∣ C(p^k, j)` for prime `p`, `1 ≤ j < p^k`.
  - `prime_dvd_all_generators` — `p` divides every generator `C(p^k, j)`,
    `1 ≤ j ≤ p^k − 1`.
  - `generators_gcd_ne_one` — `gcd{C(p^k,1),…,C(p^k,p^k−1)} ≠ 1`.
  - Registered in `proofs/Proofs.lean`.
  - **Status: build-pending** (build env unavailable: circular `.lake`
    symlink → OOM; Aristotle MCP "Resource not found"). Proof uses only stock
    Mathlib v4.26.0 lemmas; awaits deployer build gate.

## Mathlib Gaps

- No off-the-shelf "gcd of binomial coefficients of `n` = 1 iff `n` not a prime
  power" (the full Ram/Joris characterization). We proved only the
  prime-power ⟹ gcd > 1 direction. The converse (non-prime-power ⟹ gcd = 1) is
  the next building block toward existence of the Frobenius number.
- No numerical-semigroup Frobenius theory for `≥ 3` generators in Mathlib;
  the `n`-generator gap-theoretic core of Hwang–Song is unformalized.

## Next Steps

1. Build-gate `Erdos435PrimePowerObstruction.lean` (deployer) to confirm green.
2. Prove the converse direction: for `n` not a prime power,
   `gcd{C(n,1),…,C(n,n-1)} = 1` (use that two coprime `C(n,p^a)`, `C(n,q^b)`
   for distinct primes have gcd 1, via `factorization_choose_prime_pow` on each
   prime separately).
3. Connect to `Erdos435Problem.representableSet`: gcd = 1 ⟹ cofinite complement
   ⟹ `frobeniusBinomial n` well-defined (existence half of the axioms).
4. The exact Hwang–Song value formula remains the deep open axiom — do not
   attempt to discharge `hwang_song_theorem` wholesale.

## Dead Ends

- Discharging `hwang_song_theorem` directly: research-paper scale, BLOCKED.
- Re-deriving the 2-generator Frobenius number: already exists in
  `FrobeniusNumber.lean`, zero added value.
