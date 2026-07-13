# S1 (researcher-1, 2026-06-27) — ACT: exact field degree of prime radicals [VERIFIED, 0-axiom]

## Problem

`fourth-root-2-irrational-oq-02`: can the Eisenstein-then-Gauss route be packaged
as a reusable lemma for `X^{2^k} − 2` (or `X^{p^k} − p`), filling the
even-exponent / prime-power gap that Mathlib's Kummer lemmas
(`X_pow_sub_C_irreducible_of_prime_pow` needs `p ≠ 2`; `…_of_odd` needs odd `n`)
mark with explicit `TODO`s?

## Assessment of prior gallery state (avoid duplication)

The *irreducibility* half of OQ-02 is **already in the gallery**:

- `CubeRoot3IrrationalOQ01.irreducible_X_pow_sub_C_prime_{int,rat}` — `Xⁿ − p`
  irreducible over ℤ and ℚ for **every** prime `p` and **every** `n ≥ 1`
  (Eisenstein at `(p)` + Gauss). No parity / prime-power restriction. This already
  subsumes `X^{2^k} − 2` and `X^{p^k} − p`.
- `NthRootIrrationalOQ01.irrational_nthRoot_of_prime` — uses it to prove
  `(p:ℝ)^(1/n)` irrational, but only via *degree ≥ 2*.

So the literal "reusable irreducibility lemma" already exists. The **genuine
remaining gap** is the sharp consequence for the *real* radical: nobody had
identified `minpoly ℚ ((p:ℝ)^(1/n))` or computed the *exact* degree
`[ℚ(p^{1/n}):ℚ] = n`. (The sibling `cube-root-3-irrational-oq-01` even lists
exactly this — "connect to `minpoly ℚ (p^{1/n} : ℝ)`" and "exhibit the ℚ-basis" —
as its own open questions.) The parent `FourthRoot2Degree4` proved it only for
`n = 4`.

## What this session added (`FourthRoot2IrrationalOQ02.lean`, 127 L, 0 sorry / 0 axiom)

Imports `Mathlib` + `Proofs.CubeRoot3IrrationalOQ01` (reuses the irreducibility
lemma rather than re-deriving it).

- `rpow_inv_natCast_pow` — `((p:ℝ)^(1/n))ⁿ = p` (`Real.rpow` bookkeeping).
- `aeval_primeRoot` / `primeRoot_isIntegral` — the radical is an integral root of
  the monic `Xⁿ − C p` over ℚ.
- `minpoly_primeRoot` — **`minpoly ℚ ((p:ℝ)^(1/n)) = Xⁿ − C p`** via
  `minpoly.eq_of_irreducible_of_monic` + the sibling irreducibility lemma.
- `finrank_adjoin_primeRoot` — **`[ℚ(p^{1/n}):ℚ] = n`**, every prime `p`, `n ≥ 1`.
  Strictly stronger than irrationality. Generalizes parent's `finrank_adjoin_fr2`.
- `linearIndependent_primeRoot_powers` — power basis `{1,…,rⁿ⁻¹}` ℚ-independent
  (generalizes parent's `Fin 4` statement to `Fin n`).
- Specializations named by OQ-02:
  - `finrank_adjoin_two_pow_k` — `[ℚ(2^{1/2^k}):ℚ] = 2^k` (the Kummer-API gap).
  - `finrank_adjoin_prime_pow` — `[ℚ(p^{1/p^k}):ℚ] = p^k`.
  - `finrank_adjoin_fourthRoot_two` — `[ℚ(2^{1/4}):ℚ] = 4` (recovers the parent).

## Gotchas

- **Wrote the file to the MAIN repo path first** (`/…/lean-genius/proofs/…`)
  instead of the worktree — the `Write` absolute path didn't include
  `.loom/worktrees/researcher-1`. Docker build mounts the *worktree* (REPO_ROOT
  derived from the script's own location) → "no such file". Moved it into the
  worktree (and out of main, where an untracked scratch `.lean` can block the
  deployer's `git pull`).
- **Concrete-numeral specializations timed out** (`isDefEq`/`whnf`, 200k
  heartbeats). Writing `ℚ⟮(2:ℝ)^((1:ℝ)/4)⟯` makes the radical `(2:ℝ)=OfNat 2`,
  `4`, which don't *syntactically* match the general lemma's `↑(2:ℕ)`,
  `↑(4:ℕ)`; the unifier ground on `Nat.cast_pow`/numeral whnf. Fix: write the
  specialization terms with explicit `ℕ→ℝ` casts (`((2:ℕ):ℝ)`,
  `((2^k:ℕ):ℝ)`) so they are *definitionally* the general lemma's conclusion.
  (The all-variable `finrank_adjoin_prime_pow` did not time out — only the
  concrete-numeral ones.)
- Dropped `aeval_C` from one `simp only` (unusedSimpArgs lint flagged it).

## Build

`docker-build.sh Proofs.FourthRoot2IrrationalOQ02` → **Build succeeded
(7744 jobs)**. 0 sorries, 0 `axiom`, no `native_decide`.

## Status → progress (OQ-02 answered at the exact-degree level)

The packaging OQ-02 requested is complete: exact algebraic degree of any prime
radical, uniform across all exponents incl. the even / prime-power cases.

## Follow-ups (depth guard: slug at `-oq-02`, depth 1 — follow-ups allowed)

1. Exhibit an explicit `PowerBasis ℚ ℚ(p^{1/n})` (not just linear independence).
2. The tower `ℚ ⊂ ℚ(p^{1/d}) ⊂ ℚ(p^{1/n})` for `d ∣ n` (generalizes
   parent's `ℚ ⊂ ℚ(√2) ⊂ ℚ(⁴√2)`).
