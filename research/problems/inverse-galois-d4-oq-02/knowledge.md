# Knowledge Base: inverse-galois-d4-oq-02

Generalize Gal(X⁴−2/ℚ) = D₄ to Gal(Xⁿ−p/ℚ): metacyclic of order n·φ(n) under genericity.

---

## Problem Understanding

The splitting field of `Xⁿ − p` (prime `p`) over ℚ is `ℚ(ⁿ√p, ζₙ)`. The Galois group is
metacyclic: `1 → Cₙ → Gal → (ℤ/n)ˣ → 1`, of order dividing `n·φ(n)`, with equality under the
genericity hypothesis `ℚ(ⁿ√p) ∩ ℚ(ζₙ) = ℚ`. Parent case `n=4, p=2` gives `D₄`, order `8 = 4·φ(4)`.

---

## Insights

- **Eisenstein is uniform in `n`.** `Xⁿ − p` is Eisenstein at `p` for every `n ≥ 1`, so it is
  irreducible over ℚ with no case analysis. Reuses `NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime`.
- **The two divisibility factors of `n·φ(n)` are independently provable and cheap.**
  - `n ∣ |Gal|` from `irred_monic_degree_dvd_splitting_finrank` (parent lemma) — the kernel `Cₙ`.
  - `φ(n) ∣ |Gal|` from a primitive `n`-th root of unity living in the splitting field — the quotient `(ℤ/n)ˣ`.
- **Manufacture the primitive root from the roots themselves.** Every root `β` of `Xⁿ−p` has `βⁿ = p`,
  so for a fixed root `α ≠ 0` the `n` ratios `β/α` are exactly the `n` distinct `n`-th roots of unity in
  the splitting field. `HasEnoughRootsOfUnity.of_card_le` then yields a primitive `ζₙ` with no separate
  cyclotomic splitting-field construction. `rootsOfUnity.mkOfPowEq` packages each ratio as a unit.
- **`[ℚ(ζₙ):ℚ] = φ(n)`** via `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` (note: the lemma
  returns `cyclotomic n ℚ = minpoly ℚ ζ`, the REVERSED direction — rewrite with `←`) + `natDegree_cyclotomic`.
  Needs the instance `[NeZero ((n:ℕ):ℚ)]` (supply via `Nat.cast_ne_zero.mpr`).
- **Upper bound `|Gal| ∣ n!`** from the faithful action on roots (`galActionHom_injective`), generalizing
  the parent's `x4_sub_2_gal_card_dvd_24`.

## Session 2026-06-27 (Session 1) — FRESH, outcome: progress (verified)

**Built** `proofs/Proofs/InverseGaloisD4OQ02.lean` (185 lines, 7 theorems, 0 sorries, 0 axioms;
`#print axioms` = propext/Classical.choice/Quot.sound only):
- `x_pow_sub_prime_irreducible / natDegree / monic / separable` — basic facts for all `n ≥ 2`.
- `n_dvd_gal_card : n ∣ |Gal(Xⁿ−p)|`.
- `gal_card_dvd_factorial : |Gal(Xⁿ−p)| ∣ n!`.
- `totient_dvd_gal_card : φ(n) ∣ |Gal(Xⁿ−p)|` — the new metacyclic ingredient.

Gallery entry `src/data/proofs/inverse-galois-d4-oq-02/`.

**Verification recipe** (docker image build was down — host disk I/O error): single-file elaboration
`LAKE_UNSAFE=1 lake env lean Proofs/InverseGaloisD4OQ02.lean`; dependency oleans on LEAN_PATH live under
`.lake/build/lib/lean/Proofs/` (NOT `.lake/build/lib/Proofs/`).

---

## Dead Ends / Gotchas

- `rw [← hcardroot]` on the goal `n ≤ card (rootsOfUnity n L)` fails: motive not type-correct because
  `rootsOfUnity n` carries a `NeZero n` instance and rewriting every `n` breaks it. Fix: prove the
  `card rootSet ≤ card rootsOfUnity` inequality first, then `rwa [hcardroot] at hle` (only rewrites the LHS).
- `minpoly_eq_cyclotomic_of_irreducible` is stated `cyclotomic n K = minpoly K μ` (reversed); use `← hmin`.

---

## Child entry: coprime sharpness (inverse-galois-d4-oq-02-oq-03)

`Proofs/InverseGaloisD4OQ02OQ03.lean` (4 theorems, 0 sorries, 0 axioms; `#print axioms` =
propext/Classical.choice/Quot.sound only) completes the "lcm + sharpness" next step below:

- `lcm_dvd_gal_card : lcm(n, φ(n)) ∣ |Gal(Xⁿ−p)|` — combines the two lower factors via `Nat.lcm_dvd`.
  Must be the **lcm, not the product**, since `n` and `φ(n)` may overlap (n=4: lcm(4,2)=4).
- `mul_totient_dvd_gal_card_of_coprime : gcd(n,φ(n))=1 ⟹ n·φ(n) ∣ |Gal|` — `Nat.Coprime.lcm_eq_mul`
  upgrades the lcm to the full metacyclic order, with **no genericity hypothesis** on the lower half.
- `gal_card_cubic_eq_six : |Gal(X³−p/ℚ)| = 6` for every prime `p`. Coprime (gcd(3,2)=1) gives 6 ∣ |Gal|;
  parent's `gal_card_dvd_factorial` gives |Gal| ∣ 3! = 6; `Nat.dvd_antisymm` squeezes. Cubic analogue of
  the base |Gal(X⁴−2)| = 8, but uniform in `p` and argument-free.

**Why n=4 is outside this regime**: gcd(4, φ(4)=2) = 2 ≠ 1, so lcm(4,2) = 4 ≠ 8 — the bracket alone
cannot pin |Gal| = 8; that's exactly why the base D₄ entry needed a separate ℝ-embedding argument.

Gallery entry `src/data/proofs/inverse-galois-d4-oq-02-oq-03/`. Same single-file `lake env lean` recipe.

## Next Steps

- Exact order `|Gal| = n·φ(n)` under genericity: prove the upper bound `|Gal| ≤ n·φ(n)` via the tower
  `SF = ℚ(ζₙ)(ⁿ√p)`, i.e. `[SF:ℚ(ζₙ)] ≤ n` (root of `Xⁿ−p` over `ℚ(ζₙ)`) and `[ℚ(ζₙ):ℚ] = φ(n)`.
  The hard formalization step is `splittingField (Xⁿ−p) = ℚ(ζₙ, ⁿ√p)` (all roots are `ⁿ√p · ζₙᵏ`).
- Non-coprime case (n=4): recover the full `n·φ(n)` beyond `lcm(n,φ(n))` via an independent kernel×quotient
  product witness.
- Identify the semidirect-product structure `Gal ≅ ℤ/n ⋊ (ℤ/n)ˣ` explicitly.

## Session 2026-06-27 (follow-up child oq-03-oq-01) — sharp degree boundary

`Proofs/InverseGaloisD4OQ02OQ03OQ01.lean` (3 theorems, 0 sorries, 0 axioms; `#print axioms` =
propext/Classical.choice/Quot.sound only) resolves the **first open question** of the cubic-pinning
entry oq-03 ("characterize all n with n·φ(n) = n!"):

- `totient_mul_eq_factorial_iff (hn : 2 ≤ n) : n·φ(n) = n! ↔ n = 2 ∨ n = 3`. Forward: write n = m+2,
  use `Nat.totient_lt` (φ(n) ≤ n−1 ⟹ n·φ(n) ≤ n(n−1)) and `(m+2)! = (m+2)(m+1)·m!` with m! ≥ 2
  (`Nat.factorial_le`), so n! ≥ 2·n(n−1) > n·φ(n) for n ≥ 4 — contradiction (nlinarith).
- `gal_card_eq_factorial_of_pin` : n·φ(n) = n! ⟹ |Gal(Xⁿ−p)| = n!, with **no coprimality hypothesis**
  — the only boundary degrees n ∈ {2,3} are automatically coprime, so the parent coprime bound applies.
- `gal_card_quadratic_eq_two : |Gal(X²−p/ℚ)| = 2` for every prime p — the quadratic companion of
  oq-03's cubic |Gal(X³−p)| = 6. (2·φ(2) = 2 = 2!.)

**Upshot**: the elementary bracket pins |Gal(Xⁿ−p)| exactly at n = 2 (→ 2 = |C₂|) and n = 3 (→ 6 = |S₃|),
and nowhere else; n ≥ 4 (starting with the base entry's n = 4, where 4·φ(4) = 8 ≠ 24) has genuine slack.
Gallery entry `src/data/proofs/inverse-galois-d4-oq-02-oq-03-oq-01/`. Same single-file `lake env lean` recipe.
