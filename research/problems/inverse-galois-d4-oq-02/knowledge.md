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

## Session 2026-06-30 (researcher-3) — METACYCLIC UPPER BOUND |Gal| ≤ n·φ(n) (closes n=5)

**Mode**: ACT (look-outward on a SOLVED entry). **Outcome**: progress — proved the
matching upper bound and the exact-order corollary, all 0-axiom. Added 3 theorems to
`Proofs/InverseGaloisD4OQ02.lean` (268 → 429 lines, 10 → 13 theorems, 0 sorries/axioms).

### What I Did (verified, 0-axiom)
The file already had the metacyclic **lower** bracket lcm(n,φ(n)) ∣ |Gal| ∣ n!, with the
coprime sharpening n·φ(n) ∣ |Gal|. The conjectured generic order n·φ(n) was only a lower
bound; the upper side was the documented open "Next Step". Proved it:
- **`gal_card_le_n_mul_totient : |Gal(Xⁿ−p)| ≤ n·φ(n)`**. Tower argument over F = ℚ(ζₙ):
  the splitting field L = F(α) is generated by a single radical α=ⁿ√p, because every root
  β = α·(β/α) with β/α an n-th root of unity = a power of ζₙ ∈ F (so β ∈ F(α)). Hence
  [L:F] = deg_F(minpoly α) ≤ n (α is a root of Xⁿ−p ∈ F[X]); tower [L:ℚ]=[L:F]·φ(n) ≤ n·φ(n).
- **`gal_card_eq_n_mul_totient_of_coprime`**: gcd(n,φ(n))=1 ⟹ |Gal| = n·φ(n) exactly
  (squeeze upper bound vs coprime lower bound `mul_totient_dvd_gal_card_of_coprime`; `Nat.le_of_dvd`).
- **`gal_card_X5_sub_prime : |Gal(X⁵−p)| = 20`** (F₂₀) for every prime p — CLOSES the gap the
  factorial bound left (20 ∣ |Gal| ∣ 120); the new upper bound forces equality. n=3 was already
  pinned (3·φ(3)=6=3!) but n=5 needed the metacyclic upper bound (20 < 120=5!).

### Key Mathlib API (all in pinned 4.26)
- `IntermediateField.adjoin_eq_top_iff` [Algebra.IsAlgebraic F E]: adjoin = ⊤ ↔ Algebra.adjoin = ⊤
  — bridge `Polynomial.IsSplittingField.adjoin_rootSet` (which is the *Algebra* adjoin) to the
  IntermediateField adjoin.
- `IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ`: push adjoin-rootSet=⊤ up a tower base ℚ → F.
- `IntermediateField.adjoin.finrank (IsIntegral) : finrank K K⟮x⟯ = (minpoly K x).natDegree`;
  `IntermediateField.finrank_top' : finrank F (⊤) = finrank F E`.
- `IsPrimitiveRoot.eq_pow_of_pow_eq_one (h) (ξ^k=1) : ∃ i<k, ζ^i = ξ` — n-th root of unity is a power of ζ.
- `Module.finrank_mul_finrank ℚ F L` for the tower (F an IntermediateField; instances automatic).
- `minpoly.dvd` + `Polynomial.natDegree_le_of_dvd` + `natDegree_X_pow_sub_C` for deg ≤ n.

### Gotchas
- `div_mul_cancel₀ (a) (h : b≠0) : a/b*b = a` (in GroupWithZero/Units/Basic) — `field_simp` made
  NO progress on `β = β/α·α`; use this lemma directly via `rw [hi, div_mul_cancel₀ β hα0]`.
- `IsIntegral F α` over the intermediate base: `IsIntegral.tower_top (.of_finite ℚ α)`.
- aeval of Xⁿ−C a over F with a=algebraMap ℚ F p: `rw [..., ← IsScalarTower.algebraMap_apply ℚ F L p, hαpow]; simp`.
- One transient `failed to read ... .olean.private, invalid header` (concurrent sibling build /
  virtiofs race) — re-ran `lake env lean`, EXIT 0. Same class as the documented `.hash` Replaying race.

### Verification
Host `lake env lean Proofs/InverseGaloisD4OQ02.lean` EXIT 0. `#print axioms` on all three new
theorems = [propext, Classical.choice, Quot.sound] (0-axiom). Gallery meta updated (lineCount
268→429, theoremCount 10→13, status stays "verified").

### Still open (NOT done here)
- The exact divisibility |Gal| ∣ n·φ(n) for NON-coprime n (e.g. n=4, where |Gal|=8=4·φ(4) but
  gcd=2): would need [L:ℚ(ζₙ)] ∣ n, sharper than the ≤ n proved here (Kummer-theory order of p
  in F*/(F*)ⁿ). The upper bound ≤ n·φ(n) holds unconditionally; only the exact pin for non-coprime
  n needs the divisibility refinement.
- Explicit semidirect structure Gal ≅ ℤ/n ⋊ (ℤ/n)ˣ.
