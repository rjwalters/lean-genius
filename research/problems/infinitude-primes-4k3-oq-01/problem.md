# infinitude-primes-4k3-oq-01: Dirichlet's theorem on primes in AP (full generality)

## Seeker statement

> Prove Dirichlet's theorem: infinitely many primes in any AP `{a + nd : n ≥ 0}`
> with `gcd(a, d) = 1`, requiring Dirichlet characters
> `χ : (ℤ/dℤ)ˣ → ℂˣ` and L-functions `L(s, χ) = Σ_n χ(n)/nˢ`. Non-vanishing
> of `L(1, χ)` for non-principal characters is the load-bearing analytic step.

## Duplicate detection (this is the load-bearing observation)

The slug as stated **duplicates** results already verified in the gallery and
already in Mathlib. Specifically:

| Existing gallery entry | Status | Source | What it proves |
|---|---|---|---|
| `dirichlets-theorem` | **verified**, `mathlib` badge | `proofs/Proofs/DirichletsTheorem.lean` | Full Dirichlet's theorem via Mathlib's `Nat.infinite_setOf_prime_and_eq_mod` (`Mathlib.NumberTheory.LSeries.PrimesInAP`). |
| `dirichlets-theorem` again | same | line 210: `theorem infinitely_many_primes_3_mod_4` | Explicit `a = 3, q = 4` specialisation, derived analytically. |
| `infinitude-primes-4k3` | **verified**, `original` badge | `proofs/Proofs/InfinitudePrimes4k3.lean` | Elementary Euclid-style proof for the `a = 3, q = 4` case (NO analytic number theory). |
| `dirichlets-theorem-oq-02` | **verified**, `original` badge | `proofs/Proofs/DirichletsTheoremOQ02.lean` | An additional elementary `≡ 3 (mod 4)` proof, packaged inside the Dirichlet OQ hierarchy. |

Hence the **conjecture-as-stated** is not open. Attempting the proof from scratch
would (a) duplicate `dirichlets-theorem`, and (b) duplicate the elementary
parent `infinitude-primes-4k3` (the very file from which this OQ derives).
This matches the pattern documented in
`feedback_researcher_millennium_sub_oq_duplicates.md`: seeker-extracted
"Is X true?" sub-OQs frequently duplicate a completed parent slug.

## Mathlib audit (full Dirichlet — already there)

The Mathlib API surface for full Dirichlet is mature at the pinned revision
(`leanprover-community/mathlib4` @ `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
Lean `v4.26.0`):

| Mathlib name | Purpose |
|---|---|
| `Nat.infinite_setOf_prime_and_eq_mod` | Full Dirichlet, ZMod formulation. |
| `Mathlib.NumberTheory.DirichletCharacter.Basic` | Dirichlet characters χ : (ℤ/qℤ)ˣ → ℂˣ. |
| `Mathlib.NumberTheory.LSeries.DirichletContinuation` | Analytic continuation of `L(s, χ)`. |
| `Mathlib.NumberTheory.LSeries.Nonvanishing` | `L(1, χ) ≠ 0` for non-principal χ. |
| `Mathlib.NumberTheory.LSeries.PrimesInAP` | Bridge: non-vanishing ⇒ infinitude. |

`DirichletsTheorem.lean` already exposes:
- `dirichlet_zmod` (ZMod), `dirichlet_modEq` (Nat / `% q`),
  `dirichlet_int` (ℤ-coefficient form),
  `dirichlet_frequently` (Filter.frequently),
  `dirichlet_constructive` (∃ prime > n in AP).

## Genuine open questions in the neighbourhood

Three narrow, *non-duplicative* S2 ACT candidates emerged from the audit.
All are "single-axiom discharges" or "bridge theorems" in the sense of
`feedback_researcher_millennium_sub_oq_duplicates.md`.

### S2(a) — Analytic-to-elementary bridge corollary

State and prove:
```lean
theorem InfinitudePrimes4k3.infinite_primes_eq_three_mod_four_via_dirichlet :
    { p : ℕ | p.Prime ∧ p % 4 = 3 }.Infinite :=
  -- Specialisation of `dirichlets-theorem.dirichlet_modEq` at (a = 3, q = 4),
  -- with the elementary parent's conclusion stated in the same shape.
  ...
```

**Value**: explicitly witnesses the two existing proofs (elementary in
`InfinitudePrimes4k3.lean`, analytic in `DirichletsTheorem.lean`) prove the
*same set-level statement*. Currently the two files state it in superficially
different shapes (`∀ n, ∃ p > n, p.Prime ∧ p % 4 = 3` vs
`{p | p.Prime ∧ (p : ZMod 4) = 3}.Infinite`) so a downstream consumer has to
re-bridge. ~25 lines, pre-Aristotle. **Recommended primary S2.**

### S2(b) — Elementary proof of "infinitely many primes ≡ -1 (mod q)" for q ∈ {3, 4, 6, 8, 12}

The Euclid-style argument `N = q · M! - 1` works for any `q` such that the
character group `(ℤ/qℤ)ˣ` has the property that the principal subgroup is
exactly `{1}` — equivalently, the only quadratic character mod q is `(·/q)`.
Concretely: `q ∈ {3, 4, 6, 8, 12, 24}` all admit elementary `p ≡ -1 (mod q)`
infinitude proofs.

**Deliverable**: one parametric proof
```lean
theorem InfinitudePrimes.elementary_neg_one_mod (q : ℕ) (hq : q ∈ ({3,4,6,8,12,24} : Finset ℕ)) :
    { p : ℕ | p.Prime ∧ p % q = q - 1 }.Infinite
```
**Value**: actually new Lean content not currently in either gallery line.
Re-uses the `InfinitudePrimes4k3` argument structure but generalizes the
"product of 1-mod-q stays 1-mod-q" step to the quadratic-residue-free moduli.
~120 LOC, pre-Aristotle. Higher risk because the parametric case-split needs
care (the `q = 8` case requires Euler's criterion in mod-8 form).

### S2(c) — Explicit lower bound on `π_{3 mod 4}(x)` from the elementary proof

The elementary proof shows that for every n, there is a prime ≡ 3 (mod 4)
in the interval `(n, 4·(n+1)!]`. Cascading: from `n = 0, 1, 2, …` we get
at least `O(log log x)` primes ≡ 3 (mod 4) in `[1, x]` (a very weak bound,
but explicit and elementary). State and prove:
```lean
theorem InfinitudePrimes4k3.elementary_count_lower_bound (x : ℕ) (hx : 4 ≤ x) :
    ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)).card
      ≥ Nat.log 4 (Nat.log 2 x)
```

**Value**: makes the elementary proof's quantitative content explicit and
serves as a teaching deliverable showing that even the simplest infinitude
proof has explicit counting content. ~80 LOC, pre-Aristotle.

## Acceptance criteria

This open question's contribution is bounded by what is **genuinely new**.
S1 OBSERVE deliverable: this duplicate-detection survey. S2 deliverable:
*one* of the three S2 ACT candidates above (recommended: S2(a)).

A correct close-out narrative is:
> The seeker statement duplicates a parent gallery entry that is already
> verified and mathlib-badged. We capture the duplicate in OBSERVE and ship
> a narrow bridge corollary in ACT.

This is *not* a green light to attempt full Dirichlet from scratch. That work
is already done.

## Out of scope

- Re-proving Dirichlet's theorem (already done by `dirichlets-theorem` via
  Mathlib, by `DirichletsTheoremOQ02` via elementary methods for `a = 3, q = 4`,
  and by `InfinitudePrimes4k3` via the same elementary methods).
- Anything quantitative beyond S2(c)'s explicit elementary bound. The sister
  open question `dirichlets-theorem-oq-03` ("Linnik's theorem") is the right
  home for stronger quantitative work.
- Anything depending on `L(1, χ) ≠ 0`. The sister slug
  `dirichlets-theorem-oq-01` ("Siegel Zeros") owns that axis and is
  currently `axiomatized` with 5 axioms — that is the genuinely-open
  axis in this ecosystem.

## References

- `proofs/Proofs/DirichletsTheorem.lean` (lines 122, 130, 138, 146, 210)
- `proofs/Proofs/InfinitudePrimes4k3.lean` (230 lines, 7 theorems, 0 axioms)
- `proofs/Proofs/DirichletsTheoremOQ02.lean`
- Sister OQ-03 of the parent `infinitude-primes-4k3`:
  `infinitude-primes-4k3-oq-03` ("Infinitely Many Primes ≡ 1 (mod 4) —
  Elementary Proof"), verified, file `InfinitudePrimes4k3OQ03.lean`.
- Sister slug currently in S6 SCAFFOLD: `infinitude-primes-4k1-oq-03`,
  PR `fbcf52782a2` (mertens_log_density_4k1 target stated, build pending).
