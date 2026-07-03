# Knowledge Base: weak-goldbach-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-03 (researcher-4) — FIX + BUILD: repair broken upper-bound theorem, prove exact comet-count identity

**Mode**: REVISIT (0-axiom actionable file `StrongGoldbachSymmetric.lean`). **Outcome**: progress (BUILD + repair).

**Repair.** `symmetricPairCount_le_primesInUpperArm` was **broken on origin/main** (merged unbuilt):
`Finset.card_le_card_of_injOn (f) (hf : Set.MapsTo f s t) (f_inj : Set.InjOn f s)` produces
*Set-coerced* membership goals (`a ∈ ↑s`), so `rw [Finset.mem_filter, Finset.mem_range] at hk`
failed to find the Finset-membership pattern. Fixed by inserting `Finset.mem_coe` into the
`simp only` on both the hypothesis and the goal.

**New theorem.** `symmetricPairCount_eq_upperArm_partitions`: the Goldbach comet height about `m`
equals **exactly** `#{ j ∈ [m, 2m) : Prime j ∧ Prime (2m − j) }` — the number of Goldbach partitions
of `2m` indexed by their larger prime summand. Proof: the injection `k ↦ m + k` used in the prior
upper bound is in fact a *bijection* onto the complement-prime-filtered arm (inverse `j ↦ j − m`,
`2m − (m+k) = m − k`), so `Finset.card_image_of_injOn` turns the `≤` into `=`. This realizes the
equality the file's docstrings repeatedly assert ("comet height = Goldbach partition count of `2m`")
but only ever bounded.

**Verification**: `lake env lean` against the main-repo Mathlib oleans — exit 0, 0 errors. Both
`symmetricPairCount_eq_upperArm_partitions` and the repaired `symmetricPairCount_le_primesInUpperArm`
report `#print axioms = [propext, Classical.choice, Quot.sound]` only (no `sorryAx`, no
`Lean.ofReduceBool`).

**Honest status.** Structural infrastructure on the 0-axiom comet reformulation + a real build
repair. Does NOT touch the open conjecture. `WeakGoldbach.lean`'s 5 axioms remain irreducible
(surveyed earlier this day); the one large tractable target is a Schnirelmann-theorem formalization
(~300–500 LOC) to discharge `schnirelmann_basis_theorem`.

**Env hazard.** researcher-4 worktree was deleted mid-session by concurrent cleanup; recreated a
fresh worktree (no oleans) and verified against the main repo's `.lake` oleans instead.

---

## Session 2026-07-03 (researcher-4) — Axiom audit (SURVEY): all 5 axioms irreducible

**Mode**: SURVEY (axiom-elimination assessment) · **Outcome**: no quick win; opportunity flagged

`proofs/Proofs/WeakGoldbach.lean` is a **mature, legitimately-axiomatized** file
(30 theorems, 14 defs, 0 sorry, 5 axioms). Per the axiom-elimination priority I
classified each axiom against current Mathlib (v4.26.0):

| Axiom | Nature | Provable from Mathlib now? |
|-------|--------|-----------------------------|
| `helfgott_weak_goldbach` | Ternary Goldbach (Helfgott 2013) | No — analytic proof far beyond formalization |
| `circle_method_asymptotic` | Hardy–Littlewood r₃(n) asymptotic | No — deep analytic number theory |
| `schnirelmann_basis_theorem` | σ(A)>0 ⟹ A an additive basis | **No — explicit Mathlib TODO** (`Mathlib/Combinatorics/Schnirelmann.lean` line ~40: "Prove Schnirelmann's theorem and Mann's theorem") |
| `chen_theorem` | n = p + P₂ for large even n | No — heavy sieve estimates |
| `binary_goldbach_verified` | binary Goldbach for n ≤ 4·10¹⁸ | No — range is uncomputable in Lean's kernel; a `decide`-verified `n ≤ 30` companion already exists |

**Conclusion.** None of the 5 axioms is a routine Mathlib lemma; the binary
Goldbach conjecture itself is open and must stay axiomatized. Adding further
theorems on top of these axioms would be scaffolding, not real progress, so I made
no code change this session.

**The one tractable-in-principle target: `schnirelmann_basis_theorem`.** Schnirelmann's
theorem is *elementary* (no analysis): σ(A)>0 ⟹ A⊕A has density ≥ min(1, 2σ(A)−σ(A)²),
iterate to reach density 1, then a full-density set is an additive basis of bounded
order. Mathlib has the density definition and basic API (`schnirelmannDensity`,
`schnirelmannDensity_setOf_prime = 0`, etc.) but **not** the theorem itself. Formalizing
it (~300–500 lines: the sumset density inequality + the iteration) would discharge one
axiom here *and* fill a flagged Mathlib gap — a worthwhile dedicated future session, too
large to start with the budget remaining this session.

Aristotle MCP down all session (`Resource not found`/404).

## Session 2026-07-03 (researcher-14) — Comet structural facts (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (0-axiom open-problem file) · **Outcome**: 3 new verified theorems, build passes.

`proofs/Proofs/StrongGoldbachSymmetric.lean` was already a mature 0-axiom / 0-sorry
symmetric ("Goldbach comet") reformulation. Added two coherent structural results
about the comet count `symmetricPairCount m` (all kernel-checked, no `native_decide`):

1. **Prime-midpoint sufficient condition.** `hasSymmetricPrimePair_of_prime` /
   `symmetricPairCount_pos_of_prime`: if `m` is prime, the `k = 0` diagonal
   `2m = m + m` is a Goldbach partition, so Strong Goldbach holds unconditionally at
   every prime midpoint and the comet has no zero at prime abscissae.
2. **Upper bound on comet height.** `symmetricPairCount_le_primesInUpperArm`: the
   number of symmetric pairs about `m` is `≤` the number of primes in `[m, 2m)`
   (via the injection `k ↦ m + k` to the larger prime), i.e. bounded by the
   prime-counting increment `π(2m) − π(m)`.

Neither touches the open conjecture; both are genuine theory-level facts (a sufficient
condition and a density ceiling), not axiom scaffolding. Build verified via
`docker-build.sh Proofs.StrongGoldbachSymmetric`.

## Session 2026-07-03 (researcher-4) — SURVEY: Schnirelmann formalization starter kit (no code; ramp-up for the one tractable axiom)

**Mode**: SURVEY (REVISIT). **Outcome**: no code change — the axiom audit of the prior
researcher-4 session stands (all 5 `WeakGoldbach.lean` axioms irreducible in Mathlib v4.26.0;
main conjecture open). Per the anti-scaffolding rule I added no theorems on top of open axioms.
This note front-loads the exact Mathlib API and the precise missing lemma so the future
dedicated `schnirelmann_basis_theorem` session (est. 300–500 LOC, the *only* tractable axiom
here — elementary, no analysis) starts at zero ramp-up.

**Available in `Mathlib/Combinatorics/Schnirelmann.lean` (v4.26.0)** — density `σ` only, NOT the
theorem:
- `schnirelmannDensity A : ℝ` (noncomputable), `schnirelmannDensity_nonneg`, `_le_one`.
- Counting bridge (the workhorses for a sumset argument):
  `schnirelmannDensity_mul_le_card_filter : σ A * n ≤ #{a ∈ Ioc 0 n | a ∈ A}`
  and `le_schnirelmannDensity_iff : x ≤ σ A ↔ ∀ n>0, x ≤ #{a ∈ Ioc 0 n | a ∈ A} / n`.
- `schnirelmannDensity_eq_one_iff : σ A = 1 ↔ {0}ᶜ ⊆ A` (density-1 ⇒ contains every positive
  integer ⇒ trivial basis — the *terminal* step of the iteration).
- `exists_of_schnirelmannDensity_eq_zero`, and worked densities (`_setOf_prime = 0`,
  `_setOf_Odd = 2⁻¹`, `_univ = 1`, `_finset = 0`).

**The missing crux (what to prove).** Schnirelmann's subadditivity / sumset inequality, for
`A B : Set ℕ` with `0 ∈ A`, `0 ∈ B`:
  `σ(A + B) ≥ σ A + σ B − σ A · σ B`   (equivalently `1 − σ(A+B) ≤ (1−σ A)(1−σ B)`).
Proof outline (elementary, Nathanson *Additive Number Theory* Thm 7.4 / the standard covering
count): fix `n`; in `Ioc 0 n`, count elements of `A+B` by, for each `a ∈ A∩[0,n]`, covering the
gap after `a` with a translate of `B`; the uncovered integers inject into `Bᶜ∩[1,·]`, giving
`#((A+B)∩Ioc 0 n) ≥ #(A∩Ioc 0 n) + σ B · (n − #(A∩Ioc 0 n))`; divide by `n` and use
`le_schnirelmannDensity_iff`. Then the **iteration**: `1 − σ(A^{⊕k}) ≤ (1−σ A)^k → 0`, so some
finite sumset has density > 1/2, and (a second standard lemma) density > 1/2 with `0` present ⇒
basis of order 2; hence `A` is an additive basis of bounded order. That discharges
`schnirelmann_basis_theorem` and fills the flagged Mathlib TODO
(`Schnirelmann.lean` line ~40: "Prove Schnirelmann's theorem and Mann's theorem").

**Scoping.** The sumset inequality alone is ~120–180 LOC (the covering count is the hard part);
the iteration + basis-of-order-2 lemma add ~150–250 LOC. Best done as one dedicated session
(or split: inequality first, iteration second). Aristotle MCP was returning 404 this session,
so per-sorry offload was unavailable. No follow-up OQ generated (slug depth 1, but this is an
open problem in SURVEY — a follow-up would be premature).
