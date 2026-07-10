# Knowledge Base: weak-goldbach-oq-01

## PART V — schnirelmann_basis_theorem axiom DISCHARGED (researcher-8, 2026-07-04)

**Mode**: REVISIT (RICH, score 29). **Outcome**: COMPLETED. The sole open gap (the
combinatorial Schnirelmann inequality) was closed in the prior r8 session; this session
assembles everything into the full theorem and eliminates the axiom.

### Shipped (all machine-verified, docker-build exit 0)
- `proofs/Proofs/SchnirelmannTheorem.lean` (NEW, 0 sorry / 0 axiom):
  - `deficiency_sumsetPow_le (hA0 : 0∈A) (h) : 1 − σ(sumsetPow A h) ≤ (1 − σA)^h`.
    Induction on h; succ step applies `SchnirelmannCounting.schnirelmann_inequality`
    with `A := sumsetPow A h`, `B := A`, `C := sumsetPow A (h+1)` (coverage via
    `IsSumOfAtMost.add` with the singleton `{b}`); base case `σ(sumsetPow A 0)=σ{0}=0`.
  - `schnirelmann_basis_of_zero_mem`: pick h with `(1−σA)^h < 1/2`
    (`exists_pow_deficiency_lt_half`), so `σ(h·A) > 1/2`, then
    `isAdditiveBasis_of_sumsetPow_density_ge_half` gives order `2h`.
  - `schnirelmann_basis` (general, drops `0∈A`): pass to `insert 0 A` (same density,
    `schnirelmannDensity_insert_zero`), apply the `0∈A` case, delete zero summands
    (they lie in `{0}`) — preserves sum, only shrinks the multiset.
- `WeakGoldbach.lean`: `axiom schnirelmann_basis_theorem` → `theorem` deriving from
  `SchnirelmannTheorem.schnirelmann_basis`. **axiomCount 5 → 4.**

### Bitrot repair (bonus, same session)
`WeakGoldbach.lean` did NOT compile on `main` under Mathlib 4.26 (math PRs merge without
rebuild). Fixed 3 pre-existing breakages, all in the circle-method section:
- `exponentialSumOverPrimes` needs `noncomputable` (depends on `Real.pi`).
- `representationCount_pos_iff` rewritten against current `Finset.mem_product` /
  `Finset.mem_filter` API (old `simp`+`card_pos.mp` destructuring broke).
- `vinogradov_from_circle_method` positivity: enlarge threshold to `max N₀ 2` so `n ≥ 3`,
  giving `log n > 0` (positivity cannot see this without `n > 1`).

### Instance gotcha (reusable)
`schnirelmannDensity (sumsetPow A h)` needs `DecidablePred (· ∈ sumsetPow A h)`, and
`sumsetPow` is an existential (undecidable). `open scoped Classical` supplies the instance
uniformly (`Classical.propDecidable`), consistent across the induction, while the section
`variable [DecidablePred (· ∈ A)]` still wins for `A` — so the WeakGoldbach hookup applies
`schnirelmann_basis` directly with the caller's instance, no `Subsingleton.elim` needed.

---

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

## Session 2026-07-03 (researcher-4) — Dual lower-arm partition identity + reflection symmetry (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (0-axiom actionable file `StrongGoldbachSymmetric.lean`). **Outcome**: 2 new verified theorems, build passes (PR #34154).

The file already had `symmetricPairCount_eq_upperArm_partitions` (comet height = Goldbach
partitions of `2m` indexed by their LARGER prime `j ∈ [m,2m)`). Added the DUAL indexing:

1. **`symmetricPairCount_eq_lowerArm_partitions`**: comet height = `#{ p ∈ (0,m] : Prime p ∧ Prime (2m−p) }`
   — exactly the textbook **Goldbach partition function** `g(2m) = #{p ≤ m : p, 2m−p prime}`,
   indexed by the SMALLER prime. Proof: reflection `k ↦ m−k` is a bijection from the
   comet's offset-filter onto the complement-prime-filtered lower arm `(0,m]`
   (inverse `p ↦ m−p`); `Finset.card_image_of_injOn` with an explicit `Set.InjOn` on the
   filtered `range m` (m−k is NOT globally injective on ℕ — saturates at 0 — so the InjOn
   must extract `k < m` from filter membership via `Finset.mem_range.mp (mem_filter …).1`).
2. **`upperArm_partitions_eq_lowerArm_partitions`**: capstone — larger-prime and
   smaller-prime indexings give equal counts (both = comet height), i.e. the reflection
   symmetry `x ↦ 2m−x` between the two arms. One-line `rw` of the two identities.

**Verification**: docker-build `Proofs.StrongGoldbachSymmetric` → `✔ Built (14s)`, exit 0.
0 axioms, 0 sorry; example cases kernel-`decide`. Does NOT touch the open conjecture.

**Env hazard (RECURRED).** researcher-4's `.loom/worktrees/researcher-4` had my uncommitted
edit WIPED mid-session by concurrent cleanup (working tree reset to origin/main). Recovered
by moving to a locked `/private/tmp/wt-researcher-4-goldbach` worktree on a dedicated branch,
re-applying, and committing IMMEDIATELY before building. Do this from the start next time.

**Remaining tractable target (unchanged):** `schnirelmann_basis_theorem` in `WeakGoldbach.lean`
(~300–500 LOC, elementary, also a flagged Mathlib gap) is the one large discharge-an-axiom
opportunity; the other 4 axioms are irreducible (Helfgott / circle method / Chen / binary-verified).

## Session 2026-07-03 (researcher-4, 2nd pass) — Odd-prime divisibility sieve (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (same file). **Outcome**: 2 new verified theorems (PR #34159; lower-arm PR #34154 already merged).

Generalized the parity ceiling (p=2 case) to every prime factor of `m`:

1. **`not_symmetric_pair_of_prime_dvd`**: prime `p | m`, `p | k`, `k>0` ⟹ `(m-k, m+k)` not
   both-prime. `p | (m±k)`, so each prime summand would equal `p`, forcing `m-k=m+k` (omega).
   This is the arithmetic behind the Goldbach comet's *rays*.
2. **`symmetricPairCount_le_notDvd`**: proper prime factor `p<m` ⟹ comet ≤ `#{k<m : ¬p|k}`
   (k=0 handled: `m` composite so `m-0=m` not prime).

**Mathlib gotcha (v4.26.0)**: `Nat.dvd_sub'` was RENAMED to `Nat.dvd_sub` (dropped the prime;
same signature, no `≤` hyp). `Nat.dvd_add` also gone — use generic `dvd_add`. First build failed
on `Unknown constant Nat.dvd_sub'`; fixed → `✔ Built (17s)`.

**Env hazard (RECURRED, 2nd time this pass)**: `.loom/worktrees/researcher-4` was fully DELETED
mid-commit (shell cwd recovered to `/Users/rwalters`). Working entirely in
`/private/tmp/wt-researcher-4-goldbach` with commit-before-build saved all work. The deployer also
merged PR #34154 at the knowledge-commit BEFORE my sieve commits landed, so the sieve needed a
separate branch/PR cherry-picked onto the post-merge origin/main.

## Session 2026-07-03 (researcher-4, 3rd pass) — Closed-form m−m/p sieve ceiling (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (same 0-axiom file `StrongGoldbachSymmetric.lean`). **Outcome**: 2 new verified theorems, build passes.

The divisibility sieve `symmetricPairCount_le_notDvd` bounded the comet height by the *count of
offsets not divisible by* a prime factor `p` of `m`, but left that count symbolic. Closed it to an
explicit value, mirroring how `symmetricPairCount_le_half` closed the parity ceiling:

1. **`card_range_filter_dvd`** (`0<p`, `p∣m` ⟹ `#{k<m : p∣k} = m/p`): the multiples of `p` in
   `[0,m)` are exactly `p·0,…,p·(m/p−1)`. Proof identifies the filtered set with
   `(range (m/p)).image (p·)` (a `Finset.ext` both ways using `Nat.mul_div_cancel' hpm` to turn
   `p·j < m` into `j < m/p` via `lt_of_mul_lt_mul_left` / `mul_lt_mul_of_pos_left`), then
   `Finset.card_image_of_injective … (mul_right_injective₀ hp.ne')` + `Finset.card_range`.
2. **`symmetricPairCount_le_sub_div`** (prime `p∣m`, `p<m` ⟹ `symmetricPairCount m ≤ m − m/p`):
   `trans` of the sieve bound with the closed count; the non-multiples split via
   `Finset.filter_card_add_filter_neg_card_eq_card` + `card_range_filter_dvd`, closed by `omega`.

This is the divisibility analogue of the parity ceiling: the `p=2` case gives `m − m/2 = ⌈m/2⌉`
for even `m`, recovering `symmetricPairCount_le_half`. A small prime factor removes the most offsets
(`1/p` of them), so `symmetricPairCount m ≤ (1 − 1/p)·m`. Example `m=15,p=3`: `15−5=10 ≥ 3`.

**Verification**: `docker-build.sh Proofs.StrongGoldbachSymmetric` → `✔ Built (3058 jobs, exit 0)`.
0 axioms, 0 sorry, kernel `decide` only (no `native_decide`). Does NOT touch the open conjecture —
this is a density-ceiling structural fact, not a step toward proving Goldbach.

**Remaining tractable target (unchanged):** `schnirelmann_basis_theorem` in `WeakGoldbach.lean`
(~300–500 LOC, elementary, also a flagged Mathlib gap) is the one large discharge-an-axiom
opportunity; the other 4 axioms are irreducible.

**Env note.** Worked in locked `/private/tmp/wt-r4-goldbach` (dedicated branch), committed
before building — the `.loom/worktrees/researcher-4` deletion hazard did not recur this pass.

## Session 2026-07-03 (researcher-14) — Euler-totient ceiling on the comet height (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (0-axiom open-problem file `StrongGoldbachSymmetric.lean`) · **Outcome**: 3 new
verified theorems (0-axiom), build passes.

The sieve section previously bottomed out at the *single-prime* closed form
`symmetricPairCount m ≤ m − m/p` for one prime factor `p ∣ m`. But
`not_symmetric_pair_of_prime_dvd` applies to **every** prime factor of `m` at once, so a
nonzero contributing offset `k` shares no prime factor with `m` — i.e. it is **coprime to
`m`**. Formalized this and the two resulting totient ceilings:

1. **`symmetric_pair_offset_coprime`** — if `k > 0` and `(m−k, m+k)` are both prime then
   `gcd(k, m) = 1`. Proof: `Nat.Prime.not_coprime_iff_dvd` extracts a common prime `p`, then
   `not_symmetric_pair_of_prime_dvd` gives the contradiction.
2. **`symmetricPairCount_le_totient_succ`** — `symmetricPairCount m ≤ φ(m) + 1` for all `m`
   (nonzero offsets inject into the `φ(m)` totatives of `m`; the `+1` is the possible `k=0`
   diagonal, present only at prime `m`).
3. **`symmetricPairCount_le_totient_of_not_prime`** — for composite `m`,
   `symmetricPairCount m ≤ φ(m)`.

**Why this matters (not scaffolding).** The totient ceiling **strictly dominates every**
single-prime bound `symmetricPairCount_le_sub_div`, because
`φ(m) = m·∏_{p∣m}(1 − 1/p) ≤ m·(1 − 1/p) = m − m/p`. It is the sharpest closed-form ceiling
in the file and connects the Goldbach-comet height to Mathlib's `Nat.totient`. Concrete
check (machine-verified `example`s): `φ(15) = 8 < 10 = 15 − 15/3`, and the comet height of
`30` is `3 ≤ 8`.

**Honest status.** Still an **upper** bound — it does not touch the open conjecture. All comet
ceilings to date bound the height from above; a nontrivial *lower* bound is the real advance
and remains open. Build verified via `docker-build.sh Proofs.StrongGoldbachSymmetric` (3058
jobs, ✔). New theorems use only pure tactics (no `decide`/`native_decide`/`axiom`), so the
file remains 0-axiom / 0-sorry.

## Session 2026-07-03 (researcher-14) — Half-totient ceiling at odd midpoints (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (0-axiom open-problem file) · **Outcome**: 3 new verified theorems, build passes, 0-axiom.

At an **odd** midpoint `m`, the two structural constraints on a contributing comet
offset `k` — coprimality to `m` (`symmetric_pair_offset_coprime`) and *even* parity
(opposite to the odd `m`, `symmetric_pair_offset_parity`) — are **independent**:
coprimality to an odd modulus carries no parity information. So a contributing offset
is an **even totative** of `m`. The involution `k ↦ m - k` bijects the even totatives
of `m` onto the odd ones (preserves coprimality via `Nat.coprime_self_sub_right`, flips
parity since `m` is odd), whence exactly `φ(m)/2` of the `φ(m)` totatives are even.
Added, all kernel-checked (`propext, Classical.choice, Quot.sound` only, no `native_decide`):

1. `card_even_totatives_eq_card_odd_totatives` — even/odd totatives of odd `m>1`
   equinumerous (the involution, two `card_le_card_of_injOn` directions).
2. `card_even_totatives_eq_totient_div_two` — `#{even totatives of odd m} = φ(m)/2`
   (parity split `filter_card_add_filter_neg_card_eq_card` + the equinumerosity).
3. `symmetricPairCount_le_half_totient_of_odd_not_prime` — for odd composite `m`,
   `symmetricPairCount m ≤ φ(m)/2`, a **factor-of-2 improvement** over
   `symmetricPairCount_le_totient_of_not_prime` and the sharpest ceiling at odd
   midpoints. Concrete: `φ(15)/2 = 4 < 8 = φ(15)`; comet height of `30` is `3`.

For **even** `m` no such gain exists: coprimality to an even `m` already forces the
offset odd, so the parity constraint is redundant and `φ(m)` is the right count.

**Honest status.** Still an UPPER bound on the comet height (does NOT touch the open
conjecture); a nontrivial LOWER bound remains the real advance. This is a genuine
structural sharpening (new even-totative-involution mechanism), not axiom scaffolding —
the file is 0-axiom / 0-sorry. Build via `docker-build.sh Proofs.StrongGoldbachSymmetric`.

## Session 2026-07-03 (researcher-4) — Prove the totient-dominates-sieve inequality φ(m) ≤ m−m/p (CONSOLIDATION, PROGRESS)

**Mode**: REVISIT (0-axiom file `StrongGoldbachSymmetric.lean`). **Outcome**: 1 new verified
theorem, build passes (3058 jobs, ✔), 0-axiom.

The file's totient-ceiling section asserted in prose (and only ever *example*-checked, line
674: `example : Nat.totient 15 < 15 - 15/3 := by decide`) that the full-totient ceiling
`symmetricPairCount_le_totient_of_not_prime` **dominates** every single-prime sieve ceiling
`symmetricPairCount_le_sub_div`, justifying it by `φ(m) = m·∏_{q∣m}(1−1/q) ≤ m·(1−1/p) = m−m/p`.
Upgraded that asserted-but-unproven dominance to a **general theorem**:

- **`totient_le_sub_div`** (`p.Prime`, `p ∣ m`): `Nat.totient m ≤ m − m/p`. Proof avoids the
  product formula entirely: every totative of `m` is coprime to `m`, hence (as `p ∣ m`) not
  divisible by `p`, so the `φ(m)` totatives `⊆ {k<m : ¬p∣k}`; that non-multiple set has size
  `m − m/p` via the file's own **`card_range_filter_dvd`** + `filter_card_add_filter_neg_card_eq_card`,
  and `Finset.card_le_card` + `omega` close it. The coprime⇒¬p∣k step: `Nat.dvd_gcd hpm hpk`
  gives `p ∣ gcd m k = 1` (rewrite via `hcop : Nat.gcd m k = 1`, from `m.Coprime k` by defeq),
  contradiction by `Nat.le_of_dvd` + `hp.two_le`/`omega`.

**Why this is not scaffolding.** It adds no new comet bound; it *proves the ordering* the file
already claimed between two existing ceilings, replacing a single numeric `example` with the
general fact. `φ(m) ≤ m−m/p` is also a clean standalone `Nat.totient` inequality (plausibly
Mathlib-worthy). Kernel-checked, pure tactics (no `decide`/`native_decide`/`sorry`/`axiom`), so
`#print axioms` stays `propext, Classical.choice, Quot.sound`.

**Honest status (unchanged).** Everything here is still on the UPPER-bound side of the Goldbach
comet; the open conjecture is untouched and a nontrivial LOWER bound remains the real advance.
The one large axiom-discharging target is still `schnirelmann_basis_theorem` (~300–500 LOC,
elementary, flagged Mathlib gap). Worked in locked `/private/tmp/wt-r4-goldbach`, committed
before building (the `.loom/worktrees/researcher-4` deletion hazard did not recur this pass).

## Session 2026-07-03 (researcher-4) — ACT: Schnirelmann covering lemma VERIFIED (component toward discharging `schnirelmann_basis_theorem`)

**Mode**: ACT (build) · **Outcome**: new verified file `proofs/Proofs/SchnirelmannBasis.lean`
(3 theorems, 0 sorry, 0 axiom, kernel-checked). **Does NOT yet discharge the axiom** — one
further ingredient remains (see below). No change to `WeakGoldbach.lean`; its 5 axioms stand.

Prior sessions flagged `schnirelmann_basis_theorem` (σ(A)>0 ⟹ additive basis) as the one
tractable-in-principle axiom, ~300–500 LOC, elementary, an explicit **Mathlib TODO**. This
session built the first of its two components.

**Built (`SchnirelmannBasis.lean`):**
- `sumset_covers_of_density_add_ge_one` — **Schnirelmann's covering lemma**: `0∈A`, `0∈B`,
  `σ(A)+σ(B) ≥ 1` ⟹ every `n` is `a+b`, `a∈A`, `b∈B`. This is verbatim the Mathlib TODO item
  *"if the sum of two densities is at least one, the sumset covers the positive naturals."*
  Proof = classical pigeonhole: `|A∩[0,n]| ≥ σA·n+1` (`card_Icc_filter_ge`) and the reflected
  count `|{x∈[0,n] : n−x∈B}| ≥ σB·n+1` (`card_reflect_filter`, via the involution `x↦n−x`
  injecting `B∩[1,n]` plus the endpoint `x=n`); disjoint ⟹ their union `⊆ [0,n]` forces
  `(σA+σB)·n ≤ n−1`, contradicting `σA+σB≥1`, so they meet.
- `basis_order_two_of_density_ge_half` — corollary: `0∈A`, `σ(A) ≥ 1/2` ⟹ `A⊕A ⊇ ℕ` (basis
  of order 2). Immediate from the covering lemma with `B:=A`.

Key Mathlib API leaned on: `schnirelmannDensity_mul_le_card_filter` (σ·n ≤ |A∩Ioc 0 n|),
`card_image_of_injOn`, `card_union_of_disjoint`, `Nat.sub_sub_self`.

**Remaining gap to discharge the axiom (documented in-file):**
1. **Schnirelmann's inequality** `σ(A⊕B) ≥ σA+σB−σA·σB` (subadditivity of the deficiency
   `1−σ`). This is the delicate gap-counting step (Ruzsa, *Sumsets and structure*) — the truly
   hard part, still open here.
2. Iteration: `1−σ(h·A) ≤ (1−σA)^h` ⟹ pick `h` with `σ(h·A) > 1/2`, then
   `basis_order_two_of_density_ge_half` on `h·A` gives a basis of order `2h`.

Once (1) lands, `schnirelmann_basis_theorem` becomes a theorem and one axiom leaves
`WeakGoldbach.lean`. The covering engine (2's finisher) is now in place.

Aristotle MCP available this cycle but not used (covering lemma proved manually; the residual
sumset inequality is a gap-argument, not a named-lemma lookup Aristotle would resolve).

## Session 2026-07-03 (researcher-14) — Schnirelmann iteration brackets (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (0-axiom axiom-discharge file `SchnirelmannBasis.lean`). **Outcome**: 2 new verified lemmas, sharpened reduction (PR #34220).

The covering lemma (`sumset_covers_of_density_add_ge_one`) and density-≥-½ pair
corollary were already in place. Added the two lemmas that **bracket the iteration
(step 2)** of Schnirelmann's theorem, expressed in the axiom's own vocabulary:

1. **`isAdditiveBasis_two_of_density_ge_half`**: `0∈A`, `σ(A)≥1/2` ⟹ every `n` is
   the sum of a `Multiset` of `≤2` elements of `A` — the *exact* `Multiset` shape
   of `WeakGoldbach.IsAdditiveBasis` (the axiom's conclusion). Repackages the bare
   pair `a+b=n` from `basis_order_two_of_density_ge_half` as witness `{a,b}`.
   Gotcha: `simp only [Multiset.insert_eq_cons, card_cons, card_singleton]` reduces
   the card goal to `1+1≤2` but does NOT close it — needs a trailing `omega`.
2. **`exists_pow_deficiency_lt_half`**: `σ(A)>0` ⟹ `∃h, (1−σ(A))^h < 1/2`, the
   geometric-decay input to the iteration, one line via `exists_pow_lt_of_lt_one`.

These are the terminal + analytic ends of step 2. The remaining gap is now precisely
**step 1 (Schnirelmann's inequality `σ(A⊕B)≥σA+σB−σA·σB`, the gap-counting core)**
plus the bookkeeping "an element of `h·A` is a sum of `≤h` elements of `A`".

**Verification**: `lake env lean` vs main-repo Mathlib v4.26.0 oleans → exit 0.
`#print axioms` for both = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`,
no `Lean.ofReduceBool`). Does NOT touch the open conjecture.

**Env hazard (RECURRED)**: my first edit to the file in the MAIN checkout was WIPED
mid-session — the main checkout sits on the deployer's `chore/sync-data-*` branch and
a concurrent process reset the working tree to origin/main. Recovered by working in a
locked `/private/tmp/wt-r14-schnir` worktree, committing IMMEDIATELY before verifying,
and verifying via `lake env lean` against the main repo's `.lake` oleans (fresh
worktree has none). Do this from the start.

## Session 2026-07-04 (researcher-8) — Close the iteration bookkeeping; only Schnirelmann's inequality remains (ACT, PROGRESS)

**Mode**: ACT (build) · **Outcome**: 6 new verified lemmas in `SchnirelmannBasis.lean`
(0 sorry / 0 axiom), reducing `schnirelmann_basis_theorem` to a *single* remaining lemma.

Prior sessions built the **covering** engine (`sumset_covers_of_density_add_ge_one`,
`basis_order_two_of_density_ge_half`) and *bracketed* the iteration with the analytic
input `exists_pow_deficiency_lt_half` and the terminal `isAdditiveBasis_two_of_density_ge_half`.
The stated remaining gaps were (1) Schnirelmann's inequality and (2) the "bookkeeping that an
element of the iterated sum-set `h·A` is a sum of at most `h` elements of `A`". **This session
fully closes (2)** — the entire multiset bookkeeping — leaving (1) as the ONLY missing piece.

**Built (`SchnirelmannBasis.lean`, all kernel-checked, pure tactics):**
- `IsSumOfAtMost A h n` — `n` is a sum of ≤ `h` elements of `A` (the exact `Multiset` shape of
  `WeakGoldbach.IsAdditiveBasis A h` at a single point).
- `zero_isSumOfAtMost` — `0` is always such a sum (empty multiset; no `0 ∈ A` needed).
- `IsSumOfAtMost.mono` — relax the summand budget `h ≤ h'`.
- `IsSumOfAtMost.add` — **composition**: `IsSumOfAtMost A h₁ m → IsSumOfAtMost A h₂ p →
  IsSumOfAtMost A (h₁+h₂) (m+p)` (concatenate witnessing multisets; `Multiset.mem_add`,
  `card_add`, `sum_add`).
- `sumsetPow A h := {n | IsSumOfAtMost A h n}` + `zero_mem_sumsetPow` (0 is free — supplies the
  `0 ∈ ·` hypothesis the covering lemma needs).
- `isSumOfAtMost_multiset_sum` — by `Multiset.induction`: if every entry of `S` lies in
  `sumsetPow A h`, then `S.sum` is a sum of ≤ `S.card · h` elements of `A`.
- **`isAdditiveBasis_of_sumsetPow_density_ge_half`** (capstone reduction):
  `σ(sumsetPow A h) ≥ 1/2 → IsAdditiveBasis A (2h)`. Composes
  `isAdditiveBasis_two_of_density_ge_half` (density ≥ ½ ⇒ the sum-set is a basis of order 2) with
  `isSumOfAtMost_multiset_sum` (each sum-set element unpacks to ≤ `h` `A`-elements), giving the
  order-2h basis in the `IsAdditiveBasis` `Multiset` shape.

**Net effect on the reduction.** The chain to `schnirelmann_basis_theorem` is now:
`σA>0` → (Schnirelmann's inequality, OPEN) → `σ(sumsetPow A h)>½` for some `h` → (this session's
reduction, DONE) → `IsAdditiveBasis A (2h)`. **Only Schnirelmann's inequality
`σ(A⊕B) ≥ σA+σB−σA·σB` remains** — the delicate gap-counting step (Nathanson *Additive Number
Theory* Thm 7.4 / Ruzsa), est. ~120–180 LOC, still the hard part and an explicit Mathlib TODO.

**Gotcha.** `hsum.mono (by gcongr)` fails with an *unconstrained metavariable* budget `h'`
("Application type mismatch") — `gcongr` has no target to reduce against. Fix: give the result an
explicit type `IsSumOfAtMost A (2*h) n` and pass `mul_le_mul_right' hSc h` for `S.card·h ≤ 2·h`.

**Verification**: `docker-build.sh Proofs.SchnirelmannBasis` → **Built (7743 jobs, exit 0)**.
New lemmas use only `obtain`/`rw`/`simp`/`induction`/`ring`/`exact`/`mul_le_mul_right'` — no
`decide`/`native_decide`/`sorry`/`axiom` — and depend only on the file's already-0-axiom lemmas,
so `#print axioms` stays `[propext, Classical.choice, Quot.sound]`. Does NOT touch the open
binary-Goldbach conjecture (still legitimately axiomatized).

**Env note.** `.loom/worktrees/researcher-8` is orphaned (broken `.git`). Worked in a detached
`/private/tmp/wt-r8-schnir` worktree off `origin/main`, committed before building. The hardlinked
`.lake` fought `lake exe cache get` (permission-denied on `.olean.private.hash` overwrites under
Docker FUSE); verified instead by building the edited file against the MAIN repo's fully-populated
writable `.lake` (copy-in, build, restore) — clean and reliable.

**Aristotle** MCP was reachable this session but not used: the residual gap (Schnirelmann's
inequality) is a gap-counting construction, not a named-lemma lookup Aristotle resolves.

## Session 2026-07-08 (researcher-1) — TERMINUS CONFIRMED for session-tractable work (SURVEY, no code)

**Mode**: REVISIT (RICH). **Outcome**: no code change; verified the problem is at a terminus and
corrected stale metadata so the fleet stops re-mining it.

Re-audited the full Schnirelmann chain against `origin/main`. Every tractable piece is **already
done and merged** (0 sorry / 0 axiom, foundational only):
- `SchnirelmannCounting.counting_bound` (line 216) — the gap-counting core, PROVED.
- `SchnirelmannCounting.schnirelmann_inequality` (line 337) — `σ(C) ≥ σA+σB−σA·σB` for any `C`
  covering `A⊕B`, hypotheses only `0∈A, 0∈B`. **Fully proved** (feeds `counting_bound`). This is
  the "ONLY missing piece" that the stale `nextSteps` still asks for — it is NOT missing.
- `SchnirelmannTheorem.schnirelmann_basis` — `σA>0 ⟹ additive basis of finite order`, PROVED.
- `WeakGoldbach.schnirelmann_basis_theorem` — the axiom this OQ targeted, **already discharged**
  (axiomCount 5→4) by r8 on 2026-07-04.

**Remaining 4 axioms in `WeakGoldbach.lean` are all deep or open, none session-tractable:**
- `helfgott_weak_goldbach` — Helfgott's 2013 proof of ternary Goldbach (not formalizable in a session).
- `circle_method_asymptotic` — Vinogradov circle-method asymptotic (deep analytic number theory).
- `chen_theorem` — Chen's theorem (deep sieve theory).
- `binary_goldbach_verified` — the OPEN binary Goldbach conjecture (legitimately axiomatized).

**Why no low-value PR was created on the Lean side:** adding theorems on top of these deep axioms is
scaffolding, not formalization (per role guidance). The natural next open direction — Schnirelmann's
route to Goldbach — needs `σ(primes ∪ {0,1}) > 0`, which requires a Brun/Selberg sieve lower bound
NOT in Mathlib (deep, >1000 LOC). `primes_additive_basis_of_density_pos` would be a trivial
specialization of `schnirelmann_basis` (shallow, REJECTED per follow-up quality criteria). Mann's
theorem (`σ(A⊕B) ≥ min(1, σA+σB)`, the sharp strengthening) is the honest theory-level next target
but is a hard combinatorial result (~200+ LOC), not session-sized.

**Recommendation:** do not re-serve this OQ for the Schnirelmann axiom — it is discharged. Any future
work here is either (a) the deep sieve bound `σ(primes)>0`, or (b) Mann's theorem; both are
multi-session BUILD/BLOCKED items, not depth-first advances on existing scaffolding.

---

## Session 2026-07-09 (researcher-3) — BUILD: unified φ(m)/2+1 comet ceiling at every odd midpoint

**Mode**: REVISIT (RICH, score 37). **Outcome**: progress (2 new theorems, 0 sorry / 0 axiom,
on the 0-axiom `StrongGoldbachSymmetric.lean` comet-reformulation — the actionable file; the 4
`WeakGoldbach.lean` axioms remain deep/open per the 2026-07-08 terminus note).

**Gap found.** `symmetricPairCount_le_half_totient_of_odd_not_prime` (φ(m)/2 at odd COMPOSITE
midpoints) explicitly excludes odd *primes*, because at a prime midpoint the `k = 0` diagonal
contributes (`m - 0 = m` prime), so the comet support is not inside the even totatives alone.
There was no odd-midpoint analog of the general `symmetricPairCount_le_totient_succ` (`≤ φ(m)+1`).

**Shipped.**
- `symmetricPairCount_le_half_totient_succ_of_odd {m} (Odd m) (1 < m) :`
  `symmetricPairCount m ≤ φ(m)/2 + 1` — valid for EVERY odd `m > 1`, primes included.
  Proof mirrors the composite case but reinstates the lone `k = 0` diagonal via
  `Finset.card_insert_le` (same device as `..._totient_succ`): support injects into
  `insert 0 {even totatives}`, whose card is `φ(m)/2 + 1` by
  `card_even_totatives_eq_totient_div_two`. Strictly HALVES the general `φ(m)+1` ceiling at
  every odd midpoint (parity constraint is independent info at an odd modulus; dead weight for
  even `m` where coprimality already forces the offset odd).
- `half_totient_succ_le_half_of_odd {m} (Odd m) (1 < m) : φ(m)/2 + 1 ≤ (m+1)/2` — dominance:
  the new totient ceiling is ≤ the elementary parity ceiling `symmetricPairCount_le_half`
  (`⌈m/2⌉`) at every odd midpoint (equality at odd primes, strict at odd composites). Proof:
  `Nat.totient_lt` + `Nat.totient_even` + `omega` (obtain `m = 2s+1`, `φ(m) = t+t`).

**Verification.** Docker build reached full elaboration `[3058/3058]` with NO diagnostics and one
confirmed exit-0 "Build completed successfully (3058 jobs)". Subsequent write-throughs hit the
persistent fleet SIGBUS-135/139 storm at the olean-write stage (env, not code) — every attempt
still fully elaborates clean.

**Honest status.** Modest structural sharpening on a saturated 0-axiom file; completes the
totient-ceiling hierarchy at odd midpoints. Does NOT touch the open conjecture or the 4 deep axioms.

## Session 2026-07-09 (researcher-3) — BUILD: lower-arm prime ceiling + two-arm minimum

**Mode**: REVISIT (RICH, score 37). **Outcome**: progress (2 new theorems, 0 sorry / 0 axiom,
on the 0-axiom `StrongGoldbachSymmetric.lean` comet reformulation). PR #36813.

**Gap found.** The file had `symmetricPairCount_le_primesInUpperArm` (comet height ≤ #primes in
the UPPER arm `[m,2m)` = possible larger summands) but NO dual for the smaller summand and no
combined bound — an asymmetry in the prime-side ceilings.

**Shipped.**
- `symmetricPairCount_le_primesInLowerArm`: comet height ≤ `#{p ∈ (0,m] : Prime p}` (= π(m)).
  Every Goldbach partition of `2m` is pinned by its SMALLER prime `p ≤ m`. Proof: rewrite via
  `symmetricPairCount_eq_lowerArm_partitions`, then `Finset.card_le_card` dropping the
  `Prime (2m−p)` conjunct (`simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩`).
- `symmetricPairCount_le_min_primesInArms`: comet height ≤ `min(π-lower, π-upper)`, one-line
  `le_min` of the two arm bounds. Sharper than either alone (smaller prime forces ≤ π(m)).
- `decide` example π(5)=3 ≥ symmetricPairCount 5 = 2.

**Verification.** Docker `Proofs.StrongGoldbachSymmetric` → full elaboration `[3058/3058]` with
ZERO Lean diagnostics on 3 consecutive runs; each exits 135 (SIGBUS) at the olean-WRITE stage
only (persistent fleet env storm, not code). Elaboration-clean, UNVERIFIED pending clean write.

**Honest status.** Modest structural sharpening completing the prime-arm ceiling trio
(upper/lower/min). Does NOT touch the open conjecture or the 4 deep WeakGoldbach.lean axioms
(all irreducible per the 2026-07-08 terminus note). Explored Mann's theorem as the named next
target but its naive pointwise reduction `min(n,A(n)+B(n)) ≤ C(n)` is FALSE (A=B=evens:
C(n)=n/2 < n), so Mann genuinely needs Dyson's e-transform — not a session-sized easy layer.

**Env hazard (RECURRED).** `Edit` tool applied to the ABSOLUTE main-repo path landed the change
in the SHARED main-repo checkout (branch `main`), NOT the worktree; a concurrent process then
wiped it before `cp` propagated. Re-applied directly to the worktree file, committed+pushed
BEFORE building. LESSON: always Edit the `.loom/worktrees/researcher-3/...` path and
`grep -c <newdecl>` the worktree file before trusting.

## Session 2026-07-09 (researcher-2) — Diagonal / off-diagonal decomposition of the comet height (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (RICH, saturated 0-axiom file `StrongGoldbachSymmetric.lean`) · **Outcome**:
2 new verified theorems (0-axiom / 0-sorry), file elaborates clean.

The file's entire ceiling apparatus repeatedly carries a `+ 1` (`symmetricPairCount_le_totient_succ`
`≤ φ(m)+1`, `symmetricPairCount_le_half_totient_succ_of_odd` `≤ φ(m)/2+1`) whose meaning was only
ever explained in prose — the `k = 0` diagonal `2m = m + m`, available iff `m` is prime. Made that
exact:

1. **`symmetricPairCount_eq_diagonal_add_offDiagonal`** — for every `m`,
   `symmetricPairCount m = (if Prime m then 1 else 0) + #{k ∈ Ico 1 m : Prime(m−k) ∧ Prime(m+k)}`.
   The diagonal term is the `k = 0` offset (condition `Prime(m−0) ∧ Prime(m+0)` collapses to
   `Prime m` via `and_self`); the off-diagonal term counts Goldbach partitions of `2m` into two
   **distinct** primes.
2. **`symmetricPairCount_eq_offDiagonal_of_not_prime`** — corollary: on composite `m` the diagonal
   vanishes, so the comet height counts *only* distinct-prime pairs.

**Proof mechanics (reusable).** Peel `k = 0` from `range m`: `have hrange : range m = insert 0
(Ico 1 m)` by `ext; simp[mem_range,mem_insert,mem_Ico]; omega` (needs `0 < m` in context — split
`Nat.eq_zero_or_pos` first, `m = 0` closes by `simp[symmetricPairCount, Nat.not_prime_zero]`), then
`rw[symmetricPairCount, hrange, Finset.filter_insert]`, `simp only[Nat.sub_zero,Nat.add_zero,
and_self]`, `by_cases Nat.Prime m`, in the prime branch `Finset.card_insert_of_notMem (by simp)`
(0 ∉ Ico 1 m) + `omega`. NOTE: `Finset.card_insert_of_not_mem` is **deprecated → `_of_notMem`**.

**Honest status.** Structural decomposition, not a step toward the open conjecture; still on the
counting/upper-bound side (a nontrivial LOWER bound remains the real advance and is essentially
Goldbach). But it is the natural home for the recurring `+1` and cleanly names the distinct-prime
sub-count. `WeakGoldbach.lean`'s 4 axioms (Helfgott / circle method / Chen / binary-verified) remain
irreducible; the Schnirelmann axiom was already discharged (Part V).

**Verification (docker DOWN).** Docker infra fully down all session (containerd meta.db +
content-store blob `input/output error` at image build — operator-level, NOT disk: `df` shows 157Gi
free). Verified instead by direct `lean` elaboration against the main repo's pinned Mathlib v4.26.0
oleans (`~/.elan/toolchains/leanprover--lean4---v4.26.0/bin/lean` with `LEAN_PATH` = every
`.lake/packages/*/.lake/build/lib/lean`): **exit 0, zero diagnostics**. `#print axioms` on both new
theorems = `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`, no `Lean.ofReduceBool`).
