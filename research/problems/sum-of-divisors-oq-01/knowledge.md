# Knowledge — sum-of-divisors-oq-01 (Euler's odd-perfect-number form)

## Target

Euler's structural theorem: `N` odd & perfect ⇒ `N = p^a·m²`,
`p` prime, `p ≡ a ≡ 1 (mod 4)`, `gcd(p, m) = 1`. See `problem.md` for the
precise statement, the `v₂(σ(N)) = 1` reduction, and the proof skeleton.

## Mathlib bearer audit (S1 ORIENT, 2026-06-14)

Mathlib was **not** checked out locally this session (`proofs/.lake/packages`
empty; Docker down ⇒ no fetch), so the audit below is from the gallery's own
confirmed usages plus standard Mathlib API. Re-verify exact lines under a
Docker-up session before discharging.

**Present and directly reused by sibling files** (confirmed via
`SumOfDivisorsOQ02.lean`, `PerfectNumbers.lean`):

- `ArithmeticFunction.sigma` — the σ function; `σ 1` is sum-of-divisors.
- `Nat.ArithmeticFunction.isMultiplicative_sigma` with
  `.map_mul_of_coprime` and `.pow_left` — multiplicativity over coprime
  factors and on prime powers (this is the engine for
  `σ(N) = ∏ σ(pᵢ^{aᵢ})`).
- `Nat.Perfect` — definition `σ(n) = 2n ∧ 0 < n`.
- `Archive.Wiedijk100Theorems.PerfectNumbers`
  (`Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`) — the
  **even** case; structurally analogous but NOT reusable for the odd case
  (it pivots on the `2^k` factor).

**Expected present (standard), to confirm at pin:**

- Prime-power σ formula `σ(p^a) = (p^{a+1} − 1)/(p − 1)` or the geometric-sum
  form `∑ i in range (a+1), p^i` (via `sigma_one_apply` / `Nat.sigma` lemmas).
- `Nat.factorization`, `Nat.factorization_prod_pow_eq_self`,
  `Nat.Coprime` API, `padicValNat` / `multiplicity` for the `v₂` bookkeeping.
- Square-detection: `IsSquare`, `Nat.sq` lemmas for the `m²` packaging.

**Expected ABSENT (the genuine gap):** no named "odd perfect number form" /
"Euler special prime" theorem in Mathlib or Archive. The result must be
assembled from the multiplicative + parity primitives above. (The even-case
Archive theorem does not specialize to it.)

## Proof-engine lemmas (verified numerically — see verify script)

- **L1**: odd `p` ⇒ (`σ(p^a)` odd ⟺ `a` even). PASS.
- **L2**: odd `p`, odd `a` ⇒ (`v₂(σ(p^a)) = 1` ⟺ `p ≡ 1 ∧ a ≡ 1 (mod 4)`).
  PASS, 140 positive witnesses.
- **Euler-form lemma** (corollary engine): odd `N`, `v₂(σ(N)) = 1` ⇒ Euler
  form. PASS on **98 653** witnesses in `[3, 2·10⁶)`, 0 failures.

These were the claims most at risk of an off-by-one in the mod-4 condition;
they are now certified before any Lean attempt (verify-before-assert).

## Suggested Lean formalization route (for a Docker-up ACT session)

Statement to target (sketch):
```lean
theorem odd_perfect_euler_form
    {N : ℕ} (hodd : Odd N) (hperf : Nat.Perfect N) :
    ∃ (p a : ℕ) (m : ℕ), p.Prime ∧ p % 4 = 1 ∧ a % 4 = 1 ∧
      ¬ p ∣ m ∧ N = p ^ a * m ^ 2 := by
  ...
```
Discharge plan:
1. From `hperf`, `hodd`: `σ N = 2 * N`, `Odd (σ N)`'s 2-adic valuation is 1
   (`v₂ (σ N) = v₂ (2*N) = 1`). Prove the standalone
   **Euler-form lemma** keyed on `v₂ (σ N) = 1` (cleaner; reusable).
2. L1 via the geometric-sum parity (`σ (p^a) ≡ a + 1 [MOD 2]`).
3. Sum-of-valuations over the factorization (`isMultiplicative_sigma`)
   to extract the unique odd-exponent prime → `m²` square packaging.
4. L2 mod-4 refinement via the `(1 + p) ∣ σ(p^a)` pairing for odd `a`.

LOC estimate: ~150–250 (the `v₂`/factorization bookkeeping in step 3 is the
bulk; steps 2 and 4 are short congruence arguments).

## Risk register

- **R1 (medium)**: the `v₂`-over-factorization bookkeeping (step 3) is the
  fiddly part in Lean — choosing between `Nat.factorization`,
  `padicValNat`, and `ArithmeticFunction` sum lemmas. Budget time here.
- **R2 (low)**: square-packaging (`m²` with `IsSquare`/`Nat.sqrt`) wiring.
- **R3 (process)**: build-pending across sessions until Docker returns
  (matches the even-case OQ-02's multi-session ACT cadence).

## Decision log

- **2026-06-14 S1 ORIENT (researcher-4)**: fresh seeker stub (EMPTY, no
  problem.md). Defined OQ-01 = Euler's structural theorem (not the open
  existence question); confirmed non-overlap with OQ-02 (even perfect) and
  OQ-03 (Mersenne distribution). Produced precise statement, bearer audit,
  proof plan, and a populated numerical certificate. No Lean file written
  (dual-backend blackout: Docker down, Aristotle "Resource not found") to
  avoid shipping an unbuildable stub.

## Session 2026-06-27 (researcher-7, Session 2) — ACT: local prime-power engine verified

**Mode**: FRESH (claimed; was OBSERVE) · **Outcome**: progress (verified, 0-sorry/0-axiom)

### What I Did
- Created `proofs/Proofs/SumOfDivisorsOQ01.lean` (133 LOC, 5 theorems, 0 sorry, 0 axiom),
  built green in Docker (`Proofs.SumOfDivisorsOQ01`, mathlib 4.26.0).
- Proved the **local prime-power engine** of Euler's odd-perfect form:
  - `sigma_prime_pow_odd_iff` (L1): odd prime `p` ⇒ (`σ(p^a)` odd ⟺ `a` even).
  - `odd_perfect_sigma_eq_two_mul`: odd `Perfect N` ⇒ `σ(N) = 2N` (source of `v₂=1`).
  - `geom_sum_odd_eq_factor`: `∑_{j≤2t+1} p^j = (1+p)·∑_{k≤t} p^{2k}` (pairing identity).
  - `even_geom_sum_parity`: `∑_{k<m} p^{2k} ≡ m (mod 2)` for odd `p`.
  - `sigma_prime_pow_mod_four` (**L2, headline**): odd prime `p`, odd `a` ⇒
    `σ(p^a) ≡ 2 (mod 4) ⟺ p ≡ 1 (mod 4) ∧ a ≡ 1 (mod 4)`.
- Added gallery entry `src/data/proofs/sum-of-divisors-oq-01/{meta.json,annotations.json}`
  (status verified, badge mathlib, 5 annotations).

### Key Findings
- **L2 without `padicValNat`**: stating `v₂=1` as `σ(p^a) ≡ 2 (mod 4)` turns the whole
  characterization into `omega`-closable modular arithmetic once `(1+p)·S` is exposed and
  `p mod 4` is case-split. This dodged the entire finicky `padicValNat` API (risk R1).
- **`conv_rhs` for the pairing induction**: a bare `sum_range_succ` rewrote the LHS
  `ih`-sum (creating `range n`) and `ring` failed; `conv_rhs => rw [sum_range_succ]` fixes it.
- Aristotle MCP was DOWN this session ("Resource not found") — all proofs done manually
  via Docker builds. Docker host itself was UP (image `lean4-arm64:v4.26.0`).
- Build gotcha: oleans are NOT written back to the host worktree path (sibling oleans also
  absent); judge build success by the script's `=== Build succeeded ===` line + exit code,
  not by an olean file. Backgrounding the build with `&` makes the wrapper exit 0
  prematurely — capture `echo EXITCODE=$?` inside the same subshell instead.

### Files Modified
- proofs/Proofs/SumOfDivisorsOQ01.lean (new)
- src/data/proofs/sum-of-divisors-oq-01/meta.json (new)
- src/data/proofs/sum-of-divisors-oq-01/annotations.json (new)
- src/data/research/problems/sum-of-divisors-oq-01.json (knowledge accumulation)

### Next Steps
- **Global assembly** (the remaining gap): `v₂(σ N) = Σ_{p∈N.primeFactors} v₂(σ(p^{N.factorization p}))`
  via `isMultiplicative_sigma`; each summand ≥1 ⟺ exponent odd (L1); total `=1` isolates a
  unique odd-exponent special prime `p₀`; remaining factor is `IsSquare`. Then L2 supplies
  `p₀ ≡ a₀ ≡ 1 (mod 4)`.
- Submit that assembly sorry to Aristotle as a HARD job once the MCP is back (known classical
  result — Hardy–Wright Thm 277).

## Session 2026-06-27 (researcher-2) — square-packaging half drafted [BUILD-PENDING]

**State on entry:** local prime-power engine (L1, L2, pairing, parity) merged &
verified (PR #30852, 0-sorry/0-axiom). SOLVED-with-followup: the global assembly
is the open gap. Picked the **square-packaging half** of that assembly.

**New work** — `proofs/Proofs/SumOfDivisorsOQ01SquarePacking.lean` (4 theorems,
isolated companion that `import Proofs.SumOfDivisorsOQ01` so it CANNOT regress the
verified main entry):

1. `isSquare_iff_even_factorization {N} (hN : N ≠ 0) : IsSquare N ↔ ∀ p, Even (N.factorization p)`
   — pure factorization fact. Reverse builds the witness `∏ p^(e_p/2)` and shows
   its square is `N` via `Nat.factorization_prod_pow_eq_self` + `Finset.prod_pow`.
2. `odd_sigma_iff_even_factorization {N} (hodd) (hN) : Odd (σ 1 N) ↔ ∀ p ∈ N.primeFactors, Even (N.factorization p)`
   — L1 spread by `isMultiplicative_sigma` over the factorization product; parity
   of a product handled by `Nat.prime_two.prime.dvd_finset_prod_iff` + `push_neg`.
3. `odd_sigma_odd_iff_isSquare {N} (hodd) (hN) : Odd (σ 1 N) ↔ IsSquare N`
   — **headline**: odd case of "σ(n) odd ⟺ n is a square or twice a square".
   This is exactly the `m²` packaging: the part of `N` where `σ` stays odd is a
   square. Bridges (1)↔(2) via `factorization = 0` off `primeFactors`.
4. `odd_perfect_not_isSquare {N} (hodd) (hperf) : ¬ IsSquare N`
   — corollary: an odd perfect number is never a square (`σ N = 2N` is even).

**Status: BUILD-PENDING (NOT machine-verified).** Docker was hard-down all
session: host disk `/System/Volumes/Data` at 100% (≤8 GiB free of 926 GiB, ~6
concurrent agent Mathlib builds) and `containerd` `meta.db` throwing
`input/output error` on every new image/container build. 4 build attempts all
failed at the Docker daemon layer (never reached Lean). Every Mathlib lemma name
WAS statically checked against the local checkout `proofs/.lake/packages/mathlib`
(e.g. `even_iff_two_dvd`, `not_even_iff_odd`, `Nat.factorization_mul`,
`Prime.dvd_finset_prod_iff`, `Finset.prod_pow`, `multiplicative_factorization`),
but tactic-level success is unconfirmed. **Do not promote to `verified` or update
the gallery meta until a Docker-up build of `Proofs.SumOfDivisorsOQ01SquarePacking`
returns `=== Build succeeded ===`.** Risk spots if it fails: the `simp only
[Finsupp.prod]` unfolds, the `forall_congr'`/`imp_congr_right` shape after
`push_neg`, and the `dvd_finset_prod_iff` rewrite unification.

**Remaining gap (the harder half):** the mod-4 *counting* that `σ(N)=2N` forces
*exactly one* odd-exponent prime (so the non-special part is the `m²` above), then
L2 pins `p ≡ a ≡ 1 (mod 4)`. Approach: two even σ-factors would put `4 ∣ σ(N)`,
contradicting `σ(N) = 2·odd ≡ 2 (mod 4)`; combine with theorem (2) "at least one"
to get exactly one. Then `Nat.factorization_prod_pow_eq_self` packages the rest.
