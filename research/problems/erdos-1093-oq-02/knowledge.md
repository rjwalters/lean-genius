# Erdős #1093 — OQ-02: Is d(284,28)=9 the maximal deficiency?

## Summary

**Parent:** Erdős #1093 (deficiency of binomial coefficients, Erdős–Lacampagne–Selfridge).
For `n ≥ 2k`, when `C(n,k)` has no prime factor `≤ k`, the *deficiency* is the number
of `0 ≤ i < k` with `n − i` being `k`-smooth. The current record is
`deficiency(C(284,28)) = 9`.

**OQ-02:** Is `9` the maximum possible deficiency over all admissible `(n,k)`,
or do higher values occur? (The universal upper-bound direction is open.)

## Status: OPEN (universal bound, now confined to k≥16); existence half machine-verified.

---

## Session 2026-07-08 (Session 3) — Correct OQ-02 frontier: k≥15 → k≥16

**Mode:** REVISIT (RICH knowledge tier, highest available)
**Outcome:** progress (limitative + strict sharpening)

### Key realization
Sections XII–XIII tracked the **deficiency-9** comparison `(k!)² < (k+9)!`
(reversing at `k=15`) and concluded "open frontier `k ≥ 15`". But OQ-02
(`MaximalDeficiencyIs 9`) rules out deficiency **`≥ 10`**, whose exclusion is
governed by `(k!)² < (k+10)!` — reversing one step **later**, at `k=16`. The
threshold `9` was one too small. Exact arithmetic:
- `25!/(15!)² ≈ 9.07 > 1` ⟹ deficiency `≥10` **excluded** at `k=15`
- `26!/(16!)² ≈ 0.92 < 1` ⟹ deficiency `10` **permitted** at `k=16`

So the elementary sharp bound `(k+deficiency)! ≤ (k!)²` (Section X) already
**resolves OQ-02 for all `k ≤ 15`**; the tight open frontier is **`k ≥ 16`**.

### What I Did — Section XV (VERIFIED, 0 sorry, 0 new axioms, ofReduceBool-free)
- `factorial_sq_lt_add_ten_of_k_le_15` — `(k!)² < (k+10)!` for `k ≤ 15` (kernel `decide`).
- `deficiency_le_nine_of_k_le_15` — admissible `k ≤ 15` ⟹ `deficiency ≤ 9`
  (a deficiency `≥10` forces `(k+10)! ≤ (k!)²`, impossible for `k ≤ 15`).
- `maximalDeficiencyIs_nine_iff_kGe16` — strict sharpening of `_kGe15`.
- `sharp_bound_permits_deficiency_ten` — `(k+10)! ≤ (k!)²` for `k ≥ 16` (limitative:
  induction from `26! ≤ (16!)²`, step factor `k+11 ≤ (k+1)²`).
- `oq02_frontier_exact` — the split at the frontier `k = 16`.

### Why the tail is genuinely blocked (new clarification)
The parent axiom `els_upper_bound` (`n ≪ 2^k·√k` for deficiency `≥1`) is a
**location** bound on `n`, provably insufficient to close the deficiency universal
bound: it constrains *where* admissible pairs sit, not *how many* `k`-smooth values
the length-`k` window holds. A conditional resolution needs a short-interval
**smooth-count** bound; any faithful such hypothesis is `#{k-smooth in (n−k,n]} ≤ 9`
`= deficiency n k ≤ 9`, i.e. circular. Hence the `k ≥ 16` tail is irreducibly
analytic (ψ(x,y)/Dickman-ρ density) — BLOCKED pending Mathlib smooth-number density
(>1000 lines, deep chains). This corrects the earlier "axiomatize ELS then prove a
conditional resolution" next-step, which cannot work.

### Verification
`./proofs/scripts/docker-build.sh Proofs.Erdos1093ProblemOQ02` → `Built (3060 jobs)`,
0 sorry, 0 `axiom` declarations. File now 816 lines, 35 theorems.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XV, +~110 lines, verified)
- `src/data/research/problems/erdos-1093-oq-02.json` (leanFiles counts + knowledge)

---

## Session 2026-07-08 (Session 2) — Density bound + sharpened reduction

**Mode:** REVISIT (MODERATE knowledge tier, highest available)
**Outcome:** progress

### What I Did
- Added the first **non-trivial upper bound** on the deficiency to the OQ-02
  file (Section V), all `ofReduceBool`-free (no `native_decide`):
  - `smooth_contributor_not_prime` — every smooth contributor `n−i` (`i<k`,
    `n≥2k`) is composite: it exceeds `k`, and a `k`-smooth number `>k` cannot be
    prime (`isKSmooth_prime_iff`).
  - `deficiency_le_nonprime_count` — weak form: `deficiency ≤ #{i<k : ¬(n−i).Prime}`
    (smooth filter ⊆ non-prime filter).
  - `deficiency_add_prime_count_le` — **sharp density bound**:
    `deficiency n k + #{i<k : (n−i).Prime} ≤ k`.
- Added `maximalDeficiencyIs_nine_iff_kGe10` (Section VI): the conjecture is
  equivalent to the open statement quantified only over `k ≥ 10` (small `k`
  discharged by the trivial bound). Strictly sharper than
  `maximalDeficiencyIs_nine_iff_upperBound`.
- Built clean: `Proofs.Erdos1093ProblemOQ02` (3059 jobs), 0 sorry, 0 new axioms.

### Key Findings
- **Primes in the window contribute nothing.** The `k` consecutive integers
  `n, …, n−k+1` all exceed `k` (admissible ⇒ `n ≥ 2k`), and a prime is
  `k`-smooth iff `≤ k`. So the trivial `deficiency ≤ k` upgrades to
  `deficiency ≤ k − (#primes in window)` — the first genuine upper bound here.
- **Reframes the open core.** A hypothetical deficiency `> 9` at `k ≥ 10` needs a
  length-`k` run of consecutive integers with `< k−9` primes: an exceptionally
  prime-poor window. This is exactly the density input the ELS bound
  (`els_upper_bound`, `n ≪ 2^k√k`) formalizes.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Sections V–VI, +~75 lines, verified)
- `src/data/research/problems/erdos-1093-oq-02.json` (knowledge)

### Next Steps
- Quantify: combine `deficiency + #primes ≤ k` with a prime-count lower bound on
  `[n−k+1, n]` (Brun–Titchmarsh) to force `k`-dependent upper bounds for `k ≥ 10`.
- Attempt `k = 10, 11, 12` slices via the composite-contributor structure plus
  the `p ∤ C(n,k)` admissibility constraint.

---

## Session 2026-07-08 (Session 1) — Record admissibility + reduction

**Mode:** FRESH
**Outcome:** progress

### What I Did
- Selected erdos-1093-oq-02 (concrete, computable record value; parent infrastructure exists).
- Discovered the parent `Erdos1093Problem.lean` was **broken on main** — `omega` at
  L173 (`isKSmooth_one`) lacked `p.Prime`'s `two_le`. Repaired with
  `hp.one_lt.ne'` on `Nat.dvd_one.mp hd`. Parent now builds (3058 jobs).
- Wrote companion `Erdos1093ProblemOQ02.lean` (0 sorry, 0 axiom declarations).

### Key Findings
- The parent's `deficiency_284_28 = 9` does **not** by itself exhibit a valid
  deficiency example: the `deficiency` count is defined unconditionally, but the
  ELS problem additionally requires `C(n,k)` to have no prime factor `≤ k`. That
  admissibility check was never done. It only needs primes `≤ k` (Kummer not
  required): `C(284,28)` is a ~110-bit bignum, so `native_decide` computes it and
  tests divisibility by primes `≤ 28` instantly ⇒ `noSmallPrimeFactors_284_28`.
- The maximality question splits: **existence half** = finite verification
  (attained at `(284,28)`); **universal half** = genuinely open (unbounded `n,k`,
  cannot enumerate). `maximalDeficiencyIs_nine_iff_upperBound` reduces the whole
  conjecture to exactly the universal bound.
- Trivial bound `deficiency ≤ k` ⇒ any counterexample needs `k ≥ 10`
  (`deficiency_le_nine_of_k_le_nine`).
- Explicit certificate: the 9 smooth indices are `{4,8,9,11,12,14,18,20,24}`,
  i.e. `280,276,275,273,272,270,266,264,260` are the 28-smooth values.

### Files Modified
- `proofs/Proofs/Erdos1093Problem.lean` (1-line repair)
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (new, verified)
- `src/data/research/problems/erdos-1093-oq-02.json` (new)

### Next Steps
- Attack the universal bound for small `k ≥ 10`: the ELS bound `n ≪ 2^k√k`
  gives a finite per-`k` range, but the parent axiom `els_upper_bound`'s constant
  is not effective — an explicit constant would make each fixed-`k` slice decidable.
- Exploit the density constraint: deficiency `d` forces `d` of the `k` consecutive
  integers `n,…,n−k+1` to be `k`-smooth.
- Consider a Kummer-based (`ofReduceBool`-free) proof of `noSmallPrimeFactors_284_28`.

## Session 2026-07-08 (Session 2, researcher-1) — Section VII: prime-window caps deficiency

**Mode:** DEEP DIVE (RICH problem, look-outward from mature state)
**Outcome:** progress (2 new ofReduceBool-free theorems)

### What I Did
Extended the sharp density bound `deficiency + #primes-in-window ≤ k`
(`deficiency_add_prime_count_le`) with its effective/extreme consequences:
- `deficiency_lt_k_of_prime_in_window`: a single prime `n-i` (`i<k`) in the
  window forces `deficiency n k < k` (one prime certificate suffices — effective).
- `window_primefree_of_deficiency_eq_k`: the trivial-max case `deficiency n k = k`
  forces a prime gap of length ≥ k (no window value is prime). Structural reason
  record deficiencies are hard: they demand prime-poor windows (the ELS density
  phenomenon).

Both proved by pulling `#primes ≥ 1` (`Finset.one_le_card.mpr ⟨i,_⟩`) into the
sharp bound and closing with `omega`. No native_decide, no new axioms.

### Verification
Built clean (3059 jobs). File now 19 theorems, 0 sorries, 0 axiom declarations.
native_decide (⇒ ofReduceBool) still used ONLY by the 3 record facts
(deficiency_284_28 [parent], noSmallPrimeFactors_284_28, smooth_indices_284_28);
all structural results (Sections I,III–VII) are ofReduceBool-free.

### Assessment / Frontier
The open core (universal upper bound `deficiency ≤ 9` for all admissible pairs,
k ≥ 10) is genuinely blocked on analytic NT: it needs an *effective* ELS/Brun–
Titchmarsh short-interval prime-count bound, absent from Mathlib v4.26. The parent
axiom `els_upper_bound` has a non-effective constant, so even fixed-k slices aren't
decidable. Elementary structural theory here is near its frontier.

### Next Steps (if revisited)
- ofReduceBool-free proof of `noSmallPrimeFactors_284_28` via Kummer/Legendre digit
  sums (Mathlib `Nat.Prime.factorization_choose`), per-prime for p∈{2,3,5,7,11,13,17,19,23};
  only partial (record count/smooth_indices still need native_decide).
- The universal bound needs effective analytic NT — BLOCKED until Mathlib has it.

## Session 2026-07-08 (researcher-6) — Section XII: explicit ceiling ≤18 at k=28

**Mode:** REVISIT (RICH; file saturated through Section XI)
**Outcome:** progress (1 new theorem)

### What I Did
The file's elementary theory was already very mature: Section X's sharp closed
form `(k + deficiency n k)! ≤ (k!)²` and Section XI's strict `deficiency n k < k`
(#35434, landed mid-session) exhaust the abstract structural bounds. The one
concrete consequence only *asserted in prose* was the numeric ceiling at the
record modulus. Formalized it:
- `deficiency_record_le_18`: every admissible `(n,28)` has `deficiency n 28 ≤ 18`.
  Specialises `deficiency_add_factorial_le_sq` (`(28+d)! ≤ (28!)²`) with the
  single bignum certificate `(28!)² < 47!` (`native_decide`); a deficiency `≥ 19`
  forces `47! ≤ (28+d)! ≤ (28!)² < 47!`, contradiction. Since `46! = (28+18)!`
  is `≤ (28!)²` but `47!` is not, `18` is the exact ceiling this bound gives.

### Key Finding
This pins the elementary-vs-record gap concretely: at `k=28` the sharpest
ELS-axiom-free theory in the file proves `deficiency ≤ 18`, while the actual
record is `deficiency 284 28 = 9`. Closing OQ-02 at this modulus still requires
ruling out `10 ≤ d ≤ 18` — exactly the effective short-interval prime-density
input the elementary product argument cannot supply.

### Verification
Built clean: `Proofs.Erdos1093ProblemOQ02` (3060 jobs), 0 sorry, 0 axiom
declarations. `native_decide` (⇒ `Lean.ofReduceBool`) now used by 4 numeric facts
(3 record facts + the `(28!)²<47!` certificate); all of Sections IV–XI remain
`ofReduceBool`-free. File: 595 lines, 26 theorems. (Build hit rotating shared-
volume corruption — `.ir` invalid-header then exit-135 — cleared after cache
force-refresh + retries; identical code had already built green pre-rebase.)

### Frontier / Next Steps
Elementary structural theory is saturated. The remaining content (the universal
bound, or closing `10 ≤ d ≤ 18` at `k=28`) is BLOCKED on effective analytic NT
(short-interval prime counts / an effective ELS constant), absent from Mathlib
v4.26 — `els_upper_bound`'s constant is non-effective, so even fixed-`k` slices
are not decidable.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XII, +~35 lines, verified)
- `src/data/research/problems/erdos-1093-oq-02.json` (metadata + knowledge)

## Session 2026-07-08 (researcher-2) — de-native_decide the (28!)²<47! certificate

**Mode:** AXIOM-REDUCTION (elementary theory saturated; look at trust surface).
**Outcome:** progress (1 native_decide → kernel `decide`).

### What I Did
Converted the numeric certificate `(Nat.factorial 28)^2 < Nat.factorial 47` inside
`deficiency_record_le_18` (Section XIV) from `native_decide` to kernel `decide`.
`Nat.factorial` is *structural* recursion, so the kernel reduces `47!`/`28!`
(47/28 GMP-accelerated mults) and the `<` literal comparison — no `Lean.ofReduceBool`.
This matches the pre-existing `interval_cases k <;> decide` pattern (Section on the
abstract `(k!)² < (k+9)!` bound). So `deficiency_record_le_18` is now
`ofReduceBool`-free.

### Why the other two certs can't follow (documented in the file's ## Axioms block)
- `noSmallPrimeFactors_284_28`: reduces (via `noSmallPrimeFactors_iff`) to testing
  `p ∤ C(284,28)` for primes p≤28. Kernel `decide` would have to compute the bignum
  binomial `C(284,28)` by Pascal recursion — infeasible. A genuine `ofReduceBool`-free
  route is Kummer/Legendre (v_p(C(n,k))=0 ⟺ no base-p carries adding 28 and 256), a
  per-prime finite carry check; not attempted here (≈100+ lines, 9 primes).
- `smooth_indices_284_28`: `IsKSmooth` decidability goes through `Nat.primeFactors`,
  which is **well-founded** recursion → does NOT reduce under kernel `decide` (only
  `native_decide`). This is why `decide` cannot replace it even though the values are
  ≤ 284.

### Verification
Built clean: `Proofs.Erdos1093ProblemOQ02` (3060 jobs, exit 0). File 714 lines,
30 theorems, 0 sorry, 0 axiom declarations. Remaining native_decide: exactly the
two binomial/factorization record certs above (+ parent's `deficiency_284_28`).

### Frontier
Unchanged: the universal upper bound (and closing 10≤d≤18 at k=28) is BLOCKED on
effective analytic NT absent from Mathlib. The Kummer de-native_decide of
`noSmallPrimeFactors_284_28` is the one remaining *bounded* trust-surface win.

## Session 2026-07-08 (researcher-3) — de-native_decide `noSmallPrimeFactors_284_28` via Kummer

**Mode:** AXIOM/TRUST-REDUCTION (elementary theory saturated; the "one remaining
bounded trust-surface win" flagged by researcher-2's session was the Kummer route).
**Outcome:** progress (1 native_decide → kernel `decide`). VERIFIED, 0 sorry / 0 axiom.

### What I did
Rewrote `noSmallPrimeFactors_284_28`. Old proof: `rw [noSmallPrimeFactors_iff]; native_decide`
(computes the ~50-digit bignum `C(284,28)` and tests divisibility → `Lean.ofReduceBool`).
New proof invokes **Kummer's theorem** `Nat.factorization_choose` (Mathlib
`Mathlib/Data/Nat/Choose/Factorization.lean`): `(C n k).factorization p =
#{i ∈ Ico 1 b | p^i ≤ k % p^i + (n-k) % p^i}` (carry count), for any `b > log p n`.
For each prime `p ≤ 28`, `p ∣ C(284,28)` ⇒ `0 < factorization p` (`Prime.factorization_pos_of_dvd`)
⇒ a positive carry count over `Ico 1 9`; adding `28`+`256` has no carry in any base
`p ≤ 28`, so the count is 0 — contradiction. `interval_cases p` (2..28), primes closed by
`decide` on the concrete carry set, composites by `norm_num` on `¬ p.Prime`.

### Key gotchas (reusable)
- **`log` doesn't reduce under kernel `decide`** (well-founded rec). Bound `log p 284 < 9`
  via `Nat.log_lt_of_lt_pow (h : 284 < p^9)`, and `284 < p^9` generically from
  `284 < 2^9 ≤ p^9` (`Nat.pow_le_pow_left hpp.two_le`). No `log` ever hits `decide`.
- **`decide` DOES reduce the `Finset.Ico 1 9` filter-card** (confirmed by isolated probes —
  `decide`, `rfl`, `simp+decide` all work standalone even for `p=23`, `23^8`). The bignum
  `C(284,28)` is what `decide` can't do (exponential Pascal recursion), NOT the carry set.
- **Branch-order trap in `interval_cases p <;> first | A | B`:** put the `decide` branch
  FIRST. If `norm_num` (proving `¬ p.Prime`) is tried against a genuine *prime*, it reduces
  the side goal to `⊢ False` and STALLS with "unsolved goals" — a hard error, not a clean
  failure `first` can recover from. With `decide` first, primes are closed before `norm_num`
  is reached, so `norm_num` only ever sees composites (where `¬ p.Prime` holds cleanly).

### Build notes
Documented exit-135/139 SIGBUS at `[3060/3060]` (elaborates fully in ~1-2s, 0 proof errors,
then crashes on olean finalization under fleet memory contention) reproduced ~11× in a row;
`LEAN_SKIP_CACHE=true` did NOT help (crash is post-decompress). Fix: `docker-build.sh
--repair-cache` (force cache refresh; decompress dropped to 15s, a sign the fleet quieted),
then the very next build went green `✔ [3060/3060] Built (2.4s)` exit 0. Real proof errors,
by contrast, print explicit `.lean:LINE:COL: error` diagnostics (the branch-order bug printed
9 of them) — their ABSENCE + reaching `[3060/3060]` is the tell for an environmental crash.

### Frontier
Unchanged: the universal upper bound (and closing `10 ≤ d ≤ 18` at `k=28`) is BLOCKED on
effective analytic NT absent from Mathlib. Remaining native_decide in this file: exactly one
— `smooth_indices_284_28` — which CANNOT be de-native_decided (`IsKSmooth` decidability routes
through `Nat.primeFactors`, well-founded recursion, does not reduce under kernel `decide`). The
parent's `deficiency_284_28` also remains native_decide. So the file is still `ofReduceBool`-
dependent overall, but this session removed one of the two record-cert dependencies here.

## Session 2026-07-08 (researcher-3, 2nd visit) — TERMINUS confirmed; no session-sized win remains

**Mode:** ASSESS. **Outcome:** no Lean shipped (correctly). Reasons, verified this visit:

1. **No gallery entry exists for this slug.** `src/data/proofs/` contains only
   `erdos-1093/` (path `Proofs/Erdos1093Problem.lean`) — there is **no**
   `src/data/proofs/erdos-1093-oq-02/`, and no meta references
   `Erdos1093ProblemOQ02.lean`. So `Erdos1093ProblemOQ02.lean` is a **research-only
   file with no gallery integration**: any trust-surface change to it is invisible
   to the gallery and cannot flip any entry to `verified`.
2. **The parent is irreducibly axiomatized.** `erdos-1093` is `axiomatized`
   (axiomCount 2), resting on `axiom els_upper_bound` (Erdős–Lacampagne–Selfridge,
   a deep analytic-NT result not in Mathlib). No native_decide removal changes that.
3. **Correction to the prior note's "CANNOT."** `smooth_indices_284_28` (and hence
   the parent's `deficiency_284_28 = card ∘ filter`) *can* in fact be
   de-native_decided — not by the `decide` **tactic** (which the prior note ruled
   out, correctly, since `IsKSmooth`'s `Decidable` instance routes through
   `Nat.primeFactors` / well-founded rec), but by a **manual factorization proof**:
   `ext i; interval_cases i`, then for each smooth value `m = 284−i` prove
   `IsKSmooth 28 m` by peeling its factorisation with `Nat.Prime.dvd_mul` +
   `Nat.prime_dvd_prime_iff_eq` (each prime divisor forced into `{2,3,5,7,…,23}`,
   all ≤ 28), and for each non-smooth `m` exhibit a prime factor > 28
   (`fun h => absurd (h P _ _) (by norm_num)`). Factorisations (all verified):
   smooth idx→val 4→280=2³·5·7, 8→276=2²·3·23, 9→275=5²·11, 11→273=3·7·13,
   12→272=2⁴·17, 14→270=2·3³·5, 18→266=2·7·19, 20→264=2³·3·11, 24→260=2²·5·13;
   the 19 non-smooth carry a prime >28 (e.g. 261=9·**29**, 284=4·**71**, 283 prime).
   `Nat.div`/`Nat.mod` on literals *do* reduce in the kernel (GMP-backed), so
   `card {…} = 9` closes by `decide`/`rfl` once the filter is rewritten.

**Why it was NOT done:** it is ~100 lines of laborious, first-try-fragile Lean
requiring a heavy Docker build (HermiteLindemann-class import weight, documented
SIGBUS-135 risk), and per (1)+(2) it yields **zero gallery-visible improvement** and
cannot reach `verified` (no entry; parent axiom-blocked). Pure trust-surface polish
of an ungalleried file is not worth the compute. **This slug is a terminus for
session-sized work** — the genuine frontier (universal bound / `10≤d≤18` at k=28) is
blocked on effective analytic NT absent from Mathlib. Future agents: do not reclaim
for elementary or de-native_decide work; the only real advance is formalising ELS,
a multi-month effort. Recipe above is recorded so no one re-derives it.
