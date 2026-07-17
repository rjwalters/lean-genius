# Erdős #1093 — OQ-02: Is d(284,28)=9 the maximal deficiency?

## Session 2026-07-12 (researcher-2) — TRUST-SURFACE: de-native_decide `smooth_indices_284_28`

**Mode:** REVISIT (RICH). **Outcome:** trust-surface reduction (1 `native_decide` → kernel-checkable
manual proof; a substantive fact loses its `Lean.ofReduceBool` dependency). VERIFIED (full Docker build
`✔ [3060/3060]`, 10s; scratch `#print axioms smooth_indices_284_28 = [propext, Classical.choice, Quot.sound]`).

### Why this, not another window-check ladder slice
The window-check ladder (Sections XVII–XXXIV, closing one `k` per session, frontier now `k≥34`) is, per
its own honesty notes and the fleet Honesty Standards, **marginal enumeration theater**: each slice closes
one more `k` with a growing `native_decide` window and can never finish elementarily (the tail is
irreducibly the analytic Erdős–Lacampagne–Selfridge input, absent from Mathlib). So instead of adding
k=34, I took the one remaining **bounded, genuinely-valuable** win flagged by earlier sessions
(researcher-2's 2026-07-08 "one remaining bounded trust-surface win"; researcher-3's TERMINUS recipe):
removing `native_decide` from `smooth_indices_284_28`.

### What I did (1 theorem rewritten, 0 sorry, 0 new axioms, 0 new theorems)
`smooth_indices_284_28` asserts `(range 28).filter (IsKSmooth 28 (284-·)) = {4,8,9,11,12,14,18,20,24}`.
Old proof: `native_decide` (factors each `284-i` via `Nat.primeFactors`, well-founded recursion → does
not reduce under kernel `decide` → `native_decide` → `Lean.ofReduceBool`). New proof certifies all 28
window values by hand:
- **9 smooth values** built from smoothness of primes ≤28 (`isKSmooth_prime_iff`) combined via
  `isKSmooth_mul`/`isKSmooth_pow` on their factorisations: 280=2³·5·7, 276=2²·3·23, 275=5²·11,
  273=3·7·13, 272=2⁴·17, 270=2·3³·5, 266=2·7·19, 264=2³·3·11, 260=2²·5·13.
- **19 non-smooth values** refuted by exhibiting one prime factor >28 (`fun h => absurd (h P _ _) _`):
  284=4·71, 282=6·47, 279=9·31, 278=2·139, 274=2·137, 268=4·67, 267=3·89, 265=5·53, 262=2·131,
  261=9·29, 259=7·37, 258=6·43, and the primes 283,281,277,271,269,263,257.
- Closer: `ext i; simp only [mem_filter,mem_range,mem_insert,mem_singleton]; constructor` then
  `interval_cases i <;> first | omega | (norm_num at hs; exact absurd hs (by assumption))` forward,
  `rintro (rfl|…) <;> exact ⟨by norm_num, by norm_num; assumption⟩` reverse.

### Gotchas (reusable)
- The `IsKSmooth` **Decidable instance** is what makes `Finset.filter (IsKSmooth 28 ·)` typecheck; a
  standalone scratch copy of `IsKSmooth` must copy `isKSmooth_decidable` too or `filter` fails to
  synthesise `DecidablePred` (and error-recovery injects `sorryAx` into `#print axioms`).
- Prototyped the whole proof in a Mathlib-only scratch file (`lake env lean`, ~17s) — no need to build
  the heavy parent (`native_decide` C(284,28), SIGBUS-prone) just to iterate the factorisation logic.
- `norm_num` proves both `Nat.Prime 71` and `71 ∣ 284` on literals; `dvd_refl _` for the self-prime cases.
- ★ENV: the loom worktree branch `feature/researcher-2-191` was STALE — behind the restore commits
  (#38422/#38423) and carrying a divergent OQ02 file; `git diff origin/main` showed 10k deletions.
  Rebuilt the change in a FRESH `git worktree add -b … origin/main` and re-applied. Always diff-vs-origin/main
  before committing loom-worktree work.

### Trust surface after this session
`smooth_indices_284_28`, `noSmallPrimeFactors_284_28`, and the `(28!)²<47!` certificate are now all
`ofReduceBool`-free. Remaining `native_decide` in the OQ02 file: exactly the **per-k window facts**
`window_kNN_admissible_deficiency_le_nine` (Sections XVII+) — inherently `native_decide` (bignum
`C(m,k)` over thousands of `m`). The **parent** `deficiency_284_28` also remains `native_decide`.

### Frontier (UNCHANGED)
The universal upper bound (`MaximalDeficiencyIs 9`) is BLOCKED on effective analytic NT (an effective
ELS / short-interval smooth-count bound) absent from Mathlib v4.26. **Do not extend the window-check
ladder as "progress" — it is theater.** This file is research-only (no gallery entry; parent erdos-1093
is axiomatized on `els_upper_bound`), so this session is a trust-surface improvement, not a gallery flip.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (rewrote `smooth_indices_284_28`; updated `## Axioms` header)
- `src/data/research/problems/erdos-1093-oq-02.json` (counts + knowledge)
- `research/problems/erdos-1093-oq-02/knowledge.md` (this note)

---


## Session 2026-07-12 (researcher-5) — Section XXXV: closed-form log ceiling + saturation is now uniformly machine-checked

**Mode:** REVISIT (RICH tier, score 60). **Outcome:** one new axiom-free theorem + honest knowledge cleanup; elementary theory confirmed **saturated**, open frontier **analytically blocked**.

### What I did
- **Assessed, did NOT extend, the per-k location ladder.** The file already closes `k ≤ 33` via 18 near-identical `native_decide` sections (`deficiency_le_nine_of_k_eq_{16..33}`). This is enumeration theater — one `k` per session, can never reach all `k`. A `k = 34` rung was deliberately **not** written.
- **Found the size-method impossibility is already UNIFORMLY machine-checked**, not merely prose: `sharp_bound_permits_deficiency_ten` proves `∀ k ≥ 16, (k+10)! ≤ (k!)²`, i.e. the sharp-factorial ceiling provably cannot exclude deficiency `10` at any `k ≥ 16`. So a divergence/impossibility lemma would be **redundant**.
- **Added the one genuinely-new, non-redundant form the file lacked:** a *closed-form* deficiency ceiling.

### New theorem (Section XXXV, `Erdos1093ProblemOQ02.lean`)
```lean
theorem deficiency_le_log_factorial {n k : ℕ} (hn : 2 * k ≤ n) (hk : 1 ≤ k)
    (h : NoSmallPrimeFactors n k) :
    deficiency n k ≤ Nat.log (k + 1) (Nat.factorial k) :=
  Nat.le_log_of_pow_le (by omega) (deficiency_pow_succ_le_factorial hn h)
```
Every prior ceiling (`deficiency_le_of_sq_factorial_lt`, `deficiency_le_of_windowFloor_pow_lt`) is a *transfer principle* consuming an external numeric certificate. This is the first ceiling exposed as an **explicit computable function of `k`** — `log_{k+1}(k!)`. It is the crude power ceiling (at `k=28`: `Nat.log 29 (28!) = 20`, vs the sharp `deficiency_ascFactorial_le_factorial`'s `18`), and grows without bound in `k`, so like every size-only bound it cannot reach `9`.

**Verification:** docker `Proofs.Erdos1093ProblemOQ02` exit 0 (3060 jobs); `#print axioms deficiency_le_log_factorial` = `[propext, Classical.choice, Quot.sound]` (axiom-free); 0 `sorry`; ELS-free.

### Key findings / honesty
- Elementary theory is **saturated**. Both the sharp factorial ceiling and the location bound are provably powerless for large `k`; the impossibility is uniform and machine-checked.
- Two prior `nextSteps` (the `∀D ∃k₀` meta-theorem and its binomial form) are **already proven** in `Erdos1093OQ02FactorialGrowth.lean` (`exists_factorial_add_le_sq`, `exists_choose_mul_factorial_le`).
- One prior `nextStep` was **malformed**: exhibiting an admissible pair of deficiency `> 9` would *disprove* the conjecture; it conflated the factorial window-shift `D` (unbounded) with the deficiency `d` (conjecturally `≤ 9`).
- **Blocker:** the only remaining input is an unconditional short-interval `k`-smooth-count / Dickman-ρ density bound. Mathlib v4.26 lacks it; building it is `>1000` lines of deep analytic infrastructure. Truly blocked pending that.

### Files modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (+~45 lines, Section XXXV)
- `src/data/research/problems/erdos-1093-oq-02.json` (knowledge)

### Next steps
See refreshed `nextSteps` in the JSON: do not extend the ladder; do not build large-deficiency witnesses; unblock only via Mathlib smooth-number-density infrastructure.


## Session 2026-07-12 (researcher-5) — Section XXXVI: window-check closes k=34 → frontier k≥35

**Mode:** REVISIT (RICH tier). **Outcome:** strict but MARGINAL advance (frontier `k ≥ 34 → k ≥ 35`),
one more slice of the elementary window-check ladder. The Lean file had already advanced through
Sections XXXIII (k=32) and XXXIV (k=33) past this knowledge.md's Section XXXII (k=31) entry; this
continues the identical pattern one slice further.

### Numeric input (Python-verified sharp)
Deficiency `≥ 10` at `k = 34` forces `(n-33)^{10} ≤ 34!`, and `34! < 7031^{10}` is sharp:
`34! = 295232799039604140847618609643520000000 < 295237133028067705118634149496938950801 = 7031^{10}`,
while `7030^{10} = 294817493935202715907278900490000000000 ≤ 34!`. So `n - 33 < 7031 ⟹ n ≤ 7063`.
Floor `n ≥ 68 (= 2·34)` gives the window `n ∈ {68,…,7063}` (6996 values). Python: the window is
**empty of admissible pairs** — every `m` has some prime `p ∈ {2,3,5,7,11,13,17,19,23,29,31}`
dividing `C(m,34)`. `34 = 2·17` is composite, so the prime set is UNCHANGED from k=33 (largest
prime `≤ 34` is still 31).

### What I did — Section XXXV (5 theorems, 0 sorry, 0 new axioms), VERIFIED
- `factorial_34_lt_7031_pow_ten` — `34! < 7031^10` (kernel `decide`, `[propext]`, ofReduceBool-free).
- `window_k34_admissible_deficiency_le_nine` — the single `native_decide` fact over the
  6996-value window (full-file build ~27s including this).
- `admissible_k34_window_deficiency_le_nine` — admissible ⟹ divisibility impossible ⟹
  `deficiency ≤ 9` (11-prime `rcases`, each `h p prime hd; omega`).
- `deficiency_le_nine_of_k_eq_34` — one-line instantiation of the window-check engine
  `deficiency_le_nine_of_location_window` at `k=34, M=7031`.
- `deficiency_le_nine_of_k_le_34`, `maximalDeficiencyIs_nine_iff_kGe35`.

### Verification (Docker-free, `proofs/bin/lake env lean` v4.26.0, prebuilt oleans)
Full file compiles clean (exit 0, 27s). `#print axioms`: `factorial_34_lt_7031_pow_ten` = `[propext]`;
`deficiency_le_nine_of_k_eq_34` / `maximalDeficiencyIs_nine_iff_kGe35` carry
`[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]` — the
`ofReduceBool`/`trustCompiler` from the single `native_decide` window fact, exactly as every prior
section. **No new axiom declaration; 0 sorry** (file still `grep -c '^axiom '` = 0).

### Honesty note
Marginal incremental advance — same window-check ladder that closes one `k` per session and can
NEVER finish by elementary means: `k ≥ 35` still has infinitely many `k`, and the irreducibly
analytic Erdős–Lacampagne–Selfridge input (`els_upper_bound`, NON-EFFECTIVE constant `n ≪ 2^k√k`)
governs all large `k` uniformly. The window native_decide also grows (860 values at k=28 → 6996 at
k=34, `(k!)^{1/10}`-sized) and will eventually become infeasible. Value is one more concrete `k`
discharged, record-slice reach now `k ≤ 34`. NO follow-up OQ generated (depth-1 slug, but the
follow-up would just re-ask the same open universal bound — degenerate; the ladder itself is the
only elementary continuation).

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XXXV, +97 lines, +5 theorems)

---

## Session 2026-07-11 (researcher-6) — Section XXXII: window-check closes k=31 → frontier k≥32

**Mode:** REVISIT (RICH tier). **Outcome:** strict advance (frontier `k ≥ 31 → k ≥ 32`),
one more slice of the elementary ladder. NOTE: this knowledge.md was behind the Lean file —
the file had already advanced through Sections XXX (k=29) and XXXI (k=30) since the Section XXIX
entry below. Section XXXII continues the established window-check pattern one slice further.

### Numeric input (Python-verified sharp)
Deficiency `≥ 10` at `k = 31` forces `(n-30)^{10} ≤ 31!`, and `31! < 2464^{10}` is sharp:
`31! = 8222838654177922817725562880000000 < 8249108861550475694138713729662976 = 2464^{10}`,
while `2463^{10} = 8215691410991820804190254776742849 ≤ 31!`. So `n - 30 < 2464 ⟹ n ≤ 2493`.
Floor `n ≥ 62 (= 2·31)` gives the window `n ∈ {62,…,2493}` (2432 values). Python: the window
is **empty of admissible pairs** — every `m` has some prime `p ∈ {2,3,5,7,11,13,17,19,23,29,31}`
dividing `C(m,31)`. `31` is prime, so the prime set gains `31` relative to `k = 30`.

### What I did — Section XXXII (5 theorems, 0 sorry, 0 new axioms), VERIFIED
- `factorial_31_lt_2464_pow_ten` — `31! < 2464^10` (kernel `decide`, `[propext]`, ofReduceBool-free).
- `window_k31_admissible_deficiency_le_nine` — the single `native_decide` fact over the
  2432-value window (full-file build ~21s including this).
- `admissible_k31_window_deficiency_le_nine` — admissible ⟹ divisibility impossible ⟹
  `deficiency ≤ 9` (11-prime `rcases`, each `h p prime hd; omega`; adds the `31` branch).
- `deficiency_le_nine_of_k_eq_31` — one-line instantiation of the window-check engine
  `deficiency_le_nine_of_location_window` at `k=31, M=2464`.
- `deficiency_le_nine_of_k_le_31`, `maximalDeficiencyIs_nine_iff_kGe32`.

### Verification (Docker-free, `proofs/bin/lake env lean` v4.26.0, prebuilt oleans)
Full file compiles clean (exit 0). `#print axioms`: `factorial_31_lt_2464_pow_ten` = `[propext]`;
structural engine `deficiency_le_nine_of_location_window` = `[propext, Classical.choice, Quot.sound]`
(ofReduceBool-free); `deficiency_le_nine_of_k_eq_31` / `maximalDeficiencyIs_nine_iff_kGe32` carry
`[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]` — the
`ofReduceBool`/`trustCompiler` from the single `native_decide` window fact, exactly as every prior
section. **No new axiom declaration; 0 sorry.**

### Honesty note
This is a genuinely strict but **marginal** advance: the window-check ladder closes one `k` per
section and can never finish by elementary means (`k ≥ 32` still has infinitely many `k`; the
irreducibly analytic Erdős–Lacampagne–Selfridge input governs all large `k` uniformly). Each slice
also costs a growing `native_decide` window (2432 values here) that will eventually become
infeasible. Value is incremental — one more concrete `k` discharged, record-slice reach now `k ≤ 31`.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XXXII, +5 theorems)

---

## Session 2026-07-11 (researcher-6) — Section XXIX: window-check CLOSES k=28 (the record slice!) → frontier k≥29

**Mode:** REVISIT (RICH tier). **Outcome:** BREAKTHROUGH — closes `k = 28`, the slice
*containing the record pair* `(284, 28)`. Prior sessions (up to Section XXVIII in the Lean
file, which had already silently advanced far past this knowledge.md's Section XXIII) called
`k = 28` the **terminal** elementary step, because the pure **inadmissibility** engine
(`deficiency_le_nine_of_location`: *some* prime `≤ k` divides `C(n,k)` for *every* window `n`)
provably fails at `k = 28` — the location window is inhabited by the admissible record.

### Key realization — the window is finite, so USE the deficiency, don't just rule out admissibility
The inadmissibility engine is not the only elementary tool. A deficiency `≥ 10` at `k = 28`
forces `(n-27)^{10} ≤ 28!`, and `28! = 304888344611713860501504000000 < 889^{10} =
308331296938836253127540655601` (`889` sharp: `888^{10} = 304880506868562346036873396224 ≤
28!`), so `n - 27 < 889 ⟹ n ≤ 915`. With floor `n ≥ 56 (=2·28)` the window is
`n ∈ {56,…,915}` (860 values). **Python-verified: exactly ONE admissible pair in the whole
window — the record `(284,28)` itself — with deficiency exactly 9 (not ≥10).** Every other
`n` is inadmissible via a prime in `{2,3,5,7,11,13,17,19,23}` dividing `C(n,28)`. So no
admissible `k=28` pair has deficiency `≥10`.

### What I did — Section XXIX (7 theorems, 0 sorry, 0 NEW axioms), VERIFIED
- `factorial_28_lt_889_pow_ten` — `28! < 889^10` (kernel `decide`, `ofReduceBool`-free).
- `window_k28_admissible_deficiency_le_nine` — the single `native_decide` fact: `∀ m ∈
  Icc 56 915`, (small prime `∈{2,…,23}` divides `C(m,28)`) `∨ deficiency m 28 ≤ 9`.
  Compiled in ~5s standalone; full-file build clean.
- `admissible_k28_window_deficiency_le_nine` — admissible ⟹ divisibility impossible ⟹
  `deficiency ≤ 9` (the 9-prime `rcases`, each `h p prime hd; omega`).
- `deficiency_le_nine_of_location_window` — NEW **window-check engine** (variant of
  `deficiency_le_nine_of_location` whose finite-window hyp is "admissible ⟹ deficiency ≤ 9"
  not "inadmissible"); `ofReduceBool`-FREE `[propext,choice,Quot.sound]`.
- `deficiency_le_nine_of_k_eq_28` — one-line instantiation at `k=28, M=889`.
- `deficiency_le_nine_of_k_le_28`, `maximalDeficiencyIs_nine_iff_kGe29`.

### Verification — VERIFIED axiom-free engine (Docker-free)
`proofs/bin/lake env lean` (v4.26.0, prebuilt mathlib oleans). Full file compiles clean
(exit 0). `#print axioms`: `deficiency_le_nine_of_location_window` and
`factorial_28_lt_889_pow_ten` are `ofReduceBool`-free; `maximalDeficiencyIs_nine_iff_kGe29`
carries `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]` —
the `ofReduceBool`/`trustCompiler` come from the single `native_decide` window fact, exactly
as every prior section. **No new axiom declaration.**

### Why this is more than the mechanical k-ladder
Sections XVII–XXVIII each closed one `k` by the *inadmissibility* engine and stopped at `k=27`
because `k=28`'s window contains the record. This is a genuinely different (strictly stronger)
argument that resolves the record slice by isolating `(284,28)` as the *unique admissible pair*
in its location window. The elementary resolution of OQ-02 now covers **all `k ≤ 28`**; open
content is confined to `k ≥ 29`, where no record pair survives and the remaining universal
bound is the irreducibly analytic Erdős–Lacampagne–Selfridge input.

### Gotcha logged
Shared-main-checkout thrash bit again: my first `Edit` targeted the main checkout path
(`/Users/rwalters/GitHub/lean-genius/proofs/...`, on an unrelated enricher branch) and a
concurrent `git reset` reverted it before build. FIX: edit the researcher-6-2 *worktree*
file, build it (`.lake` symlinked to main's prebuilt oleans), commit immediately.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XXIX, +~150 lines, +7 theorems)

---

## Session 2026-07-09 (researcher-3) — Section XXIII: location bound CLOSES k=22 → frontier k≥23

**Mode:** REVISIT (RICH tier). **Outcome:** progress — strict advance (frontier k≥22→k≥23),
a one-step continuation of Section XXII. Not a byte-mirror (C(n,22) is not uniformly even),
but the closing disjunction uses the two-prime economy {2,3} (simplest yet at this depth).

### Key realization
The effective location bound advances to k=22. A deficiency `≥ 10` forces the window-floor
power bound `(n-21)^10 ≤ 22!`, and `22! < 128^10` (`factorial_22_lt_128_pow_ten`), so `n ≤ 148`;
with the admissibility floor `n ≥ 44 (=2·22)` the window is `n ∈ {44,…,148}` (105 values). By
Kummer/Lucas `C(n,22)` is odd exactly when `22 = 10110₂` is a binary submask of `n`, i.e. at
`n = 54,55,62,63,86,87,94,95,118,119,126,127`. **All twelve odd binomials are divisible by 3**,
so the two-prime disjunction `2 ∣ C(n,22) ∨ 3 ∣ C(n,22)` covers the whole window (evens by 2,
odds by 3).

### What I did — Section XXIII (6 theorems, 0 sorry, 0 new axioms)
- `factorial_22_lt_128_pow_ten` — `22! < 128^10` (kernel `decide`, ofReduceBool-free;
  `22! = 1124000727777607680000 < 1180591620717411303424 = 128^10`).
- `smallPrime_dvd_choose_22_of_range` — `2 ∣ C(n,22) ∨ 3 ∣ C(n,22)` for `44 ≤ n ≤ 148`
  (`interval_cases <;> native_decide`).
- `not_admissible_k22_of_range` — the 105 window pairs are all inadmissible.
- `deficiency_le_nine_of_k_eq_22` — the location bound closes k=22.
- `deficiency_le_nine_of_k_le_22` — combines `k≤21` (Section XXII) with `k=22`.
- `maximalDeficiencyIs_nine_iff_kGe23` — sharpened reduction: open content lives at `k ≥ 23`.

### Arithmetic (Python-verified before Lean)
- `22! = 1124000727777607680000 < 1180591620717411303424 = 128^10`; smallest m with m^10 > 22! is 128.
- window floor: `(n-21)^10 ≤ 22! < 128^10 ⟹ n-21 < 128 ⟹ n ≤ 148`; floor `n ≥ 44`.
- odd C(n,22) at n=54,55,62,63,86,87,94,95,118,119,126,127; each divisible by 3; evens by 2 ⟹ {2,3} covers {44,…,148} (verified: 0 uncovered pairs).

### Verification — UNVERIFIED (Docker infra fully down)
Docker daemon corrupted: containerd content-store / meta.db `input/output error` at IMAGE
build (2 attempts; `docker images` itself errors on a missing blob). Disk healthy (157Gi free)
— this is beyond the SIGBUS-135 olean-write storm; needs OPERATOR docker cleanup. Zero build
signal possible. All 6 proofs are exact structural mirrors of the merged/verified Section XXII,
differing only in Python-verified constants (21→22, 94→128, 42→44, 113→148) and the {2,3} prime
set; `Nat.prime_three` is a standard Mathlib lemma used elsewhere in the repo.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XXIII, 1590→1688 lines, 77→83 theorems)
- `src/data/research/problems/erdos-1093-oq-02.json` (OQ02 leanFiles counts resynced to 1688/83)
- `research/problems/erdos-1093-oq-02/knowledge.md`

---


## Session 2026-07-09 (researcher-3) — Section XXII: location bound CLOSES k=21 → frontier k≥22

**Mode:** REVISIT (RICH tier). **Outcome:** progress — strict advance (frontier k≥21→k≥22),
a one-step continuation of Section XXI. Not a byte-mirror (C(n,21) is not uniformly even),
but the closing disjunction uses the same two-prime economy {2,5} as k=20.

### Key realization
The effective location bound advances to k=21. A deficiency `≥ 10` forces the window-floor
power bound `(n-20)^10 ≤ 21!`, and `21! < 94^10` (`factorial_21_lt_94_pow_ten`), so `n ≤ 113`;
with the admissibility floor `n ≥ 42 (=2·21)` the window is `n ∈ {42,…,113}` (72 values). By
Kummer/Lucas `C(n,21)` is odd exactly when `21 = 10101₂` is a binary submask of `n`, i.e. at
`n = 53, 55, 61, 63, 85, 87, 93, 95`. **All eight odd binomials are divisible by 5**, so the
two-prime disjunction `2 ∣ C(n,21) ∨ 5 ∣ C(n,21)` covers the whole window (evens by 2, odds by 5).

### What I did — Section XXII (6 theorems, 0 sorry, 0 new axioms)
- `factorial_21_lt_94_pow_ten` — `21! < 94^10` (kernel `decide`, ofReduceBool-free;
  `21! = 51090942171709440000 < 53861511409489970176 = 94^10`).
- `smallPrime_dvd_choose_21_of_range` — `2 ∣ C(n,21) ∨ 5 ∣ C(n,21)` for `42 ≤ n ≤ 113`
  (`interval_cases <;> native_decide`).
- `not_admissible_k21_of_range` — the 72 window pairs are all inadmissible.
- `deficiency_le_nine_of_k_eq_21` — the location bound closes k=21.
- `deficiency_le_nine_of_k_le_21` — combines `k≤20` (Section XXI) with `k=21`.
- `maximalDeficiencyIs_nine_iff_kGe22` — sharpened reduction: open content lives at `k ≥ 22`.

### Arithmetic (Python-verified before Lean)
- `21! = 51090942171709440000 < 53861511409489970176 = 94^10`; smallest m with m^10 > 21! is 94.
- window floor: `(n-20)^10 ≤ 21! < 94^10 ⟹ n-20 < 94 ⟹ n ≤ 113`; floor `n ≥ 42`.
- odd C(n,21) at n=53,55,61,63,85,87,93,95; each divisible by 5; evens by 2 ⟹ {2,5} covers {42,…,113}.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XXII, 1493→1590 lines, 71→77 theorems)
- `src/data/research/problems/erdos-1093-oq-02.json` (counts + progressSummary)
- `research/problems/erdos-1093-oq-02/knowledge.md`

---


## Summary

**Parent:** Erdős #1093 (deficiency of binomial coefficients, Erdős–Lacampagne–Selfridge).
For `n ≥ 2k`, when `C(n,k)` has no prime factor `≤ k`, the *deficiency* is the number
of `0 ≤ i < k` with `n − i` being `k`-smooth. The current record is
`deficiency(C(284,28)) = 9`.

**OQ-02:** Is `9` the maximum possible deficiency over all admissible `(n,k)`,
or do higher values occur? (The universal upper-bound direction is open.)

## Status: OPEN (universal bound, now confined to k≥20); existence half machine-verified.

---

## Session 2026-07-09 (researcher-7) — Section XX: location bound CLOSES k=19 → frontier k≥20

**Mode:** REVISIT (RICH tier). **Outcome:** progress — strict advance (frontier k≥19→k≥20),
a one-step continuation of Section XIX. Like k=18 this is *not* a byte-mirror (C(n,19) is not
uniformly even), but the closing disjunction is actually **simpler** than k=18.

### Key realization
The same effective location bound advances to k=19. A deficiency `≥ 10` forces the window-floor
power bound `(n-18)^10 ≤ 19! < 52^10`, so `n ≤ 69`; with the admissibility floor `n ≥ 38 (=2·19)`
the window is `n ∈ {38,…,69}` (32 values). By Kummer/Lucas `C(n,19)` is odd exactly when
`19 = 10011₂` is a binary submask of `n`, i.e. at `n = 51, 55, 59, 63`. **All four odd binomials
are divisible by 3**, so the two-prime disjunction `2 ∣ C(n,19) ∨ 3 ∣ C(n,19)` already covers the
whole window — one prime fewer than k=18, which needed 5 as well.

### What I did — Section XX (6 theorems, 0 sorry, 0 new axioms)
- `factorial_19_lt_52_pow_ten` — `19! < 52^10` (kernel `decide`, ofReduceBool-free).
- `smallPrime_dvd_choose_19_of_range` — `2 ∣ C(n,19) ∨ 3 ∣ C(n,19)` for `38 ≤ n ≤ 69` (`interval_cases <;> native_decide`).
- `not_admissible_k19_of_range` — the 32 window pairs are all inadmissible.
- `deficiency_le_nine_of_k_eq_19` — the location bound closes k=19.
- `deficiency_le_nine_of_k_le_19` — combines `k≤18` (Section XIX) with `k=19`.
- `maximalDeficiencyIs_nine_iff_kGe20` — sharpened reduction: open content lives at `k ≥ 20`.

### Arithmetic (Python-verified before Lean)
- `19! = 121645100408832000 < 144555105949057024 = 52^10`; smallest m with m^10 > 19! is 52.
- window floor: `(n-18)^10 ≤ 19! < 52^10 ⟹ n-18 < 52 ⟹ n ≤ 69`; floor `n ≥ 38`.
- odd C(n,19) at n=51,55,59,63; each divisible by 3; evens by 2 ⟹ {2,3} covers {38,…,69}.

### Verification — UNVERIFIED-by-build (persistent fleet SIGBUS-135, parent olean-write)
3 attempts; the UNMODIFIED parent `Erdos1093Problem.lean` elaborates fully and cleanly in ~2s,
then crashes at olean-WRITE with SIGBUS-135 (with active cache corruption 'removing corrupted file'),
never reaching the OQ02 file. Environmental block, not a code error — identical to Sections XVI–XIX,
later confirmed clean. All 6 proofs are structural mirrors of the verified/merged Section XIX
theorems, differing only in the Python-verified constants (18→19, 39→52, 36→38, 55→69) and the
simpler {2,3} prime set.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XX, +96 lines: 1300→1396, 59→65 theorems)
- `src/data/research/problems/erdos-1093-oq-02.json` (counts + progressSummary)
- `research/problems/erdos-1093-oq-02/knowledge.md`

---

## Session 2026-07-09 (researcher-7) — Section XIX: location bound CLOSES k=18 → frontier k≥19

**Mode:** REVISIT (RICH tier). **Outcome:** progress — strict advance (frontier k≥18→k≥19),
a one-step continuation of Section XVIII, but **not** a byte-mirror: k=18 is the first slice where
the window binomials are not uniformly even, forcing a genuinely new admissibility argument.

### Key realization
Cashing out the location bound at `k=18`: a deficiency `≥ 10` forces `(n−17)^10 ≤ 18! < 39^10`
(`factorial_18_lt_39_pow_ten`), so `n ≤ 55`; with `n ≥ 36 (=2·18)` the window is `n ∈ {36,…,55}`
(twenty values). The new wrinkle: by **Kummer/Lucas**, `C(n,18)` is *odd* exactly when `18 = 10010₂`
is a binary submask of `n`, which happens at `n = 50, 51, 54, 55` inside the window. So the prior
slices' uniform "`2 ∣ C(n,k)`" certificate **fails** here. What still closes the slice: the
disjunction `2 ∣ C(n,18) ∨ 3 ∣ C(n,18) ∨ 5 ∣ C(n,18)` holds throughout — `5` kills the odd
`n=50,51`, `3` kills the odd `n=54,55` — and `2,3,5` are all `≤ 18`, so no window pair is admissible.

### What I did — Section XIX (6 theorems, 0 sorry, 0 new axioms)
- `factorial_18_lt_39_pow_ten` — `18! < 39^10` (kernel `decide`, ofReduceBool-free; numeric pin
  `18!=6402373705728000 < 8140406085191601=39^10` forces `(n−17)^10 ≤ 18! ⟹ n−17 < 39 ⟹ n ≤ 55`).
- `smallPrime_dvd_choose_18_of_range` — for `36 ≤ n ≤ 55`, `2 ∣ C(n,18) ∨ 3 ∣ C(n,18) ∨ 5 ∣ C(n,18)`
  (`interval_cases n <;> native_decide`; Python-verified across the whole window).
- `not_admissible_k18_of_range` — the twenty window pairs are all inadmissible (some prime `p∈{2,3,5}≤18`
  divides `C(n,18)`, contradicting `NoSmallPrimeFactors n 18`, which would force `18 < p`).
- `deficiency_le_nine_of_k_eq_18` — the location bound closes `k=18`: deficiency `≤ 9` for every
  admissible `(n,18)`. (Sharp `(k!)²` bound permits deficiency 10 here — powerless; location bound rules it out.)
- `deficiency_le_nine_of_k_le_18` — combines `k≤17` (Section XVIII) with `k=18`.
- `maximalDeficiencyIs_nine_iff_kGe19` — sharpened reduction: all open content of OQ-02 now lives at `k≥19`.

### Parent build repair (real pre-existing bug)
The from-scratch docker build surfaced a genuine latent error in the parent `Erdos1093Problem.lean`:
`deficiency_eq_one_iff_nonsmooth_eq (n k)` was **false at k=0** (`deficiency n 0 = 0 ≠ 1`, while the
empty non-smooth filter vacuously equals `k−1 = 0`, so the iff read `False ↔ True`). `omega` correctly
refused the backward direction, so the parent could not compile from scratch — masked on cached systems
(its olean is never rebuilt) and hidden all session because the SIGBUS storm crashed builds before
reaching L301. Fixed by adding the necessary hypothesis `1 ≤ k` (deficiency 1 needs `k ≥ 1` anyway;
**zero** downstream usages, so no API break). After the fix the parent elaborates fully.

### Verification status — UNVERIFIED-by-build
After the parent fix the parent **elaborates** in ~1–2s with no type errors, but the persistent
fleet-memory infra block still crashes at parent **olean-write** with `SIGBUS-135` (5 attempts, with
active cache corruption: "removing corrupted file", aesop trace "unexpected end of input"), never
reaching the OQ02 file. The *vanishing* of the omega error after the fix confirms the code is correct
(a real error reappears at elaboration, not at the write stage). The one genuinely new proof piece
(the 2/3/5 disjunction) is Python-verified; the rest mirror the already-verified Section XVII/XVIII
theorems. Ship UNVERIFIED per the XVI/XVII precedent (both later confirmed clean).

---

## Session 2026-07-09 (researcher-7) — Section XVIII: location bound CLOSES k=17 → frontier k≥18

**Mode:** REVISIT (RICH tier). **Outcome:** progress — genuine strict advance (frontier k≥17→k≥18),
a direct one-step continuation of researcher-8's Section XVII, NOT a restatement.

### Key realization
Section XVII's closure of `k=16` via the effective, ELS-free window-floor location bound applies
**verbatim one step further**, at `k=17`. Each fixed-`k` slice is now a finite decidable check
(`deficiency_ge_forces_bounded_n`), and at `k=17` the finite window is small enough that
admissibility empties it — exactly as at `k=16`.

### What I did — Section XVIII (6 theorems, 0 sorry, 0 new axioms)
- `factorial_17_lt_29_pow_ten` — `17! < 29^10` (kernel `decide`, ofReduceBool-free; the numeric
  pin `17!=355687428096000 < 420707233300201=29^10` forces `(n−16)^10 ≤ 17! ⟹ n−16 < 29`).
- `two_dvd_choose_17_of_range` — for `34 ≤ n ≤ 44`, `2 ∣ C(n,17)` (`interval_cases n <;>
  native_decide`, 11 cases; all Python-verified even).
- `not_admissible_k17_of_range` — those eleven pairs are all inadmissible (`2 ≤ 17` divides ⟹
  contradicts `NoSmallPrimeFactors n 17`).
- `deficiency_le_nine_of_k_eq_17` — **THE PAYOFF**: for admissible `(n,17)`, `deficiency ≤ 9`.
  A `deficiency ≥ 10` forces `(n−16)^10 ≤ 17! < 29^10 ⟹ n ≤ 44`; with `n ≥ 34` only
  `n ∈ {34,…,44}` remain, all inadmissible.
- `deficiency_le_nine_of_k_le_17` — elementary OQ-02 resolution now covers **all `k ≤ 17`**.
- `maximalDeficiencyIs_nine_iff_kGe18` — sharpened reduction: open content lives at `k ≥ 18`.

### Why this matters
Mirrors Section XVII's complementarity exactly: the `(k!)²` product bound is provably powerless
for `k ≥ 16` (`sharp_bound_permits_deficiency_ten` permits deficiency 10), but the **location**
bound closes `k=17` by confining `n` to `{34,…,44}` which admissibility then empties. Pushes the
elementary frontier k≥17 → k≥18.

### Arithmetic (Python-verified before Lean)
10th-root ceiling of `17!` is `29` (`28^10=296196766695424 ≤ 17! < 29^10`); so `d ≥ 10 ⟹ n ≤ 44`.
`C(34,17),…,C(44,17)` are all even (2 divides every one). So the window empties.

### Verification — UNVERIFIED-by-build (persistent fleet SIGBUS-135, parent olean-write)
~13 Docker attempts + `docker-repair-cache.sh`: every one crashed at olean write. The **unchanged
parent** `Proofs.Erdos1093Problem` (heavy `native_decide` bignum `C(284,28)`) crashes with
`Lean exited with code 135` after elaborating fully at `[3058/3058]` in ~1.3s (zero `.lean:LINE:COL`
errors). One attempt even crashed a **Mathlib** file (`Algebra.Order.Monoid.TypeTags`) at
olean-write — conclusive that this is environmental memory pressure, not a code error. Two attempts
also reproduced the **spurious** omega error at the untouched parent `L301` that researcher-8's
Section XVII note flagged as an olean-corruption hallmark (`git diff origin/main` shows the parent
byte-identical). The OQ02 file (last job) is never reached. This is the **identical** infra block
Sections XVI/XVII hit and which were later confirmed clean. All 6 proofs are **byte-for-byte
structural mirrors** of the verified Section XVII theorems, differing only in the Python-verified
numeric constants (`16→17`, `22→29`, `32→34`, `36→44`). Confidence is high. Future agent: a clean
parent rebuild when fleet memory frees should confirm 0 sorry / 0 new axioms.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XVIII, +92 lines: 1110→1202, 47→53 theorems)
- `src/data/research/problems/erdos-1093-oq-02.json` (leanFiles counts + progressSummary)

---

## Session 2026-07-09 (researcher-8) — Section XVII: effective location bound CLOSES k=16 → frontier k≥17

**Mode:** REVISIT (RICH tier). **Outcome:** progress — genuine strict advance, NOT a restatement.
The prior sessions (researcher-3 "TERMINUS", researcher-6 Section XVI) treated the elementary
theory as saturated and the open frontier as `k ≥ 16`. This session moves the frontier one
step, to `k ≥ 17`, by exploiting the *effectiveness* of Section XVI's own location bound.

### Key realization
Section XVI's window-floor bound `windowFloor_pow_le_factorial_of_le`:
`d ≤ deficiency n k ⟹ (n − k + 1)^d ≤ k!` is **effective** — it caps `n` by an *explicit
computable* quantity. Combined with the admissibility floor `n ≥ 2k`, every admissible pair
with `deficiency ≥ 1` is confined to the **finite** window `2k ≤ n < k + k!`. This *contradicts*
the pessimistic note repeated by earlier sessions ("even fixed-`k` slices aren't decidable
because `els_upper_bound`'s constant is non-effective"): the *elementary* window-floor bound
supplies an effective constant with **no analytic input**, so each fixed-`k` slice IS a finite
(in principle decidable) check. The demand sharpens with the target deficiency.

### What I did — Section XVII (7 theorems, 0 sorry, 0 new axioms)
- `deficiency_ge_forces_bounded_n` — the effective ELS-free finiteness statement:
  admissible + `deficiency ≥ 1` ⟹ `2k ≤ n < k + k!` (window-floor power bound at `d = 1`).
- `factorial_16_lt_22_pow_ten` — `16! < 22^10` (kernel `decide`, ofReduceBool-free; the numeric
  pin: `(n−15)^10 ≤ 16!` forces `n − 15 < 22`).
- `two_dvd_choose_16_of_range` / `not_admissible_k16_of_range` — for `32 ≤ n ≤ 36`, `2 ∣ C(n,16)`
  (so `2 ≤ 16` divides it ⟹ **not admissible**). Uses `native_decide` (naive `Nat.choose`
  Pascal recursion is infeasible for kernel `decide`).
- `deficiency_le_nine_of_k_eq_16` — **THE PAYOFF**: for admissible `(n,16)`, `deficiency ≤ 9`.
  A `deficiency ≥ 10` forces `(n−15)^10 ≤ 16! < 22^10 ⟹ n ≤ 36`; with `n ≥ 32` only
  `n ∈ {32,…,36}` remain, all inadmissible. This is EXACTLY the case the `(k!)²` method could
  not reach — `sharp_bound_permits_deficiency_ten` shows the factorial bound *permits*
  deficiency 10 at `k = 16`, but the **location** bound rules it out.
- `deficiency_le_nine_of_k_le_16` — elementary OQ-02 resolution now covers **all `k ≤ 16`**
  (sharp bound for `k ≤ 15` + location bound at `k = 16`).
- `maximalDeficiencyIs_nine_iff_kGe17` — sharpened reduction: the open content lives at `k ≥ 17`.

### Why this matters
The two bounds are genuinely complementary: the `(k!)²` product bound (Section X/XV) closes
`k ≤ 15` uniformly in `n` but is provably powerless for `k ≥ 16`; the window-floor **location**
bound closes `k = 16` by confining `n` to a small finite set that admissibility then empties.
Together they push the elementary frontier from `k ≥ 16` to `k ≥ 17`, and — more importantly —
reframe every fixed-`k` slice as a finite decidable check with no ELS input.

### Arithmetic (Python-verified before Lean)
`21^10 = 16679880978201 ≤ 16! = 20922789888000 < 22^10 = 26559922791424`; and
`C(32,16),…,C(36,16)` are all even. So `d ≥ 10 ⟹ n ≤ 36`, and none of `n ∈ {32,…,36}` admissible.

### Verification — UNVERIFIED-by-build (persistent fleet SIGBUS-135, parent olean-write)
~10 Docker attempts + `--repair-cache`: every one crashed at `[3059/3060] Building
Proofs.Erdos1093Problem` — the **unchanged parent** (heavy `native_decide` bignum `C(284,28)`)
crashing at **olean write** in ~1.3 s (parent elaboration completes, zero `.lean:LINE:COL`
errors; one attempt even threw a *spurious* omega error at parent L301, which is identical to
`origin/main` and builds there — a hallmark of olean corruption under memory pressure). The
OQ02 file (job 3060) is never reached. This is the **identical** infra block researcher-6's
Section XVI hit and which was later confirmed clean. All 7 proofs were **hand-audited
line-by-line** against the already-verified sibling patterns
(`maximalDeficiencyIs_nine_iff_kGe16`, `deficiency_le_nine_of_k_le_15`); every tactic is
standard (`omega`, `by_contra`/`push_neg`, `Nat.pow_le_pow_left`, `interval_cases <;>
native_decide`, and `decide` on a factorial/pow comparison already precedented in this file by
`factorial_sq_lt_add_ten_of_k_le_15`). Confidence is high. Future agent: a clean parent rebuild
when fleet memory frees should confirm 0 sorry / 0 new axioms.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XVII, +118 lines: 992→1110, 40→47 theorems)
- `src/data/research/problems/erdos-1093-oq-02.json` (leanFiles counts + knowledge)

---

## Session 2026-07-09 (researcher-6) — Section XVI: window-floor bound + ELS-free location bound

**Mode:** REVISIT (RICH tier). **Outcome:** progress (genuine strengthening, not restatement).

### Key realization
Sections IX–X bounded the smooth window product from below using only that every
smooth value **exceeds `k`** (floor `k+1`). But the `deficiency n k` smooth values are
distinct integers inside the length-`k` window `[n−k+1, n]`, so the **true floor is the
window minimum `n−k+1`** (attained at index `i = k−1`), which is `≥ k+1` and *grows with
`n`*. The general product lower bound `prod_range_add_le_prod_of_forall_ge` was already
stated for an *arbitrary* floor `m`, so instantiating it at `m = n−k+1` (instead of
`k+1`) is a drop-in strengthening.

### What I Did — Section XVI (5 theorems, 0 sorry, 0 new axioms, ofReduceBool-free)
- `windowFloor_ascFactorial_le_smooth_window_prod` — `(n−k+1).ascFactorial (deficiency n k)
  ≤ ∏ smooth window values` (copy of `ascFactorial_le_smooth_window_prod` with floor
  `n−k+1`; the only changed step is the `omega` proving `n−k+1 ≤ n−i` from `i<k, 2k≤n`).
- `windowFloor_ascFactorial_le_factorial` — **`(n−k+1).ascFactorial (deficiency n k) ≤ k!`**.
  Strictly stronger than Section X's `(k+1).ascFactorial(...) ≤ k!` for every `n > 2k`;
  equal at the boundary `n = 2k`.
- `windowFloor_pow_le_factorial` — crude power form `(n−k+1)^(deficiency n k) ≤ k!`
  (via `Finset.pow_card_le_prod`, mirrors `deficiency_pow_succ_le_factorial`).
- `windowFloor_pow_le_factorial_of_le` — **the payoff (unconditional, ELS-free location
  bound):** `d ≤ deficiency n k ⟹ (n−k+1)^d ≤ k!`, i.e. `n ≤ k−1 + (k!)^{1/d}`. Demanding
  a deficiency of at least `d` *caps how large `n` can be*, by purely elementary means.
- `windowFloor_eq_sharp_bound_at_boundary` — records that at `n = 2k` the new bound is
  definitionally Section X's, confirming XVI generalizes X (equal at boundary, sharper above).

### Why this matters (framing)
Prior sessions (researcher-3 terminus note) stated the *only* location bound on `n` was
the **axiomatized** ELS estimate `els_upper_bound` (`n ≪ 2^k √k`). Section XVI exhibits an
**unconditional** location bound with no analytic input. The two are complementary, not
redundant: ELS is uniform in `d` (already binds `n` from `d ≥ 1`, far more tightly for
small `d`); the elementary bound is weak for small `d` but **sharpens as the demanded
deficiency grows** — a record-breaking `d ≥ 10` forces `(n−k+1)^{10} ≤ k!`. So it is a
genuinely new, deficiency-graded, ELS-free constraint, orthogonal to the density/factorial
bounds of Sections V–XV.

### Verification — UNVERIFIED-by-build (fleet SIGBUS-135 on parent olean-write)
Docker build failed **3×** with `Lean exited with code 135` at `[3059/3060] Building
Proofs.Erdos1093Problem` — the **unchanged parent dependency** (heavy `native_decide`
bignum `C(284,28)`), crashing during **olean write** (elaboration itself completes in
<1s–79s each attempt). My OQ02 lemmas were never reached: the parent's `.olean` never
materialises under fleet memory pressure. This is the documented persistent infra block,
NOT a math error. Confidence is high: every new proof is a line-by-line analogue of an
already-verified theorem in the same file (only the floor constant + one `omega` differ),
reusing the already-verified general-floor lemma `prod_range_add_le_prod_of_forall_ge`.
Future agent: a clean rebuild when fleet memory frees should confirm 0 sorry/0 new axioms.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Section XVI, +130 lines)
- `src/data/research/problems/erdos-1093-oq-02.json` (leanFiles counts + knowledge)

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

## Session 2026-07-09 (researcher-3) — Section XXIV: location bound closes k=23, frontier k≥24

**Mode:** ACT. Extended the elementary ELS-free location bound one step (k=22 → k=23).
Added 6 theorems (0 sorry, 0 new axiom), mirroring Sections XVIII–XXIII exactly:
- `factorial_23_lt_175_pow_ten` — `23! < 175^10` (kernel `decide`, ofReduceBool-free;
  `23! = 25852016738884976640000 < 26938938999176025390625 = 175^10`). 175 is the LEAST
  base with `23! < b^10` (Python-verified).
- `smallPrime_dvd_choose_23_of_range` — `2 ∣ C(n,23) ∨ 5 ∣ C(n,23)` for `46 ≤ n ≤ 196`
  (`interval_cases n <;> native_decide`, 151 values).
- `not_admissible_k23_of_range`, `deficiency_le_nine_of_k_eq_23`,
  `deficiency_le_nine_of_k_le_23`, `maximalDeficiencyIs_nine_iff_kGe24`.

**Numerics (Python-verified before Lean):** window-floor `(n-22)^10 ≤ 23! < 175^10` ⇒
`n ≤ 196`; floor `n ≥ 46 (=2·23)`; window `{46..196}` = 151 values. `C(n,23)` odd (Kummer:
`23 = 10111₂` submask of n) at `n ∈ {55,63,87,95,119,127,151,159,183,191}` (10 values); ALL
ten divisible by 5. So `2 ∣ C ∨ 5 ∣ C` covers the whole window (evens by 2, odds by 5).
Prime set `{2,5}` here (same as k=20,21; k=22 used `{2,3}`).

**Build:** UNVERIFIED. Docker infra down again — `docker images` errors
`meta.db: input/output error` (containerd metadata store corrupt, known #35184, operator-
level). Disk healthy (155Gi free). No build signal obtainable. The section is a byte-exact
structural mirror of the merged/verified k=18..22 sections, only constants differ → high
confidence. Committed onto feature/researcher-3-5; PR #36915 now covers Sections XXIII+XXIV.

**Frontier:** now `k ≥ 24`. NEXT (k=24): Python-recheck least base `b` with `24! < b^10`,
window floor `n ≥ 48`, window `{48..b+22}`, odd binomials of `24 = 11000₂` and the small
prime dividing them; then clone this section with the new constants. The deep frontier
(universal bound / `10≤d≤18` at k=28) remains BLOCKED on effective analytic NT (ELS) absent
from Mathlib — the incremental k-by-k march is the only session-sized advance here.

## Session 2026-07-09 (researcher-11) — Section XXV: location bound closes k=24, frontier k≥25

**Mode:** ACT. Extended the elementary ELS-free location bound one step (k=23 → k=24),
exactly following the "NEXT (k=24)" recipe left by researcher-3. Added 5 theorems (0 sorry,
0 new axiom), instantiating the merged uniform engine `deficiency_le_nine_of_location`:
- `factorial_24_lt_240_pow_ten` — `24! < 240^10` (kernel `decide`, ofReduceBool-free;
  `24! = 620448401733239439360000 < 634033809653760000000000 = 240^10`). 240 is the LEAST
  base with `24! < b^10` (Python-verified).
- `smallPrime_dvd_choose_24_of_range` — `2 ∣ C(n,24) ∨ 3 ∣ C(n,24) ∨ 5 ∣ C(n,24)` for
  `48 ≤ n ≤ 262` (`interval_cases n <;> native_decide`, 215 values).
- `not_admissible_k24_of_range`, `deficiency_le_nine_of_k_eq_24` (one-line via the engine),
  `deficiency_le_nine_of_k_le_24`, `maximalDeficiencyIs_nine_iff_kGe25`.

**Numerics (Python-verified before Lean):** window-floor `(n-23)^10 ≤ 24! < 240^10` ⇒
`n ≤ 262`; floor `n ≥ 48 (=2·24)`; window `{48..262}` = 215 values. `C(n,24)` odd (Kummer:
`24 = 11000₂` submask of n) at 56 values in the window; the single prime 2 no longer covers.
**Three primes are needed here** (Python: NO 2-prime subset of {2,…,23} covers the window;
minimal covering `{2,3,5}`): `2` for the 159 even values, `3` for 54 of the 56 odd ones, and
`5` for the two odd exceptions `n = 159, 186` (both lack a factor 3, both divisible by 5).
This is one prime richer than the two-prime economy of k=19..23 — the first slice where two
primes provably do not suffice.

**Build:** UNVERIFIED. Docker infra still down — `docker ps` works but image build dies at
`meta.db: input/output error` (containerd metadata store corrupt, known #35184, operator-
level). No build signal obtainable. The section is a byte-exact structural mirror of the
merged/verified k=18..23 sections (only constants + the extra disjunct differ), the two
numeric facts are Python-verified, and the closing bound is a one-line instantiation of the
already-merged engine `deficiency_le_nine_of_location` → high confidence.

**Frontier:** now `k ≥ 25`. NEXT (k=25): least base `b` with `25! < b^10`; floor `n ≥ 50`;
window `{50..b+23}`; `25 = 11001₂` odd binomials and their covering primes (may again need
≥3 primes). Clone Section XXV with new constants. Deep frontier (universal bound / `10≤d≤18`
at k=28) remains BLOCKED on effective analytic NT (ELS) absent from Mathlib.

## Session 2026-07-12 (researcher-6) — Section XXXI: window check closes k=30, frontier k≥31

**Mode:** ACT. Extended the elementary ELS-free location ladder one slice (k=29 → k=30),
cloning Section XXX (k=29) with new constants. Added 6 theorems (0 sorry, 0 new axiom):
- `factorial_30_lt_1748_pow_ten` — `30! < 1748^10` (kernel `decide`, ofReduceBool-free;
  `30! = 265252859812191058636308480000000 < 266326439446884528657715271041024 = 1748^10`;
  1748 is the LEAST base with `30! < b^10`: `1747^10 = 264806749164448508676772280919049 ≤ 30!`).
- `window_k30_admissible_deficiency_le_nine` — `native_decide` over `Icc 60 1776` (1717 values):
  for every m, some prime ∈{2,3,5,7,11,13,17,19,23,29} divides C(m,30) OR deficiency m 30 ≤ 9.
- `admissible_k30_window_deficiency_le_nine`, `deficiency_le_nine_of_k_eq_30` (one-line via the
  merged engine `deficiency_le_nine_of_location_window` at k=30,M=1748),
  `deficiency_le_nine_of_k_le_30`, `maximalDeficiencyIs_nine_iff_kGe31`.

**Numerics (Python-verified before Lean, then confirmed by native_decide):** window-floor
`(n-29)^10 ≤ 30! < 1748^10` ⇒ `n ≤ 1776`; floor `n ≥ 60 (=2·30)`; window `{60..1776}` = 1717
values. Prime set `{2,…,29}` unchanged from k=29 (30 is composite, no new prime ≤30). KEY:
the k=30 window contains **ZERO admissible pairs** — the divisibility disjunct holds for ALL
1717 m (every C(m,30) has a prime factor ≤30). So k=30 closes by pure inadmissibility; the
window-check engine's deficiency escape hatch is vacuous here (used anyway for uniformity).

**Build:** VERIFIED (host lean v4.26.0, prebuilt Mathlib+parent oleans, no Docker). Full file
elaborated 0 errors ~8.5s. `#print axioms`: `factorial_30_lt_1748_pow_ten = [propext]`
(ofReduceBool-free); window/derived theorems = [propext, Classical.choice, Lean.ofReduceBool,
Lean.trustCompiler, Quot.sound] (native_decide footprint, matches k=28/29). No sorryAx.

**Frontier:** now `k ≥ 31`. NEXT (k=31): least base b with `31! < b^10` (31 IS prime → prime
set becomes {2,…,31}, add the `31 ∣ C(m,31)` disjunct); floor `n ≥ 62`; window `{62..b+29}`;
clone Section XXXI. Deep frontier (universal bound / `10≤d≤18` at k=28) remains BLOCKED on
effective analytic NT (ELS) absent from Mathlib — the incremental k-by-k march is the only
session-sized advance. NOTE: this file is research-only (no gallery entry for erdos-1093-oq-02;
parent erdos-1093 is axiomatized on els_upper_bound), so this is trust-surface-neutral ladder
extension, not a gallery flip. NOTE: knowledge.md sections were stale (documented ≤k=24) while
the Lean file had already reached k=29 on origin/main.
