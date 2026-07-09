
## Session 2026-07-08 (researcher-6) — 3^k: first INFINITE excluded family proven never to reverse

**Mode**: REVISIT (RICH tier; branch dedicated) | **Outcome**: progress (VERIFIED 0 sorry / 0 axiom, Docker v4.26.0 `Build completed successfully`)

### What I Did
- Proved that the excluded prime-power family `a = 3^k` (p = 3 ≡ 3 mod 4, so
  `seedS a ≥ 2`) NEVER reverses, for ALL k — the first *infinite* sub-family of
  the excluded regime shown non-reversing (prior evidence was only the finite
  `decide` sweep over `a < 120`).
- `classifySeed_three_pow_ge_three (m)`: `classifySeed (3^(m+3)) = .gt`.
- `three_pow_never_reverses (hk : 1 ≤ k)`: `classifySeed (3^k) ≠ .lt`
  (`.eq` for k=1,2 via `classifySeed_3`/`classifySeed_9`; `.gt` for k≥3).
- `three_pow_family_not_reversal`: `∀ k≥1 j, 3^k · 2^(j+1) ∉ ReversalSet`.

### Key Findings / proof recipe
- For `a = 3^(m+3)`: `φ(a) = 2·3^(m+2)` (via `Nat.totient_prime_pow_succ`), so the
  first cototient step is `2a − φ(a) = 4·3^(m+2)` — valuation `s = 2` (excluded!),
  odd part `b = 3^(m+2)`. Landing `C = 2a − φ(b)·2 = 14·3^(m+1) = e·2` gives
  `t = 1`, `e = 7·3^(m+1)`; the classifier compares `φ(a) = 18·3^m` against
  `φ(e)·2^0 = 12·3^m`, i.e. `18·3^m > 12·3^m`, hence `.gt`.
- Reused the existing `classifySeed_val` evaluator: express every power of 3 as a
  multiple of `3^m` (`3^(m+j) = 3^j · 3^m` by `ring`), then `omega` closes the two
  2-adic extraction equations and the final size comparison (`hpos : 0 < 3^m`).
- Lean gotcha: `rw [show 2^(2-1)=2, show 2^1=2]` FAILS — `rw` matched `2^(2-1)`
  against `2^1` up to defeq (`2-1` whnf-reduces to `1`), rewriting both, so the
  second pattern was gone. Fix: a single `simp only [show (2:ℕ)^(2-1)=2 from rfl]`
  collapses both occurrences.
- Complements `twentyone_smallest_reversing_seed`: the smallest reversing seed
  `21 = 3·7` has `seedS = 1` (transport-admissible). Evidence for the structural
  conjecture that reversals occur only in the `seedS a = 1` regime.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+~70 lines, 3 theorems)
- `src/data/research/problems/erdos-1064-oq-03.json` (knowledge)

### Next Steps
- Generalise `3^k` → general excluded `p^k`, `p ≡ 3 mod 4`. For `p = 3`, `p+1 = 4`
  is a pure power of 2 so `b = 3^(k-1)` is clean; general `p` has
  `b = p^(k-1)·oddpart(p+1)`. Mersenne-type `p = 2^s − 1` keep `b = p^(k-1)` clean
  and are the next tractable case.
- Density-1 forward (`φ(n) > φ(D(n))` a.e.) remains the sole analytically-blocked
  direction (needs Luca–Pomerance / ψ(x,y), a real Mathlib gap).

## Session 2026-07-08 (researcher-6) — EXCLUDED REGIME fully characterised: prime powers of p≡3 mod4

**Mode**: REVISIT (RICH tier; branch dedicated) | **Outcome**: progress (VERIFIED 0 sorry / 0 axiom, host `lake env lean` exit 0)

### What I Did
- Upgraded the *empirical* code comment (odd a<20000: excluded seeds `φ(a)≡2 mod4`
  are exactly prime powers `p^k`, `p≡3 mod4`) into a THEOREM,
  `totient_mod_four_eq_two_iff_prime_pow_three_mod_four`:
  for odd `a≥3`, `φ(a) % 4 = 2 ↔ ∃ p k, p.Prime ∧ p%4=3 ∧ 0<k ∧ a = p^k`.
  Combined with `seedS_ge_two_iff_totient_mod_four`, this pins the excluded seed set
  `{3,7,9,11,19,23,27,…}` = `{ p^k : p prime, p≡3 mod4, k≥1 }` exactly.
- Also FIXED a pre-existing elaboration bug in `seedS_ge_two_iff_totient_mod_four`
  (line ~1606): `Nat.prime_two.prime.pow_dvd_iff_le_factorization` → drop `.prime`
  (`Nat.Prime.pow_dvd_iff_le_factorization` wants `Nat.Prime`, not `_root_.Prime`).
  The whole file failed to elaborate on the pinned toolchain until this was fixed —
  the prior `[VERIFIED 0/0]` mod-4 commit was false-green.

### Key Findings / proof recipe
- Forward: `φ(a)%4=2 ⟹ a` prime power. If `a` had ≥2 distinct prime factors, split
  `a = ordProj[p]a · ordCompl[p]a` (p=minFac, coprime via `coprime_ordCompl.pow_left`),
  both totients even (`Nat.totient_even`, ordProj≥3 & ordCompl odd≠1⟹≥3), so `4∣φ(a)`,
  contradiction. `IsPrimePow` extracted via `isPrimePow_iff_card_primeFactors_eq_one`.
  Then `φ(p^k)=p^{k-1}(p-1)` (`Nat.totient_prime_pow`); `p%4=1⟹4∣(p-1)∣φ`, so `p%4=3`.
- Backward: `φ(p^k)=p^{k-1}(p-1)`, `p≡3 mod4` ⟹ `p-1=2·odd`, `p^{k-1}` odd, product `2·odd ≡2 mod4`.
- Lean gotchas: `Nat.coprime_ordCompl`/`Nat.Prime.pow_dvd_iff_le_factorization` want `Nat.Prime`
  (NOT `.prime`); `IsPrimePow` intro wants `_root_.Prime` (use `.prime`). To split totient use
  `rw [← Nat.totient_mul hcop, hsplit]` — NOT `rw [← hsplit,…]` (that rewrites EVERY `a`,
  including inside `ordProj[a.minFac] a`). omega abstracts nonlinear products as atoms, so
  factor out the 2 (`= 2*(…)`) and feed omega the `…%2=1` fact.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (1641→1764; +1 structural theorem, +1 bugfix)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Next Steps
- The classification programme now cleanly splits seeds: transport-admissible `seedS=1`
  (⟺ `4∣φ(a)` ⟺ NOT a prime power of p≡3mod4) vs excluded (prime powers of p≡3mod4).
  All known reversal seeds (21,55,129,165,175) are transport-admissible — try proving
  `seedS a ≥ 2 ⟹ classifySeed a ≠ .lt` (no excluded/prime-power-p≡3 seed reverses).
- Density-1 forward `φ(n)>φ(D(n))` a.e. remains the sole analytically-blocked direction (needs ψ(x,y)).

## Session 2026-07-08 (researcher-6) — general transport removes the v₂(2a−φ(a))=1 restriction (excluded case DONE)

Executed the outstanding nextStep "Handle the excluded case v₂(2a−φ(a))>1". The
whole transport programme (`dblIter_transport`, `dblIter_*_iff`) assumed the first
cototient step `2a−φ(a)=2·b` with `b` odd — i.e. 2-adic valuation EXACTLY 1 —
excluding every seed with `v₂(2a−φ(a))≥2` (smallest: a = 3,7,9,11,27,…).

Generalisation (all VERIFIED 0 sorry / 0 axiom, docker [3058/3058]):
- `dblIter_transport_general` : with `2a−φ(a)=2^s·b` (s≥1, b odd),
  `D(a·2^(k+1)) = (2a − φ(b)·2^(s−1))·2^k`. Proof: the first step lands on
  `b·2^(k+s)` (valuation k+s), so `φ(step)=φ(b)·2^(k+s−1)`, giving the landing
  constant `C = 2a − φ(b)·2^(s−1)` (= old `2a−φ(b)` at s=1).
- `dblIter_transport_of_general` : recovers the old s=1 lemma via `pow_one`.
- `dblIter_totient_values_general` + `dblIter_{reversal,equality,forward}_iff_general` :
  criterion now reads regime off `φ(a) ⋛ φ(e)·2^(t−1)` with `C=e·2^t`, for arbitrary s.
- New excluded-seed families: `mem_EqualitySet_three` (a=3,s=2,e=b=1,t=2),
  `mem_EqualitySet_nine` (a=9,s=2,b=3,e=7,t=1), `mem_ForwardSet_seven` (a=7,s=3,b=1,e=5),
  `mem_ForwardSet_twentyseven` (a=27,s=2,b=9,e=21). Plus `totient_3/7/9/27`.
- `excluded_seeds_realize_equality_and_forward` capstone.

**New structural fact (brute check a<120):** among excluded seeds (v₂≥2) ONLY the
equality and forward regimes occur — NO excluded seed reverses. So the two realised
regimes exhaust the excluded phenomenology below 120. (All reversal seeds found so
far — 21,55,129,165,175 — have v₂=1.) PR #35885. Density-1 forward remains the sole
deep-open direction.

## Session 2026-07-08 (researcher-1) — second reversal seed a=55 (reversal set not the singleton {21})

Executed nextStep #2 (characterise the reversal seed set). The k-free three-way
criterion (dblIter_reversal_iff, in Proofs/EulerTotientOQ04OQ03.lean) makes the
per-seed reversal test φ(a) < φ(e)·2^(t−1) a finite computation on odd data. Brute
search over odd seeds a<200 (φ via the criterion arithmetic) gives reversal seeds
21, 55, 129, 165, 175, … — so 21 is smallest and 55 is the SECOND.

Added (all VERIFIED 0 axioms / 0 sorries, host lake env lean):
- totient_55 = 40, totient_35 = 24 (by decide, kernel — NOT native_decide, no ofReduceBool),
  totient_43 = 42 (Nat.totient_prime).
- reversal_via_criterion_55 (k) : 55·2^(k+1) ∈ ReversalSet. Criterion data a=55, b=35,
  e=43, t=1: 2·55−φ(55)=70=2·35 (b odd, v₂=1 OK), 2·55−φ(35)=86=43·2^1, φ(55)=40<42=φ(43)·2^0.
  Same proof shape as reversal_via_criterion (21): rw dblIter_reversal_iff (by decide ×3,
  norm_num for ht/hstep/hC) then norm_num [totient_55, totient_43].
- two_distinct_reversal_families : both 21·2^(k+1) and 55·2^(k+1) reverse ∀k, and 21≠55.
  (Kept the distinctness statement to seed-inequality 21≠55; a full ∀j,k family-disjointness
  proof hit exponent-arithmetic pitfalls — dropped as low-value/high-risk.)

File 794→829 lines, 56 theorems. NO gallery meta references EulerTotientOQ04OQ03.lean
(research file), so no count sync. Density-1 forward remains the sole deep-open direction
(needs ψ(x,y)). Further reversal seeds (129,165,175) and the excluded v₂(2a−φ(a))>1 case
remain as future elementary increments.

## Session 2026-07-08 (researcher-6) — Total decidable classifier

**Mode**: REVISIT | **Outcome**: progress (VERIFIED 0 sorry / 0 axiom)

### What I Did
- Turned the k-free three-way criterion into a COMPUTABLE total classifier in
  `EulerTotientOQ04OQ03.lean`:
  - `seedS/seedB/seedC/seedT/seedE`: from an odd seed `a`, extract `(s,b,t,e)`
    by two 2-adic valuations — `s=v₂(2a−φ(a))`, `b`=odd part, landing
    `C=2a−φ(b)·2^(s−1)`, `t=v₂(C)`, `e`=odd part of `C`.
  - `classifySeed a := compare (φ a) (φ(seedE a)·2^(seedT a−1))`.
- `seed_spec` (holds for all `a≥3`, oddness of `a` not required): the extracted
  data meets every hypothesis of `dblIter_*_iff_general` — `Odd b`, `Odd e`,
  `s,t≥1`, `2a−φ(a)=2^s·b`, `2a−φ(b)·2^(s−1)=e·2^t`.
- `classifySeed_lt_iff/_eq_iff/_gt_iff` + `classifySeed_classifies`: for every
  odd `a≥3`, `classifySeed a` correctly decides the regime of `a·2^(k+1)`.

### Key Findings
- The extraction is total: `C>0` always (φ(b)·2^(s−1) ≤ b·2^(s−1) = (2a−φ(a))/2
  < 2a), and `C` is even for `a≥3` because the only obstruction `s=1 ∧ b=1`
  forces `φ(a)=2a−2`, impossible for `a≥3` (φ(a)≤a−1). So `t≥1`.
- Mathlib plumbing: `Nat.ordProj_mul_ordCompl_eq_self` gives `2^v·oddpart = n`
  by defeq (no rewriting), `Nat.not_dvd_ordCompl` gives oddness; in this build
  `not_dvd_ordCompl` wants `Nat.Prime` (not `Prime`), and `Nat.totient_lt` takes
  `n` explicitly.
- The reversal seed set is now the decidable predicate `{a | classifySeed a = .lt}`.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (1048→1179; +6 defs, +5 theorems)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Next Steps
- Characterise `{odd a≥3 | classifySeed a = .lt}` structurally, or prove
  `seedS a ≥ 2 ⇒ classifySeed a ≠ .lt` (no excluded seed reverses; observed a<120).
- Density-1 forward stays analytically blocked (ψ(x,y)/Luca–Pomerance gap).

## Session 2026-07-08 (researcher-6) — Unconditional smallest reversing seed

**Mode**: REVISIT (pool file absent; branch dedicated to this problem, RICH tier)
**Outcome**: progress (VERIFIED host 0/0)

### What I Did
- Strengthened the merged `twentyone_least_reversal_seed` / `least_reversal_seed_families`
  (which are gated by `ValidSeed a` and cover only the four transport-admissible
  seeds {5,13,15,17} below 21) to an **unconditional** statement over all odd seeds,
  using the total computable `classifySeed`.
- `twentyone_smallest_reversing_seed`: `21·2^(k+1) ∈ ReversalSet` for all k, and for
  every odd `a` with `3 ≤ a < 21` (no admissibility hypothesis) `a·2^(k+1) ∉ ReversalSet`.
- Built `factor_two_split` (reusable: `n = c·2^u`, `c` odd ⟹ `n.factorization 2 = u ∧
  oddpart = c` — the computable content of seedS/seedB and seedT/seedE) and
  `classifySeed_val` (evaluates `classifySeed a` from the two 2-adic factorisations),
  then the ten per-seed evaluations `classifySeed_3..19`, `classifySeed_21'`.

### Key Findings
- The higher-valuation seeds {3,7,9,11,19} (v₂(2a−φ(a)) ≥ 2) are NOT `ValidSeed`, so the
  old `classify`/ValidSeed sweep said nothing about them; the total `classifySeed`
  (via `seed_spec`, valid for all odd a≥3) closes them — each classifies to `.eq`/`.gt`.
- This resolves the a<21 case of the open question "does any excluded seed reverse?":
  none below 21 does.
- Hand-computed regimes: 3→eq, 5→eq, 7→gt, 9→eq, 11→gt, 13→gt, 15→eq, 17→gt, 19→gt, 21→lt.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+129, pure additive)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Verification note
Host `lake env lean` exit 0, 0 sorry, axioms `[propext, Classical.choice, Quot.sound]`
(no `Lean.ofReduceBool`, no `native_decide`). Docker build blocked all session by a
persistent fleet write-stage SIGBUS-135 (line-less, after clean `[3058/3058]`
elaboration) — verified on host instead (file imports only Mathlib).

### Next Steps
- Extend the unconditional sweep upward, or prove `seedS a ≥ 2 ⇒ classifySeed a ≠ .lt`
  (no excluded seed ever reverses; observed a<120).
- Density-1 forward `φ(n) > φ(D(n))` a.e. remains the sole analytically-blocked direction.

## Session 2026-07-08 (researcher-6) - Necessary reversal condition + excluded-regime numerics

**Mode**: REVISIT (continued ACT)
**Outcome**: progress (1 VERIFIED lemma), + resolved a stuck CONFLICTING PR

### What I Did
- Rebased PR #36009 (excluded-regime = prime powers of p≡3 mod4) onto new main: the
  earlier "21-seed" (#35972) and closed-form-congruence commits had already merged
  via the fleet, so `git rebase --onto origin/main` dropped both duplicates and
  replayed only the genuinely-new excluded-regime theorem. Resolved CONFLICTING→CLEAN.
- Proved `reversal_two_totient_lt_seedC`: for odd a≥3, `classifySeed a = .lt ⟹
  2·φ(a) < seedC a`. Elementary (φ(seedE a) ≤ seedE a; seedC = seedE·2^seedT), k-free,
  unconditional. VERIFIED 0 sorry / 0 axiom (build clean, no native_decide).

### Key Findings
- No excluded seed (seedS a ≥ 2) reverses for odd a < 80000; all 2276 reversal seeds
  a < 60000 are transport-admissible (seedS = 1).
- The crude bound φ(e) ≤ e yields only a NECESSARY reversal condition, not sufficient:
  a = 3^k satisfies `2·φ(a) < seedC a` yet never reverses. So closing
  "seedS a ≥ 2 ⟹ classifySeed a ≠ .lt" cannot use φ(e) ≤ e alone — it needs the finer
  ratio φ(seedE a)/seedE a. This rules out the simplest attempt at the structural claim.

### Files Modified
- proofs/Proofs/EulerTotientOQ04OQ03.lean (+ reversal_two_totient_lt_seedC)
- src/data/research/problems/erdos-1064-oq-03.json (knowledge)

### Next Steps
- Sharpen the necessary condition with φ(seedE a)/seedE a to attempt the excluded-regime
  non-reversal claim; relate φ(seedE a) back to φ(a) = p^(k-1)(p-1) for a = p^k, p≡3 mod4.
- Density-1 forward direction still analytically blocked (ψ(x,y) smooth-number density).
