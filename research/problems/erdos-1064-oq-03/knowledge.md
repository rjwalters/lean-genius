
## Session 2026-07-08 (researcher-6) — MILESTONE: excluded regime fully closed (structural conjecture proven)

**Mode**: REVISIT (RICH tier; branch dedicated) | **Outcome**: progress (VERIFIED 0 sorry / 0 axiom, Docker `Built (5.6s)`, 3058 jobs; axioms propext/Classical.choice/Quot.sound; no native_decide)

### What I Did
- Extended the general non-reversal engine `classifySeed_ne_lt_of_excess_bound`
  from its two prior special applications (the tower `3^k`; the primes `p≡3 mod4`
  at `k=1`) to their **common generalisation — every prime power `p^k` with
  `p≡3 mod4`, `k≥1`** (`classifySeed_prime_pow_three_mod_four_ne_lt`,
  `prime_pow_three_mod_four_family_not_reversal`).
- Recognised (via the file's existing `seedS_ge_two_iff_totient_mod_four` and
  `totient_mod_four_eq_two_iff_prime_pow_three_mod_four`) that the excluded seeds
  are **exactly** those prime powers, so the extension **closes the entire
  excluded regime**. Added the capstone theorems.

### Key Findings
- `a=p^(m+1)`: `a−φ(a)=p^m`, `2a−φ(a)=p^m·(p+1)`. Writing `p+1=w·2^S` (w odd,
  `S=v₂(p+1)≥2` since `p≡3 mod4`) gives `seedS a=S`, `seedB a=p^m·w` (p^m ⟂ w
  because `w∣p+1`). The engine bound becomes `p^m ≤ φ(p^m)·φ(w)·2^(S−2)`.
- Split into two elementary facts: `p^m ≤ 2·φ(p^m)` (any prime; `2(p−1)≥p`) and
  `2 ≤ φ(w)·2^(S−2)`. The latter holds **iff `p>3`**: `S=2 ∧ w=1 ⟺ p+1=4 ⟺ p=3`,
  so `p≥7` forces `S≥3` (2^(S−2)≥2) or `w≥3` odd (φ(w)≥2). `p=3` → `3^k` tower.
- **Structural dichotomy now a THEOREM**: `excluded_seed_never_reverses`
  (`seedS a≥2 ⟹ classifySeed a≠.lt`), hence `reversal_seed_transport_admissible`
  (`classifySeed a=.lt ⟹ seedS a=1`) and `reversal_mem_implies_transport_regime`
  (`a·2^(k+1)∈ReversalSet ⟹ seedS a=1`). Every reversal lives strictly inside the
  transport-admissible regime `seedS a=1` — the conjecture prior sessions circled.

### New declarations (all VERIFIED 0/0)
- `prime_pow_le_two_totient` — `p^m ≤ 2·φ(p^m)` for any prime `p` (reusable)
- `classifySeed_prime_pow_three_mod_four_ne_lt`
- `prime_pow_three_mod_four_family_not_reversal`
- `excluded_seed_never_reverses`
- `reversal_seed_transport_admissible`
- `reversal_mem_implies_transport_regime`

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+~180)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Next Steps
- The elementary/structural side of OQ-03 is COMPLETE. The only open direction is
  the analytically-hard density-1 forward statement (ψ(x,y) smooth-number
  density / Luca–Pomerance) — a genuine Mathlib gap, not session-sized.
- Optional elementary follow-up: characterise WHICH transport-admissible seeds
  (`seedS a=1`) reverse, beyond the least element `a=21`.

## Session 2026-07-08 (researcher-6) — general non-reversal ENGINE + all primes p≡3 mod4

**Mode**: REVISIT (RICH tier; branch dedicated) | **Outcome**: progress (VERIFIED 0 sorry / 0 axiom, Docker v4.26.0 `Build completed successfully`, 3058 jobs)

### What I Did
- Isolated the *mechanism* behind `3^k`-non-reversal into a **reusable engine**
  and applied it to a strictly larger class than the single-prime tower.
- `classifySeed_ne_lt_of_excess_bound (ha3, hs2 : 2 ≤ seedS a, hbound)`:
  for an excluded seed, `classifySeed a ≠ .lt` **whenever**
  `a − φ(a) ≤ φ(seedB a)·2^(seedS a − 2)`. This single arithmetic inequality is
  the only seed-specific input needed.
- `classifySeed_prime_three_mod_four_ne_lt (hp, hp3 : p%4=3)`: every prime
  `p ≡ 3 mod 4` never reverses (`a − φ(a) = p − (p−1) = 1` makes the bound trivial).
- `prime_three_mod_four_family_not_reversal`: `∀ prime p≡3 mod4, ∀ k, p·2^(k+1) ∉ ReversalSet`.

### Key Findings / proof recipe
- The classifier compares `φ(a)` with `φ(e)·2^(t−1)` where `seedC a = e·2^t`
  (`e = seedE a`, `t = seedT a`). Since `φ(e) ≤ e`,
  `φ(e)·2^(t−1) ≤ e·2^(t−1) = seedC a / 2 = a − φ(seedB a)·2^(seedS a − 2)`.
  So the family fails to reverse as soon as `a − φ(a) ≤ φ(seedB a)·2^(seedS a − 2)`.
- Lean plumbing: from `seed_spec` get `hCeq : 2a − φ(seedB a)·2^(s−1) = e·2^t`;
  split `2^t = 2·2^(t−1)` and `2^(s−1) = 2·2^(s−2)` with `conv_lhs`/`pow_succ`
  (NOT bare `rw` — that also hits `t` inside `t−1`), then `omega` halves the
  identity to `a = e·2^(t−1) + φ(seedB a)·2^(s−2)` (nat-sub resolved via `e·2^t ≠ 0`).
  Final compare closed by `simp only [classifySeed]; rw [ne_eq, compare_lt_iff_lt]; omega`.
- This class {3,7,11,19,23,31,…} ⊋ {3^k}: the primes ≡ 3 mod 4 are a genuinely
  new infinite non-reversing family, all discharged by one engine call each.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+~75 lines, 3 theorems)

### Next Steps
- Extend the engine to the full prime power `a = p^k` (p ≡ 3 mod 4): reduces to
  `φ(seedB a)·2^(seedS a − 2) ≥ p^(k−1)` where `seedB(p^k) = p^(k−1)·oddpart(p+1)`,
  `seedS = v₂(p+1)`. For `p ≥ 7` the bound holds since `φ(b)·2^(s−2) ≥ 2`; only
  `p = 3` needs the separate `three_pow` computation. Completing it fully proves
  the structural claim **no excluded seed reverses**.
- Density-1 forward remains the sole analytically-blocked direction (ψ(x,y)).

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

## Session 2026-07-08 (researcher-3) — prime-triple reversal family collapses to {21,55}

**Mode**: REVISIT (RICH tier) | **Outcome**: progress (VERIFIED 0 sorry / 0 axiom, Docker `Built (7.4s)`, 3058 jobs; axioms propext/Classical.choice/Quot.sound; no native_decide)

### What I Did
- Observed the two known reversal seeds `21 = 3·7`, `55 = 5·11` are exactly
  `a = p·(2p+1)` for the two smallest Sophie-Germain primes `p = 3, 5` (with the
  extra property that `p+2` is also prime — a "prime triple" `(p, p+2, 2p+1)`).
- Proved this natural infinite candidate family does NOT furnish infinitely many
  reversal seeds:
  - `prime_triple_family_not_reversal`: for `p ≥ 7` with `p, p+2, 2p+1` all
    prime, `p(2p+1)·2^(k+1) ∉ ReversalSet`.
  - `prime_triple_reversal_iff`: the family reverses iff `p ∈ {3, 5}`.

### Key Findings / proof recipe
- For `a = p(2p+1)` (p, 2p+1 prime): `φ(a) = 2p(p−1)`, first step
  `2a−φ(a) = 2p(p+2)` (v₂ = 1, transport-admissible, `b = p(p+2)`),
  `φ(b) = p²−1`, landing `C = 2a−φ(b) = 3p²+2p+1 = 2e`, `t = 1`.
- Reversal ⟺ `φ(a) < φ(e)` (via `dblIter_reversal_iff`, `t = 1`). The uniform
  non-reversal bound uses ONLY `φ(e) ≤ e−1` (no factorisation of the wildly
  varying `e` needed!): `φ(e) ≤ e−1 = (3p²+2p−1)/2 ≤ 2p(p−1) = φ(a)` ⟺
  `p²−6p+1 ≥ 0` ⟺ `p ≥ 6`. Below the threshold `3+2√2 ≈ 5.83` only `p = 3, 5`.
- Lean plumbing: substitute `p = 2j+1` (j ≥ 3) to kill all nat-subtraction in
  the polynomial identities; `φ(a)`, `φ(b)` via `Nat.totient_mul` +
  `Nat.totient_prime` with the two `show (2j+1)-1 = 2j` rewrites; `hstep`/`hC`
  each proven by a `ring` additive identity fed to `omega` (which abstracts the
  nonlinear products as atoms and discharges the nat subtraction); final sign
  refutation by `Nat.totient_lt` + two `nlinarith [hj3]` + `omega`.
- `prime_triple_reversal_iff` forward: an odd prime with `p+2, 2p+1` prime and
  `p ∉ {3,5}` is forced `≥ 7` by `interval_cases p <;> revert … <;> decide`.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+123 lines, 2 theorems)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Next Steps
- Elementary terminus stands: the only open direction remains the analytically
  hard density-1 forward statement (ψ(x,y) smooth-number density / Luca–Pomerance)
  — a genuine Mathlib gap, not session-sized. Reversal-seed-set infinitude, if
  true, is essentially the hard direction (this session shows the natural
  candidate family degenerates). Do not reclaim for elementary work.

## Session 2026-07-09 (researcher-2) — strict-gt classifier engine + prime forward-regime reduction

**Mode**: BUILD/ACT (RICH terminus). **Outcome**: progress, VERIFIED 0 sorry / 0 axiom
(Docker `Build succeeded`, 3058 jobs, attempt 2; attempt 1 = fleet SIGBUS-135). Pre-existing
`mul_le_mul_left'` deprecation warning at 2312 is not my code.

### Gap addressed
The file had `classifySeed_ne_lt_of_excess_bound` (a **non-strict** engine ruling out `.lt`
for excluded seeds), but **no `.gt` engine** — so the excluded regime was only known to avoid
reversal, not shown to strictly increase. The trichotomy `lt/eq/gt` on excluded seeds was
incomplete: `3^k` is `.eq` (classifySeed_3/9), the primes `7,11,13,17,19` are `.gt` (decide),
but there was no general `.gt` theorem.

### Added (2 theorems)
- `classifySeed_gt_of_excess_bound (ha3) (hs2 : 2 ≤ seedS a) (hbound) (he2 : 2 ≤ seedE a) :
  classifySeed a = .gt`. Exact `.gt` companion of the ne_lt engine, same proof skeleton
  (halve the 2-power identity `a = seedE·2^(t-1) + φ(seedB)·2^(s-2)`, get `seedE·2^(t-1) ≤ φ(a)`
  from the excess bound), plus ONE strict step: `φ(seedE a) < seedE a` (`Nat.totient_lt`, valid
  iff `seedE a ≥ 2`) → `φ(seedE)·2^(t-1) < seedE·2^(t-1) ≤ φ(a)` via `mul_lt_mul_of_pos_right`,
  so `compare φ(a) (φ(seedE)·2^(t-1)) = .gt`. **Completes the excluded-regime trichotomy as a
  function of a single invariant: `seedE a = 1 ⟹ .eq`, `seedE a ≥ 2 ⟹ .gt`.**
- `classifySeed_prime_three_mod_four_gt_of_seedE (hp) (hp3) (he2 : 2 ≤ seedE p) :
  classifySeed p = .gt`. For primes `p≡3 mod4` the excess `p−φ(p)=1` makes the bound automatic
  (reused the derivation from `classifySeed_prime_three_mod_four_ne_lt`), so `.gt ⇔ seedE p ≥ 2`.
  `p=3` is excluded automatically (`seedE 3 = 1`, so `he2` is false ⟹ vacuous).

### Precise remaining obstruction (isolated this session)
Closing "every excluded prime `p ≡ 3 mod4`, `p ≥ 7` is strictly `.gt`" now reduces to the
SINGLE arithmetic fact **`seedE p ≥ 2`** (odd part of the second landing constant
`C = 2p − φ(w)·2^(S−1)`, `p+1 = w·2^S`, is `> 1`). Verified by hand:
- `w = 1` (Mersenne-type, `p = 2^S − 1`): `C = 3·2^(S−1) − 2 = 2·(3·2^(S−2) − 1)`, odd part
  `3·2^(S−2) − 1 ≥ 5` for `S ≥ 3` — so `seedE ≥ 5`.
- crude range bound `(3p−1)/2 ≤ C ≤ 2p` does NOT close `w ≥ 3` (a power of 2 can sit in range).
A clean general `seedE p ≥ 2` proof needs the exact odd part of `C` and is the natural next
target (would upgrade `classifySeed_prime_three_mod_four_ne_lt` to a strict `.gt` family, and
then `prime_pow_three_mod_four` analogously). `seedE` is defined via `factorization`, so this is
non-trivial plumbing, not a one-liner.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+2 theorems, ~70 lines)
- `research/problems/erdos-1064-oq-03/knowledge.md`, problem json

### Next Steps (unchanged terminus + this session's target)
- **New concrete target**: prove `seedE p ≥ 2` for primes `p≡3 mod4`, `p ≥ 7` → strict `.gt`
  family via `classifySeed_prime_three_mod_four_gt_of_seedE`. Session-sized IF the odd-part
  bound can be extracted; the engine is now in place waiting for it.
- Density-1 forward direction (ψ(x,y) smooth-number density / Luca–Pomerance) still the hard
  analytic terminus — genuine Mathlib gap, not session-sized. Do not reclaim for elementary work
  beyond the seedE≥2 target above.

## Session 2026-07-09 (researcher-1) — reversal (.lt) engine on transport-admissible regime

**Mode**: REVISIT (RICH) | **Outcome**: progress (elab-clean [3058/3058], olean-write blocked by env SIGBUS-135/139 across 6 builds — UNVERIFIED; 0 sorry / 0 axiom)

### What I Did
- Added the missing `.lt`-forcing engine for the transport-admissible regime
  `seedS a = 1` (where `reversal_seed_transport_admissible` proves every reversal
  lives). The excluded regime had `classifySeed_ne_lt_of_excess_bound` and
  `classifySeed_gt_of_excess_bound` but nothing forcing reversal.
- `classifySeed_lt_iff_of_seedS_one_seedE_prime`: for odd `a≥3` with `seedS a=1`
  and `seedE a` PRIME, `classifySeed a = .lt ↔ φ(seedB a)+2^{seedT a} < 2(a−φ(a))`.
  An EXACT criterion — formalizes the empirical "reversals cluster on prime
  landings" observation.
- `prime_landing_family_reversal`: packages it into `a·2^(k+1) ∈ ReversalSet ∀k`.

### Key Findings
- Mechanism (`seedS a=1`): `2a−φ(a)=2·seedB a`, `2a−φ(seedB a)=seedE a·2^{seedT a}`.
  With `e=seedE a` prime, `φ(e)=e−1`, and `e·2^{t−1}=a−φ(seedB a)/2`; doubling
  collapses `φ(a)<φ(e)·2^{t−1}` to `φ(seedB a)+2^{seedT a} < 2(a−φ(a))`.
- Numerically verified as iff: 21(b=15,e=17),55(b=35,e=43),129(b=87,e=101),
  175(b=115,e=131) all satisfy criterion (→.lt); Sophie-Germain equality seeds
  15,33 (also prime-landing) fail it (→.eq).
- Honest limit: 165 (seedB=125, seedE=115=5·23 composite) reverses but is
  OUTSIDE the engine. Prime-landing restriction is genuine, not cosmetic.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+~80, 2 theorems)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Next Steps
- Full `seedS=1` reversal characterization (covering composite landings like 165)
  needs a lower bound on `φ(seedE a)/seedE a` beyond the prime case.
- The genuinely-open direction remains the density-1 forward `ψ(x,y)` statement.

## Session 2026-07-09 (researcher-3) — parametric REVERSAL family (completes the trichotomy)

**Mode**: REVISIT (RICH tier) | **Outcome**: progress (full elaboration clean
`[3058/3058]`, olean-write env-blocked SIGBUS-135 across 4 runs → UNVERIFIED;
0 sorry / 0 axiom).

### What I Did
- Added the **parametric reversal family** that was the missing third leg beside
  the Sophie–Germain equality family (`3q`) and the `5q` forward family. All prior
  reversal knowledge was either the *isolated* seeds `21,55,129,175` or the
  criterion `classifySeed_lt_iff_of_seedS_one_seedE_prime`; there was no closed
  infinite reversal family stated as a single parametric theorem.
- `mem_ReversalSet_primeTriple (hm : 1 ≤ m)(4m+1 prime)(6m+1 prime)(14m+3 prime)`:
  `(18m+3)·2^(k+1) ∈ ReversalSet` for all `k`.
- `classifySeed_primeTriple_lt`: the seed `18m+3` is classified `.lt`.

### Mechanism (collapse of `dblIter_reversal_iff_general`)
- `a = 18m+3 = 3·(6m+1)`, `φ(a) = 12m`.
- `2a − φ(a) = 24m+6 = 2·(12m+3)` ⟹ `s=1`, `b = 12m+3 = 3·(4m+1)`, `φ(b) = 8m`.
- landing `C = 2a − φ(b) = 28m+6 = (14m+3)·2¹` ⟹ `t=1`, `e = 14m+3`.
- reversal ⇔ `φ(a) < φ(e)·2^{t−1} = 14m+2`, i.e. `12m < 14m+2` — **automatic**.
- All three primality hypotheses load-bearing: `6m+1`,`4m+1` give the clean
  totients; `14m+3` prime is essential for the lower bound `φ(e)=14m+2>12m`
  (composite landing could drop `φ(e)` below `12m` and kill the reversal).

### Members / honesty
- `m=1 → 21` (`5,7,17` prime), `m=7 → 129` (`29,43,101`), `m=25 → 453`
  (`101,151,353`). Unifies the docstring's isolated `21` and `129`.
- Honestly bounded: the `5q`-type reversal seeds `55,175` are NOT captured (their
  seed is `5q` not `3q`), so this is one sub-family, not all reversals.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+~85 lines, 2 theorems)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Next Steps
- Structural/elementary side stays COMPLETE. Only open direction is the
  analytically-hard density-1 forward ψ(x,y) smooth-number statement (Mathlib gap).
- Optional: an analogous `5q` parametric reversal family capturing `55,175`.

## Session 2026-07-09 (researcher-5) — resolves the "optional 5q family" next-step (NEGATIVE) + concrete seed 55

**Mode**: REVISIT (RICH tier) | **Outcome**: the requested `5q` reversal family does
NOT exist as a clean infinite family — proved the honest negative, plus catalogued seed
55 concretely. 0 sorry / 0 axiom. UNVERIFIED (docker image build still dies at containerd
`meta.db` input/output error #35184).

### The 5q analogue is finite, not infinite (the honest finding)
Mirroring the `3q` family `a = 3·(6m+1)` (→ `18m+3`), the natural `5·q` analogue is
`a = 5·(5m+1) = 25m+5`, `b = 5·(3m+1) = 15m+5`, landing `e = 19m+5`, requiring `5m+1`,
`3m+1`, `19m+5` all prime. The general criterion `dblIter_reversal_iff_general` collapses
to the reversal condition `φ(a) = 20m < φ(e) = 19m+4`, i.e. **`m < 4`** — a *bounded*
window, UNLIKE the `3q` family whose margin `14m+2 − 12m = 2m+2` grows without bound. Since
`a = 25m+5` is odd only for even `m`, the sole member is `m = 2`, the seed **`55`** itself.
So `55` is genuinely isolated as a `5·(5m+1)` reversal, not the head of an infinite family.
(`175 = 5²·7` has yet another shape — `a = 25·7`, `b = 5·23`, `e = 131` — not `5·(5m+1)`.)

### Added (`proofs/Proofs/EulerTotientOQ04OQ03.lean`, +2 theorems, ~35 lines)
- `classifySeed_55 : classifySeed 55 = Ordering.lt` — via `classifySeed_val (s:=1)(b:=35)
  (t:=1)(e:=43)`; `2·55−φ(55)=70=35·2¹`, `2·55−φ(35)=86=43·2¹`, `compare φ(55)=40
  φ(43)=42 = lt`. Reuses pre-existing helpers `totient_55/35/43`; same idiom as
  `classifySeed_21'`.
- `mem_ReversalSet_55 (k) : 55·2^(k+1) ∈ ReversalSet` — `.mpr classifySeed_55` through
  `classifySeed_lt_iff`. First concrete reversal seed catalogued OUTSIDE the `3q` family,
  confirming reversals are not confined to `18m+3`.

The `5q` next-step is now RESOLVED (negative — no infinite family) and should be struck
from future to-dos. Only frontier left is the analytic density-1 forward ψ(x,y) statement.
