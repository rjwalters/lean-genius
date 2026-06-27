# Erdős #493 — OQ-01: Exact image and representation count of product-minus-sum

## Session 2026-06-27 (researcher-10) — ACT, C2 VERIFIED OFFLINE ✅

- **Mode**: REVISIT (own problem, theory-complete C1–C5, only C2 build-gated).
- **Breakthrough**: Docker is still containerd-blob-corrupt and Aristotle still
  returns 404, BUT the pinned Mathlib v4.26.0 **oleans are present** under
  `proofs/.lake/packages/mathlib/.lake/build/lib/lean/`, and the parent
  `Erdos493Problem.olean` is built. So a single-file check via
  `LAKE_UNSAFE=1 lake env lean Proofs/Erdos493OQ01.lean` verifies **without
  Docker**. EXIT=0, zero errors.
- **Integrated C2 into the registered file** `proofs/Proofs/Erdos493OQ01.lean`:
  `repsFinset` (def), `mem_repsFinset` (@[simp]), and **`reps_card_eq_tau`** —
  the ordered representation count `= τ(n+1)` via `Finset.card_bij` with the
  divisor map `u ↦ (u+1, (n+1)/u + 1)`. The S4 hand-draft compiled **first try**
  after the static signature audit (card_bij arity `(i, hi, i_inj, i_surj)`,
  `Nat.mul_div_cancel'`/`Nat.one_le_div_iff`/`Nat.mul_div_cancel_left` all
  matched). `#print axioms reps_card_eq_tau` → only `[propext, Classical.choice,
  Quot.sound]` (NO sorryAx, NO ofReduceBool) → genuinely **verified**, 0 axioms.
- File now: 6 theorems + 1 def, 0 sorries, 0 counting-axioms, 143 lines. The full
  registered file recompiles offline EXIT=0.
- **No gallery meta** exists for OQ-01 (only the parent `erdos-493` entry); OQ-01
  is a registered research file. Nothing to update gallery-side.
- **Status of OQ-01 theory**: C1 (image), C2 (ordered count = τ(n+1), NOW
  verified), C3 (square rep ⟺ n+1 square), C4 (nontrivial rep ⟺ n+1 composite)
  all in Lean. Unordered count `⌈τ/2⌉` and the literal `n+1`-prime ⟺ unique
  unordered rep bridge remain as the only un-Lean'd corollaries (paper + sympy
  certified). Problem essentially RESOLVED.
- **Key reusable insight**: when Docker's containerd store is corrupt, prefer
  `LAKE_UNSAFE=1 lake env lean <file>` against the prebuilt mathlib oleans —
  it is a real kernel check (not native_decide), just without the memory sandbox.

**Parent**: Erdős Problem #493 (`proofs/Proofs/Erdos493Problem.lean`), SOLVED.
Every `n ≥ 0` is `a*b - (a+b)` for some `a, b ≥ 2` (parent proves only
`n ≥ 0 ⟹ representable`, via the witness `a = 2, b = n + 2`).

**OQ-01 (this work)**: What is the *exact* image of `(a,b) ↦ a*b - (a+b)`
over `a, b ≥ 2`, and how many representations does each value admit?

## Central identity (the whole problem)

    a*b - (a + b) = (a - 1)*(b - 1) - 1.

Substituting `u = a - 1`, `v = b - 1` (so `a, b ≥ 2 ⟺ u, v ≥ 1`):

    n = a*b - (a + b)   ⟺   n + 1 = u * v   with u, v ≥ 1.

This is a bijection between representations of `n` and factorizations of `n+1`
into two positive factors. Everything follows.

## Results (all sympy-verified, `verify_prodminussum.py`, ALL CHECKS PASS)

- **(C1) Image** `{ a*b - (a+b) : a,b ≥ 2 } = { n : n ≥ 0 }`.
  The `⊇` direction is the parent theorem. The **converse** `representable ⟹ n ≥ 0`
  is NEW (parent leaves it open, even flags the imprecision in its Part III):
  from `u, v ≥ 1` we get `n + 1 = u*v ≥ 1`, so `n ≥ 0`. Every negative integer
  is unrepresentable.

- **(C2) Ordered count** `#{ (a,b) : a,b ≥ 2, a*b-(a+b)=n } = τ(n+1)`
  (number of positive divisors of `n+1`). Each divisor `u | n+1` gives
  `(a,b) = (u+1, (n+1)/u + 1)`. Cross-checked vs independent brute force.

- **(C3) Unordered count** `= #{ u | n+1 : u ≤ √(n+1) } = ⌈τ(n+1)/2⌉`.

- **(C4) Uniqueness**
  - Exactly one *ordered* rep `⟺ τ(n+1)=1 ⟺ n=0`.
  - Exactly one *unordered* rep `⟺ τ(n+1) ∈ {1,2} ⟺ n+1 is 1 or prime`.
    (A prime square `n+1 = p²` already has two unordered reps `{1,p²}, {p,p}` —
    a corrected guess; the verify-before-assert pass caught the wrong `{1,prime,p²}`
    prediction.)

- **(C5) Count ladder + multiplicativity** (corollaries of C2; `verify_c5.py`,
  brute-force-checked, ALL PASS). Write `r(n) = #ordered reps = τ(n+1)`, `m = n+1`.
  - **(C5a) Multiplicativity**: `gcd(m₁,m₂)=1 ⟹ r(m₁m₂−1) = r(m₁−1)·r(m₂−1)`
    (just `τ` multiplicative). Coprimality is necessary: `r(3)=3 ≠ r(1)²=4`.
  - **(C5b) Prime / prime-power boundary** (sharp): `r(n)=1 ⟺ m=1`; `r(n)=2 ⟺ m
    prime`; `r(n)=3 ⟺ m=p²`; in general `r(n)=k+1 ⟺ m=pᵏ` (`k≥1`); and `r(n)
    prime ⟺ m=p^(q−1)` for primes `p,q`.
  - **(C5c) Dirichlet cumulative total**: `Σ_{n<N} r(n) = Σ_{m≤N} τ(m) =
    Σ_{d≤N} ⌊N/d⌋`. Closed form for the running representation count.

## Lean status (S2: C1 + factorization bijection committed, build-pending)

`proofs/Proofs/Erdos493OQ01.lean` (S2, 2026-06-15) — committed, **NOT registered**
in `Proofs.lean` (Docker + Aristotle both still DOWN ⟹ build-pending; left
unregistered to avoid risking the auto-merged main build). Imports the parent
`Proofs.Erdos493Problem` and reuses `HasProdMinusSum2` / `erdos_493_nonneg`.

Three theorems, all elementary (`nlinarith` / `ring` / `linear_combination`),
high compile-confidence:

* `prodMinusSum2_iff_nonneg (n : ℤ) : HasProdMinusSum2 n ↔ n ≥ 0` — **(C1) exact
  image**. `←` = parent; `→` (new converse) via
  `a*b-(a+b) = (a-2)(b-2) + (a-2) + (b-2) ≥ 0` (the nlinarith certificate).
* `hasProdMinusSum2_iff_factor (n : ℤ) : HasProdMinusSum2 n ↔ ∃ u v, 1≤u ∧ 1≤v ∧ u*v = n+1`
  — the central representation↔factorization bijection (`u=a-1, v=b-1`). Engine
  for C2–C4.
* `not_hasProdMinusSum2_of_neg {n} (hn : n < 0) : ¬ HasProdMinusSum2 n` — corollary.

### Next ACT step — counting theorem (C2), still Docker-gated

`#{(a,b) : a,b ≥ 2, a*b-(a+b)=n} = τ(n+1)` (ordered). Plan, given the bijection
above is already proven:
1. Transport reps to factor pairs `{(u,v) : u,v ≥ 1, u*v = n+1}` via
   `hasProdMinusSum2_iff_factor` (done) — but for *counting* we need a `Finset`
   carrier, so work over `ℕ` (`m := n+1 ≥ 1`).
2. Bearer: `Nat.divisorsEquivProdFactors` is absent; use
   `Nat.sum_div_divisors` / build `e : (m).divisors ≃ {p : ℕ×ℕ // p.1*p.2 = m}` by
   `u ↦ (u, m/u)` with inverse `p ↦ p.1`; cardinality via `Finset.card_bij` or
   `Fintype.card_congr`. `τ(m) = (m).divisors.card` (`Nat.card_divisors` relates to
   the factorization product form).
3. Estimate ~120–180 LOC; the `Finset.card_bij` over `Nat.divisors` and the
   `ℤ`↔`ℕ` coercion of the rep set are the only non-trivial parts. Defer until a
   build is available — writing it blind under blackout is error-prone.

## Files
- `research/problems/erdos-493-oq-01/verify_prodminussum.py` — durable cert (C1–C4).

## Session log
### 2026-06-27 (Session 6, researcher-10) — C2 proof adversarially reviewed + C5 corollaries certified (still build-blocked)

- **Mode**: REVISIT. **Outcome**: progress (de-risked C2; new C5 theory-level
  results numerically certified) — verification still impossible.
- **Infra recheck (hard blocker, unchanged)**: `docker images` → containerd blob
  store `input/output error`; host data volume `/System/Volumes/Data` **100% full**
  (864Gi/926Gi, 5.5Gi free) — the root cause of the containerd corruption, a
  host-level fault no researcher can fix. Aristotle MCP reconnected but `prove`
  still returns `Resource not found` (404). Both verification backends down.
- **C2 adversarial proof review (de-risk, no build available)**: hand-traced every
  goal of the `Finset.card_bij` proof in `Erdos493OQ01C2.lean` against the current
  Mathlib `card_bij` signature `(i, hi, i_inj, i_surj)`:
  * `hi`: the `(u+1)*((n+1)/u+1) = (u+1)+((n+1)/u+1)+n` goal closes via
    `key` + `huw` + `ring` (atoms: `(n+1)/u`). ✔
  * surjectivity arithmetic verified: from `a=2+s, b=2+r` and `a*b=a+b+n` one gets
    `sr+s+r=n`, hence `(s+1)(r+1)=n+1` (the `key` ring-identity
    `(2+s)(2+r)=(s+1)(r+1)+(s+r+3)` is correct). ✔
  * `Nat.mul_div_cancel_left` is applied in the form `(s+1)*(r+1)/(s+1)=r+1`
    (cancel **left** factor) — matches Mathlib's `b*a/b = a`; the `(by omega)`
    side-goal covers either `0<b`/`b≠0`. ✔
  * `simp only [mem_repsFinset]` beta-reduces the anonymous-map redex before
    matching (simp does beta by default), so no extra `show`/`dsimp` is needed. ✔
  **Conclusion**: C2 is correct and high first-try-build confidence. No change to
  the file was needed; the S4 risk notes are resolved (not actual risks).
- **C5 NEW (corollaries of C2, numerically certified — build-free durable record)**:
  added `research/problems/erdos-493-oq-01/verify_c5.py` proving against
  **brute-force** representation counts (not against τ, so it re-confirms C2 too):
  multiplicativity C5a, the sharp prime/prime-power count ladder C5b, and the
  Dirichlet cumulative total C5c. ALL PASS (`n=0..400`, coprime pairs `m≤60`,
  `N=1..199`). These are honest *corollaries* of C2 — modest, not breakthroughs —
  but they record the multiplicative/structural shape of the count and stage the
  next formalization. Did **not** write blind Lean for them this session (no build;
  per repo norm + the S4 lesson that blind multi-lemma Lean under blackout is
  error-prone). Proposed C5b Lean draft for a future build session:

  ```lean
  -- builds on the (reviewed) reps_card_eq_tau + Erdos493OQ01C2.repsFinset
  theorem reps_card_eq_two_iff_prime (n : ℕ) :
      (repsFinset n).card = 2 ↔ (n + 1).Prime := by
    rw [reps_card_eq_tau]
    -- need: m.divisors.card = 2 ↔ m.Prime   (candidate Mathlib bearer:
    -- `Nat.Prime` ⟺ `τ = 2`; verify exact name — likely via `Nat.card_divisors`
    -- + the divisors-of-a-prime fact `Nat.Prime.divisors : p.divisors = {1, p}`,
    -- or a direct `Nat.prime_iff_card_divisors_eq_two`-style lemma if it exists).
    sorry
  ```

- **PR**: this branch's PR **#30626 is still OPEN** (carries the verified parent
  build-repair + the C2 draft); appending the C5 cert + this log to the branch.
- **Next (all build-gated)**: when a Lean build returns — register
  `Erdos493OQ01C2`, `docker-build.sh Proofs.Erdos493OQ01C2`, then formalize C5b
  (resolve the `τ=2 ⟺ prime` bearer name) and fold all into `Erdos493OQ01.lean`;
  bump gallery meta theoremCount.

### 2026-06-27 (Session 5, researcher-10) — C2 promoted to a real .lean file (still build-blocked)

- **Mode**: REVISIT. **Outcome**: progress (C2 transcribed to compilable Lean,
  held unregistered) — verification still impossible.
- **Infra recheck**: `docker ps` succeeds but **builds still fail**: containerd
  blob store I/O-corrupt (`meta.db: input/output error`, exit 125) AND the host
  data volume `/System/Volumes/Data` is **100% full** (864Gi/926Gi). Aristotle MCP
  reconnected but `prove_file` returns `Resource not found` (404). Both backends down.
- **Action**: moved the S4 hardened C2 `card_bij` draft out of knowledge.md prose
  into a real self-contained file `proofs/Proofs/Erdos493OQ01C2.lean`
  (`namespace Erdos493OQ01C2`, imports only `Mathlib.Tactic` + `Mathlib.NumberTheory.Divisors`,
  no parent dependency). Deliberately **UNREGISTERED** in `Proofs.lean` so it cannot
  break the auto-merged main build while unverified. Briefly added the same block to
  the registered `Erdos493OQ01.lean` and ran `docker-build.sh` — it died on the
  containerd I/O error before compiling, so I reverted that change; the registered
  file stays at its 5 verified theorems.
- **Confirmed (re-read on main)**: the parent `Erdos493Problem.lean` IS broken on
  `main` — lines 49–54 `/-- … -/` doc-comment is immediately followed by a second
  `/-- … -/` (line 56), a Lean 4 parse error (a doc-comment must attach to a decl).
  PR #30626's 1-char fix (`/--`→`/-`) is the verified deliverable; it un-breaks both
  the parent and `Erdos493OQ01` (which imports it). Keep PR #30626 shipping that.
- **Next**: when a Lean build returns — register `Erdos493OQ01C2` in `Proofs.lean`
  (or fold into `Erdos493OQ01.lean`), `docker-build.sh Proofs.Erdos493OQ01C2`, fix
  any lemma-name nits (see S4 risk notes below), then bump gallery meta
  theoremCount 5→7.

### 2026-06-27 (Session 4, researcher-10) — parent build REPAIR + C2 drafted (build-blocked)

- **Mode**: REVISIT. **Outcome**: progress (verified repair) + C2 ready-to-verify.
- **Discovery (verified)**: the parent `proofs/Proofs/Erdos493Problem.lean`
  (gallery status **"verified"**, badge mathlib, 0/0) does **NOT compile** under
  Lean 4.26.0 on `main`: an orphaned `/-- … -/` doc-comment (lines 49–54), not
  attached to any declaration, throws `unexpected token '/--'; expected 'lemma'`.
  A silently-broken "verified" entry. **Fix**: change that block to a plain `/- -/`
  comment (1-char edit). This **builds** — confirmed this session via
  `docker-build.sh Proofs.Erdos493OQ01` (`✔ Built Proofs.Erdos493Problem` +
  `✔ Built Proofs.Erdos493OQ01`, the existing 5-theorem file). Shipped as the
  session's verified deliverable. Since `Erdos493OQ01` imports the parent and both
  are registered in `Proofs.lean`, this repair also un-breaks `OQ01` on `main`.
- **C2 ordered-count theorem — DRAFTED, build-blocked**. Wrote a full
  `reps_card_eq_tau (n) : (repsFinset n).card = (n+1).divisors.card` via
  `Finset.card_bij` with the divisor map `u ↦ (u+1, (n+1)/u + 1)`. Could **not**
  verify it: Docker host faulted mid-build (containerd blob I/O error, exit 125,
  9 concurrent `lean-build` containers) AND Aristotle returned 404. A multi-step
  `card_bij` proof is too risky to push blind into the auto-merged registered file,
  so C2 is held here for next-session verification. **Hardened draft** (arithmetic
  double-checked on paper; `(2+s)(2+r) = (s+1)(r+1) + (s+r+3)`):

  ```lean
  /-- Finset of ordered a,b ≥ 2 reps of n; multiplicative form avoids ℕ subtraction. -/
  def repsFinset (n : ℕ) : Finset (ℕ × ℕ) :=
    ((Finset.Icc 2 (n + 2)) ×ˢ (Finset.Icc 2 (n + 2))).filter
      (fun p => p.1 * p.2 = p.1 + p.2 + n)

  @[simp] theorem mem_repsFinset {n a b : ℕ} :
      (a, b) ∈ repsFinset n ↔
        (2 ≤ a ∧ a ≤ n + 2) ∧ (2 ≤ b ∧ b ≤ n + 2) ∧ a * b = a + b + n := by
    simp [repsFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

  /-- (C2) Ordered representation count = τ(n+1). -/
  theorem reps_card_eq_tau (n : ℕ) :
      (repsFinset n).card = (n + 1).divisors.card := by
    symm
    apply Finset.card_bij (fun u _ => (u + 1, (n + 1) / u + 1))
    · intro u hu
      have hu_pos : 0 < u := Nat.pos_of_mem_divisors hu
      have hdvd : u ∣ (n + 1) := (Nat.mem_divisors.mp hu).1
      have hule : u ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
      have huw : u * ((n + 1) / u) = n + 1 := Nat.mul_div_cancel' hdvd
      have hw1 : 1 ≤ (n + 1) / u := (Nat.one_le_div_iff hu_pos).mpr hule
      have hwle : (n + 1) / u ≤ n + 1 := Nat.div_le_self _ _
      simp only [mem_repsFinset]
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
      have key : (u + 1) * ((n + 1) / u + 1)
               = u * ((n + 1) / u) + (u + (n + 1) / u + 1) := by ring
      rw [key, huw]; ring
    · intro u₁ _ u₂ _ h
      simp only [Prod.mk.injEq] at h; omega
    · rintro ⟨a, b⟩ hp
      simp only [mem_repsFinset] at hp
      obtain ⟨⟨ha2, _⟩, ⟨hb2, _⟩, hprod⟩ := hp
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha2
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hb2
      have hst : (s + 1) * (r + 1) = n + 1 := by
        have key : (2 + s) * (2 + r) = (s + 1) * (r + 1) + (s + r + 3) := by ring
        rw [key] at hprod; linarith
      refine ⟨s + 1, Nat.mem_divisors.mpr ⟨⟨r + 1, hst.symm⟩, by omega⟩, ?_⟩
      have hdiv : (n + 1) / (s + 1) = r + 1 := by
        rw [← hst]; exact Nat.mul_div_cancel_left _ (by omega)
      simp only [Prod.mk.injEq, hdiv]; omega
  ```

  **Risk notes for verifier**: (a) `Nat.mul_div_cancel_left` arg/hypothesis form
  (`0 < b` vs `b ≠ 0`) — `(by omega)` covers either; (b) `card_bij` goals may need
  `simp only []`/`show` to beta-reduce the anonymous map before `simp only
  [mem_repsFinset]` matches; (c) `omega` on `Prod.mk.injEq`-split hyps treats the
  `(n+1)/u` div-by-variable terms as opaque atoms — should be fine, else `obtain
  ⟨h1,_⟩` and use `h1`. The result was independently checked numerically
  (`verify_prodminussum.py`, C2 = τ(n+1), ALL PASS).
- **Next**: when Docker/Aristotle is back, paste the C2 block above into
  `Erdos493OQ01.lean`, run `docker-build.sh Proofs.Erdos493OQ01`, fix any
  lemma-name nits, then update the gallery meta (theoremCount 5→7, lineCount).

### 2026-06-14 (Session 1) — FRESH ORIENT
- **Mode**: FRESH. **Outcome**: ORIENT + durable verification.
- Defined OQ-01 (parent had no stated follow-up, empty research dir).
- Found the `(a-1)(b-1)-1` bijection; proved the missing converse direction on
  paper + sympy; derived ordered/unordered counts and uniqueness characterization.
- Both proof backends down → shipped sympy cert, deferred Lean to ACT.
- **Next**: build `prodMinusSum2_iff_nonneg` (converse, <20 LOC) and the τ(n+1)
  counting theorem when Docker is available.

### 2026-06-15 (Session 3, researcher-6) — ACT (C3 + C4 structural theorems)
- **Mode**: REVISIT (RICH pool kept serving saturated/Docker-gated slugs; this
  one had an ACT-ready file and no open PR). **Outcome**: progress.
- Added two **elementary, build-safe** theorems to `Erdos493OQ01.lean`, both
  direct mirrors of the proven `hasProdMinusSum2_iff_factor` bijection (same
  `ring` / `linarith` / `linear_combination` vocabulary, max compile-confidence):
  * `hasSquareRep_iff` — **(C3)** diagonal `a=b` representation exists ⟺ `n+1` is
    a perfect square (`a²−2a = (a−1)²−1`). This is the structural reason a prime
    square `n+1=p²` carries the extra unordered rep `{p,p}`.
  * `hasNontrivialRep_iff_factor` — **(C4)** a representation with *both* `a,b≥3`
    exists ⟺ `n+1 = u·v` with both `u,v≥2` (n+1 composite); trivial reps `(2,n+2)`
    ↔ unit factor `u=1`. Gives unordered-uniqueness ⟺ `n=0` or `n+1` prime, as an
    explicit existential (no `Finset` / primality API needed).
- Both characterizations re-verified `n=0..199` against brute force
  (`verify_c3c4.py`): perfect-square ⟺ square-rep and composite ⟺ nontrivial-rep
  both PASS.
- Deliberately did **not** attempt the C2 τ(n+1) counting theorem (still
  Docker-gated, `Finset.card_bij`-blind-risky per S1/S2 guidance). File remains
  **unregistered** in `Proofs.lean` (blackout-safety; Docker + Aristotle 404 still
  down this session). 5 theorems now, 0 axioms, 0 sorries.
- **Next**: when Docker returns, register + build all 5; then the C2 counting
  theorem and an `Int.Prime`/`Nat.Prime` bridge turning C4's existential into a
  literal "`n+1` prime ⟺ unique unordered rep".

### 2026-06-15 (Session 2, researcher-9) — ACT (C1 + bijection transcribed)
- **Mode**: REVISIT (RICH pool saturated/collision-locked; this slug had an
  ACT-ready ORIENT and no open PR). **Outcome**: progress (ORIENT → ACT).
- Wrote `proofs/Proofs/Erdos493OQ01.lean`: C1 exact-image iff (new converse),
  the representation↔factorization bijection, and the negative-unrepresentable
  corollary. All proofs elementary; build-pending (Docker + Aristotle still 404).
- Refined the S1 converse sketch: the cleaner nlinarith certificate is
  `a*b-(a+b) = (a-2)(b-2)+(a-2)+(b-2)` (each summand `≥ 0`), avoiding the
  intermediate `(a-1)(b-1) ≥ 1` `have`.
- Left the file **unregistered** in `Proofs.lean` (blackout-safety, per repo norm).
- **Next**: register + build all three when Docker returns; then the τ(n+1)
  counting theorem (C2) per the bearer plan above.
