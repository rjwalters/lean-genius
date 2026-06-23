# Erdős #258 — OQ-01: irrationality for arbitrary (non-monotone) sequences

**Problem.** `a : ℕ → ℕ`, `aₙ → ∞`. Is `S(a) = ∑ₙ τ(n+1)/(a₁⋯aₙ)` irrational?
Monotone case: Erdős–Straus 1971 (uses averaging of `τ`). General **non-monotone**
case: OPEN. This OQ asks the general case.

## Summary of contribution (ORIENT, Docker outage → build-free)

Reframed `S(a)` as a **Cantor series** and reduced the whole open content to a
single liminf claim about the **renormalised tail**
`T_N(a) = ∑_{n>N} τ(n+1)/(a_{N+1}⋯a_n) = τ(N+2)/a_{N+1} + τ(N+3)/(a_{N+1}a_{N+2}) + ⋯`.

Algebraic identity (★): `(a₁⋯a_N)·S(a) = integer + T_N(a)`. So if `S(a)=p/q`
then `q·T_N(a) ∈ ℤ`, and since `T_N>0` it is a **positive** integer, i.e.
`T_N(a) ≥ 1/q` for all `N`.

### Lemmas (in `proofs/Proofs/Erdos258OQ01.lean`)
- **Lemma A (engine):** `liminf_N T_N(a) = 0 ⟹ S(a) irrational`. Elementary,
  fully formalisable. (positive-integer-≥1 contradiction with liminf 0.)
- **Lemma B:** `a_n ≥ n^δ` eventually (any `δ>0`) ⟹ `T_N → 0`. Denominators
  `≥ (N+1)^{δ(n−N)}` dominate `τ(n+1)=n^{o(1)}`; geometric ratio `(N+1)^{−δ}→0`.
- **Corollary C:** polynomial growth ⟹ irrational, **no monotonicity needed** —
  a new sufficient condition strictly inside the non-monotone regime (E–S 1971
  needs monotone). 
- **Reduction:** `oq01 ⟸ (∀ a→∞: liminf_N T_N(a) = 0)`.

### The crux / open zone (empirically delineated)
`aₙ → ∞` ALONE does NOT force `liminf T_N = 0`: the leading term
`τ(N+2)/a_{N+1}` spikes whenever `N+2` is highly composite. The growth
threshold is real:

| sequence `aₙ`                          | `T_N` behaviour (exact sympy)        | engine |
|----------------------------------------|--------------------------------------|--------|
| `n²`, `n` (poly)                       | `→ 0` rapidly                        | fires ⟹ irrational |
| `⌊n^δ⌋`, any `δ>0`                     | `→ 0` (slow for small δ)             | fires ⟹ irrational |
| `(log n)²`, `log n`                    | hovers ≈0.2–0.5, very slow decay     | does not fire (elementary) |
| `max(τ(n+1),⌊√n⌋)` (non-monotone)     | hovers ≈0.22–1.1, `liminf>0`         | does not fire |

So the **remaining open zone is exactly: `aₙ → ∞` with subpolynomial growth
`aₙ = n^{o(1)}`, non-monotone.** [CORRECTED Session 3: the `liminf T_N>0` rows
below are NOT robust — over longer windows these `T_N` dip to ≈0.02 with erratic
non-monotone decay; the subpolynomial zone is numerically ambiguous, not clearly
`liminf>0`.] There the renormalised tail can stay bounded
below; rationality would additionally need the rigid `q·T_N ∈ ℤ` eventually,
which the wandering observed values (no convergence onto a `1/q`-grid) suggest
never happens — but that is beyond the elementary engine.

Probes: `probe.py` (identity check + 5 sequence families), `threshold_probe.py`
(δ-threshold sweep). Identity (★) verified to machine precision for `N≥1`.

## Sessions

### 2026-06-14 (Session 2) — open-zone rationality probe (deferred S1 next-step)

**Mode**: REVISIT. **Outcome**: ORIENT/evidence (build-free; Docker still down).
Closes S1's explicitly-deferred next-step *"investigate the subpolynomial zone: is
there a non-monotone aₙ→∞ making `q·T_N∈ℤ`?"* — from the dual angle: is `S(a)`
itself a low-denominator rational there?

**Method** (`verify_openzone_rationality.py`). For a sequence `a`, `S(a)` is
super-exponentially convergent, so the exact truncation `S_K` (`K=150`, `Fraction`)
differs from true `S` by `< last term ≈ 10⁻¹³¹…10⁻¹⁸⁵`. The continued-fraction
convergents of `S_K` are the **best** rational approximations (no rational with
denominator `≤ kₙ` beats the `n`-th convergent), so if true `S` were rational `p/q`
with `q ≤ Q`, a convergent with `denom ≤ Q` would match `S_K` to within the
truncation tail. **It does not.**

**Result (exact arithmetic — float underflows for these convergents, so the script
compares `Fraction`s):**
- Both open-zone non-monotone families — `aₙ=max(τ(n+1),⌊√n⌋)` and
  `aₙ=⌊(log(n+2))²⌋+2` — have **no rational with `q ≤ 10⁹`** closer than `≈10⁻¹⁸`,
  i.e. `≳10¹¹³` times the truncation accuracy. So `S` is **not** a rational with
  denominator `≤ 10⁹` in the open zone.
- CF partial quotients are Gauss–Kuzmin-typical (largest seen ≈84), with **no giant
  partial quotient** — the signature a near-rational would show is absent.
- Control `aₙ=n²` (proven irrational by the engine) shows the **same** signature,
  validating the test.

**Reading.** Evidence — *not proof* — that the answer is "irrational" precisely in
the open zone where the elementary `liminf T_N=0` engine is silent. It rules out
only the small-denominator-rational escape (`q ≤ 10⁹`); the genuine open question
(no `q` works for some pathological non-monotone `aₙ`) remains beyond this method.
No change to the Lean file or the 4 lemmas; 4 `sorry`s intact.

### 2026-06-14 (Session 1) — FRESH ORIENT
**Mode**: FRESH. **Outcome**: ORIENT (reduction + engine + new sufficient condition).
- Reframed as Cantor series; derived identity (★) and the `q·T_N∈ℤ≥1` mechanism.
- sympy probes: confirmed (★); mapped the polynomial vs subpolynomial threshold;
  showed `liminf T_N>0` for slow non-monotone families ⟹ engine genuinely fails
  there (= the open zone).
- Wrote `Erdos258OQ01.lean`: Lemma A (engine), Lemma B (poly ⟹ T_N→0),
  Corollary C (non-monotone poly ⟹ irrational), reduction theorem.
- Docker DOWN → file carries honest `sorry`s, NOT build-verified. Math is
  elementary for A/C; B needs Mathlib `τ(n)=O(n^ε)`.

**Next steps**:
- Build-verify Lemma A first (most self-contained) once Docker returns.
- For Lemma B: locate Mathlib bound `τ n ≤ C_ε n^ε` (or use crude `τ n ≤ 2*√n`
  to get the `δ>1/2` case unconditionally).
- Investigate the subpolynomial zone: is there a non-monotone `aₙ→∞` making
  `q·T_N∈ℤ` for all large `N`? (probe denominators of exact `T_N`.)

### 2026-06-15 (Session 3) — Cantor recursion + open-zone correction (ORIENT, build-free)
**Mode**: depth-first (MODERATE, score 14). **Outcome**: new verified identity +
honest correction. Docker DOWN (`docker info` timeout) and Aristotle 404 ("Resource
not found") on a trivial ping — dual blackout, build-free turn.

- **New verified backbone identity** (`verify_recursion.py`, exact `Fraction`,
  6 families, all PASS): the renormalised tail obeys the Cantor recursion
  **(R) `a_{N+1}·T_N = τ(N+2) + T_{N+1}`** and base case **(B) `S = τ(1) + T_0`**
  (`τ(1)=1`). Added both to `Erdos258OQ01.lean` as
  `renormTail_recursion` / `S_eq_head_add_renormTail_zero` (clean `sorry` stubs,
  consistent with the unbuilt file). (R)+(B) give an **inductive** proof of (★)
  with `m₀=τ(1)`, `m_{N+1}=a_{N+1}m_N+τ(N+2)` — replaces the messy unindexed tsum
  regrouping in `partialProduct_smul_S` by a one-step factor-out; docstring now
  carries that derivation. Recursion also recasts the obstruction in pure integer
  terms: `S=p/q ⟺ ∃q≥1 ∀N q·T_N∈ℤ`, and then `r_N:=q·T_N` are positive integers
  with `r_{N+1}=a_{N+1}r_N − q·τ(N+2)` (algebra verified).

- **HONEST CORRECTION to Session-1's open-zone table.** Over a longer N-window
  (exact, up to N≈12000, K=1500) the subpolynomial families are **NOT** a clean
  `liminf T_N>0`: trajectories are non-monotone with deep dips toward 0 —
  `√n` reaches ≈0.020, `max(τ,√n)` ≈0.020, `(log n)²` ≈0.025 — but the decay is
  erratic and slow, so **"→0" is equally unsupported**. The subpolynomial zone is
  genuinely **ambiguous numerically**, not settled either way (Session-1's tidy
  "liminf>0" entries overstated it).

- **Refuted a tempting conjecture.** "`a_n/τ(n)→∞ ⟹ T_N→0`" is **FALSE**:
  `a_n=τ(n)·⌊log n⌋` has `a_n/τ(n)=⌊log n⌋→∞` yet `T_N` spikes back to ≈0.89 at
  N=4000 — because numerator `τ(N+2)` and denominator `a_{N+1}` are index-shifted,
  so `a_n/τ(n)→∞` does NOT control the leading term `τ(N+2)/a_{N+1}`. The only
  rigorously CLOSED sufficient condition stays **polynomial** `a_n≥n^δ` (Cor. C),
  which still needs the same Mathlib `τ=O(n^ε)` bound for build-verification.

**Next steps** (unchanged frontier):
- Build-verify `renormTail_recursion` + `S_eq_head_add_renormTail_zero` first
  (most local), then assemble (★) by induction, then Lemma A.
- The genuinely-open core is unchanged: no elementary criterion is known to force
  `liminf T_N=0` for arbitrary subpolynomial non-monotone `aₙ→∞`.
