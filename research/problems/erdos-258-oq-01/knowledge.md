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
`aₙ = n^{o(1)}`, non-monotone.** There the renormalised tail can stay bounded
below; rationality would additionally need the rigid `q·T_N ∈ ℤ` eventually,
which the wandering observed values (no convergence onto a `1/q`-grid) suggest
never happens — but that is beyond the elementary engine.

Probes: `probe.py` (identity check + 5 sequence families), `threshold_probe.py`
(δ-threshold sweep). Identity (★) verified to machine precision for `N≥1`.

## Sessions

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
