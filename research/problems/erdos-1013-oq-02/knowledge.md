# Knowledge Base: erdos-1013-oq-02

Unconditional ratio convergence of the triangle-free chromatic threshold `h₃`.

---

## Problem Understanding

Erdős #1013 asks whether `h₃(k+1)/h₃(k) → 1`, where `h₃(k)` is the least number of
vertices in a triangle-free graph of chromatic number `k`. The known bounds are

    (log k / log log k)·k²  ≪  h₃(k)  ≪  (log k)·k².

Sibling **oq-01** (`Erdos1013ConstantRatio.lean`) proved the ratio → 1 *conditionally*:
if the asymptotic constant `c` in `h₃(k) ~ c·k²·log k` exists (`c > 0`), then the ratio
converges. This oq-02 is the **remaining unconditional gap**: prove ratio → 1 without
assuming `c` exists.

---

## Insights

### The pointwise statement is genuinely OPEN (and why)
Write `r_k := log(h₃ k) − (2·log k + log log k)`. Then `h₃(k+1)/h₃(k) → 1` is equivalent
to `r_{k+1} − r_k → 0`. The known two-sided bounds pin `r_k` only to an interval of width
`≈ log log k`, which is **unbounded**, so they permit `r_k` to oscillate by
`O(log log k)` between consecutive indices — enough to keep individual ratios away from 1.
A naive squeeze `lower(k+1)/upper(k) ≤ ratio ≤ upper(k+1)/lower(k)` collapses to
`[1/log log k, log log k]`, useless. So closing the `log log k` gap is the real content.

### The AVERAGED statements ARE unconditional (this session's contribution)
The known bounds give exactly one clean fact: `h₃` is **polynomially sandwiched**
(`k² ≤ h₃(k) ≤ k³` eventually), hence `log(h₃ k)/k → 0` (subexponential growth). From
this single "engine" fact, *telescoping cancels the oscillation* and yields, **with no
hypothesis on `c`**:

  * Cesàro mean of log-ratios → 0:  `(1/K)·Σ_{k<K} log(h₃(k+1)/h₃(k)) → 0`
    (telescopes to `(log h₃(K) − log h₃(0))/K → 0`);
  * geometric mean of consecutive ratios → 1:  `(h₃(K)/h₃(0))^{1/K} → 1`;
  * root test trivial:  `h₃(k)^{1/k} → 1`.

These are the "averaged shadow" of the open pointwise (⋆): the pointwise ratio → 1 is
equivalent to log-ratios → 0 *pointwise* (`ratio_iff_log_ratio`); we prove only their
Cesàro average → 0, which is strictly weaker and does not settle (⋆).

### Engine lemma
`log_div_tendsto_zero`: any positive, eventually-`[A, B·kᵈ]`-sandwiched sequence has
`log(h k)/k → 0`. Proof = squeeze between `log A/k → 0` and `(log B + d·log k)/k → 0`,
the latter using `log k / k → 0` (from `Real.isLittleO_log_id_atTop`).

---

## Dead Ends

- **Naive two-sided squeeze of the pointwise ratio**: the `log log k` gap between the
  known upper/lower bounds makes `lower(k+1)/upper(k)` and `upper(k+1)/lower(k)` diverge
  to `0` and `∞`; gives nothing pointwise.
- **Weakening oq-01's hypothesis to "monotone + bounded"**: `h₃/scale` is not known
  bounded below by a positive constant (the lower bound has an extra `1/log log k`), so
  monotone-bounded ⇒ convergent does not apply from known facts.

---

## Session 2026-07-04 (Session 1) — ACT

**Mode**: FRESH. **Outcome**: progress (verified partial result).

### What I Did
- Created `proofs/Proofs/Erdos1013UnconditionalRatio.lean` (9 theorems, 0 sorries,
  0 counted axioms; `#print axioms` = propext/Classical.choice/Quot.sound only).
- Proved the three unconditional averaged forms (Cesàro / geometric-mean / root) for any
  polynomially bounded positive `h`, plus the `h₃`-specialisations `h3_*` and the framing
  lemma `ratio_iff_log_ratio`.
- Verified by single-file elaboration (`lake env lean`) against Mathlib v4.26.0 — Docker
  build wrapper is down (containerd meta.db EIO blackout), so used the passthrough
  `lake env` path with the shared olean cache.

### Key Findings
- The open pointwise (⋆) reduces to controlling *local* variation of `r_k` within the
  `log log k` band; telescoping makes only the endpoint `r_K = o(K)` matter, which is why
  the averaged forms survive unconditionally.

### Files Modified
- `proofs/Proofs/Erdos1013UnconditionalRatio.lean` (new)

### Next Steps
- The pointwise ratio → 1 remains OPEN. A genuine attack would need either (a) an
  improved *upper* bound `h₃(k) ≤ (c+o(1))·k²·log k` removing the `log log k` gap, or
  (b) a direct super/subadditivity relation between `h₃(k)` and `h₃(k+1)` controlling
  local variation. Neither is currently in reach; (a) is essentially the asymptotic
  constant question.
