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

---

## Session 2026-07-05 (Session 2) — ACT

**Mode**: CONTINUE. **Outcome**: progress (verified new result).

### What I Did
- Extended `Erdos1013UnconditionalRatio.lean` from 9 → 14 theorems with the unconditional
  **straddle-1** result, and verified it via the Docker wrapper (`docker-build.sh`,
  lean 4.26.0) — the containerd blackout that forced Session 1 onto the `lake env`
  passthrough has cleared, shared Mathlib volumes work from the worktree.
- New theorems (0 sorry / 0 axiom; `#print axioms` unchanged: propext/Classical.choice/Quot.sound):
  - `cesaro_ge_imp` / `cesaro_le_imp` — a vanishing Cesàro mean of a sequence cannot be
    eventually `≥` a fixed positive constant (resp. `≤` a fixed negative one).
  - `ratio_frequently_lt` / `ratio_frequently_gt` — for every `ε>0`, the ratio is `<1+ε`
    infinitely often and `>1−ε` infinitely often, i.e. `liminf ≤ 1 ≤ limsup`.
  - `h3_ratio_straddles_one` — the `h₃` specialisation (conjunction of both frequencies).

### Key Findings
- The averaged Cesàro fact is *strong enough to straddle 1 pointwise*. This is strictly
  sharper than the `[1/2,2]` bounded-ratio window leaf (which only gives `liminf ≤ 2`,
  `limsup ≥ 1/2`): the straddle pins `liminf ≤ 1 ≤ limsup`, ruling out any **one-sided
  drift** of the ratio away from 1. Oscillation across the `log log k` band is now the
  *sole* remaining obstruction to (⋆).
- Lean mechanics worth remembering:
  - `cesaro_ge_imp` splits `range K = range N ⊔ Ico N K`
    (`Finset.sum_range_add_sum_Ico a hK`), bounds the tail below by `c·(K−N)`
    (`Finset.sum_le_sum` + `Finset.sum_const` + `Nat.card_Ico` + `Nat.cast_sub`), and
    compares the two Cesàro limits with `le_of_tendsto_of_tendsto` (eventual `≤`).
  - `cesaro_le_imp` is the `-a` mirror: `hces.neg` + `simp` for `∑(-a) = -∑a`.
  - `field_simp` fully closed the `(S + c(K−N))/K = S/K + (c − cN/K)` identity — a trailing
    `ring` then errors with "no goals"; drop it.
  - Frequency statements via `by_contra` + `Filter.not_frequently` + `not_lt.mp`, then
    `Real.log_le_log` (monotone) + `Real.log_pos` / `Real.log_neg`.

### Files Modified
- `proofs/Proofs/Erdos1013UnconditionalRatio.lean` (extended: +5 theorems, module docstring)

### Next Steps
- Pointwise ratio → 1 still OPEN. The straddle closes the "no one-sided drift" direction;
  the only remaining attack is a genuine **local-variation** bound
  `|log h₃(k+1) − log h₃(k)| = o(1)`, which the current `log log k`-wide window cannot
  supply. Optional polish: promote the frequency forms to explicit `Filter.liminf/limsup`
  corollaries once cobounded side-conditions are provided.

---

## Session 2026-07-05 (Session 3, researcher-11) — ACT

**Mode**: CONTINUE. **Outcome**: progress (verified new result, first-try Docker build).

### What I Did
- Executed the "optional polish" flagged by Session 2: promoted the frequency straddle to
  the genuine `Filter.liminf`/`Filter.limsup` order-theoretic form. Extended
  `Erdos1013UnconditionalRatio.lean` from 14 → 18 theorems (0 sorry / 0 axiom;
  `#print axioms` unchanged: propext/Classical.choice/Quot.sound).
- New theorems:
  - `ratio_liminf_le_one` — `liminf_k h(k+1)/h k ≤ 1`, needs `IsBoundedUnder (· ≥ ·)`.
  - `one_le_ratio_limsup` — `1 ≤ limsup_k h(k+1)/h k`, needs `IsBoundedUnder (· ≤ ·)`.
  - `ratio_liminf_le_one_le_limsup` — the conjunction (general `PolyBounded` `h`).
  - `h3_ratio_liminf_le_one_le_limsup` — `h₃` specialisation; takes eventual two-sided
    ratio bounds `m ≤ ratio ≤ M` and constructs the `IsBoundedUnder` witnesses.

### Key Findings
- The "frequently `< 1±ε` for all ε" facts are *definitionally* the liminf/limsup bounds;
  the only extra content needed to state them as honest `Filter.liminf`/`Filter.limsup` is
  a **cobounded side-condition** (ratio eventually bounded below / above), which the
  `[1/2, 2]` bounded-ratio leaf (`Erdos1013BoundedRatio.lean`) already supplies for `h₃`.
- **Corollary of independent interest:** `liminf ≤ 1 ≤ limsup` forces any *existing* limit
  of the ratio to equal `1`. So the open (⋆) is now "does the limit exist?", never "what
  is it?" — the value is pinned unconditionally.

### Lean mechanics worth remembering
- `Filter.liminf_le_of_frequently_le (hfreq : ∃ᶠ x, u x ≤ b) (hbdd : IsBoundedUnder (· ≥ ·) l u) : liminf u l ≤ b`
  and dual `Filter.le_limsup_of_frequently_le` — pass the boundedness explicitly (it's an
  `isBoundedDefault` autoparam that will NOT auto-discharge here).
- Weaken `∃ᶠ x, u x < c` to `∃ᶠ x, u x ≤ c` via `Filter.Frequently.mono fun k hk => le_of_lt hk`.
- `IsBoundedUnder (· ≤ ·) atTop u` unfolds (defeq, via `eventually_map`) to
  `∃ b, ∀ᶠ x, u x ≤ b`, so the anonymous constructor `⟨M, habove⟩` builds it directly from
  an eventual bound — no need for named `isBoundedUnder_of_eventually_*` lemmas.
- `liminf ≤ 1` from `∀ ε>0, liminf ≤ 1+ε`: `by_contra`/`push_neg` to `1 < L`, pick
  `ε = (L-1)/2`, apply the frequently-lemma, `linarith`. Symmetric for limsup with
  `ε = min ((1-L)/2) (1/2)` to keep `ε < 1` (required by `ratio_frequently_gt`).

### Files Modified
- `proofs/Proofs/Erdos1013UnconditionalRatio.lean` (extended: +4 theorems, +docstring)

### Next Steps
- Pointwise (⋆) still OPEN — unchanged obstruction (local variation across the
  `log log k` band). The value of any limit is now fully pinned to 1; only *existence*
  remains, which needs the improved upper bound / local-variation relation.
