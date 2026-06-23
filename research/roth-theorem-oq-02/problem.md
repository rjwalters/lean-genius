# roth-theorem-oq-02 — Problem Statement

**Parent**: `roth-theorem` (1401-line Lean formalization, 42 theorems, 0 sorries / 0 axioms,
`mathlib`-badged via `roth_3ap_theorem_nat`). The parent gives the *qualitative* Roth
theorem (every AP-free `A ⊆ {1,…,N}` has density → 0), with an ineffective bound coming
from Mathlib's corners-theorem / Szemerédi-regularity chain (`SzemerediRegularity.bound`
is tower-type, so the bound on `r₃(N)` from `roth_3ap_theorem_nat` is much weaker than
the well-known `N (log log N / log N)^{1/4}` of Heath-Brown / Szemerédi 1987).

**Concrete Lean target**: `Proofs/RothTheoremQuantitative.lean` (line 211–214)
already states the goal as

```
theorem bloom_sisask_bound :
    ∃ (c : ℝ), c > 0 ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumber N : ℝ) ≤ N / (Real.log N) ^ (1 + c) := by
  sorry
```

So OQ-02 is literally "discharge the `sorry` at line 214 of
`RothTheoremQuantitative.lean`". The same file also carries `sorry`s for
`roth_quantitative_upper_bound` (Roth 1953, line 187–190),
`behrend_lower_bound` (Behrend 1946, line 201–204), and
`kelley_meka_upper_bound` (KM 2023, line 223–226). The gallery entry
`roth-theorem-k3-oq-01` currently exposes this file with `badge: wip, sorries: 4`.

S1 also surfaces that **Behrend's lower bound (`behrend_lower_bound` at line 201)
is already proven in Mathlib** as `Behrend.roth_lower_bound` (in
`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`); the sorry can be
discharged by a one-shot wrapper — this is a separate, **much smaller**, win that
falls naturally out of the OQ-02 problem class but is independent of the
Bloom–Sisask main theorem. We surface it here so a later session can pick it up
without re-discovering it.

**OQ-02 source statement** (from `.lean/state/candidate-pool.json`):

> Formalize the Bloom-Sisask bound `r₃(N) = O(N / log^{1+c} N)`.

This is the headline result of:

> Thomas F. Bloom and Olof Sisask,
> *Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions*,
> Annals of Mathematics 199 (2024), 819–953; arXiv:2007.03528 (2020).

## Precise statement (Bloom–Sisask 2020 / Annals 2024)

There exists an absolute constant `c > 0` such that

```
  r₃(N) := max { |A| : A ⊆ {1,…,N} and A is 3-AP-free } ≤ N / (log N)^{1+c}
```

for all `N ≥ 2`. The proof gives `c = 1/9 - o(1)` (later refinements by Kelley–Meka
2023 in the ℤ/Nℤ setting reach `2^{-O((log N)^{1/12})}`, which is even outside the
"logarithmic barrier"; the OQ-02 target is the Bloom–Sisask exponent).

**Why "breaking the logarithmic barrier" matters**: For 70+ years, every bound on
`r₃(N)` was of the form `N / (log N)^{c}` for various `c < 1` (Roth 1953: c=1/log log;
Heath-Brown / Szemerédi 1987: c=1/4 (real-line) and `(log log)^{-1}` on integers;
Bourgain 1999: c=1/2, then 2/3, then 1; Sanders 2011: `c≈(log log)^{-1}` removed
log-log loss; **Bloom 2016: c=1−o(1)**). The Bloom–Sisask `c > 1` is the first
result that beats `N/log N` itself — qualitatively, "almost all `N`-sets of density
slightly above `1/log N` contain a 3-AP". This unlocks the well-known
**Erdős conjecture on AP-rich sets**: every set of natural numbers with
`Σ_{n ∈ A} 1/n = ∞` contains arbitrarily long APs — Bloom–Sisask's bound proves
**the k=3 case for the first time**, after 80 years.

## S1 Observation: this is a multi-year formalization target

The Bloom–Sisask paper is roughly 75 pages of dense analytic combinatorics. Its
proof structure has *no Mathlib-shaped subproof of similar size*. The directly
underlying tools include:

1. **Density increment via Fourier analysis on Z/NZ** (parent `roth-theorem`
   covers `δ²N/4` increment, but only enough to recover the qualitative Roth).
2. **Bohr sets and additive structure** (`Bohr(A; ρ)` = sets in which a frequency
   set `Γ` has small character variation). Mathlib has **no** Bohr-set theory.
3. **L²-style energy increment / "spectral approximate sumsets"** introduced by
   Bateman–Katz and refined throughout the Bloom 2016 / Schoen 2021 / Bloom–
   Sisask 2020 line. Mathlib has nothing of this kind.
4. **Croot–Sisask almost-periodicity lemma** (2010): if `|A + A| ≤ K|A|`, then
   `A` has a Bohr-like translation-invariant subset of density `exp(−K^{O(1)})`.
   Mathlib has nothing of this kind.
5. **The Bloom–Sisask "spectral chang" decomposition** combined with a quantitative
   structure theorem for the large spectrum (`Spec_ρ(A)`).

So an *honest* OQ-02 attempt is on the order of: define Bohr sets in Mathlib
(maybe 200–400 lines); construct the spectrum / Spec_ρ machinery (300–500
lines); formalize Croot–Sisask (probably 500+ lines); chain everything for the
final density increment (the heart of Bloom–Sisask, several thousand lines).

**This S1 session does not attempt any Lean proof.** It records the problem,
the proof landscape, and a phased plan, plus the obvious smaller wins along
the way.

## Phased plan (proposed)

The path from "qualitative Roth (already in `roth-theorem`)" to "Bloom–Sisask
quantitative bound (OQ-02)" naturally factors as:

### Phase A — "log-barrier preliminaries" (recommended S2…S10)

Targets achievable without Bohr sets or spectrum theory:

- **A1.** Behrend's lower bound `r₃(N) ≥ N · exp(−c √(log N))` (constructive;
  parent `roth-theorem` proves only the upper-bound side, leaving the matching
  lower bound undocumented). Behrend's construction is a Mathlib-friendly
  exercise: take `S ⊆ {1,…,M}^d` of `ℓ²`-norm in a thin shell and map to ℕ via
  base-`(2M)` digit expansion.
- **A2.** Heath-Brown / Szemerédi 1987 bound `r₃(N) ≤ N (log log N)^{1/4} /
  (log N)^{1/4}` — uses essentially the same Fourier / density-increment
  machinery as the parent file, sharpened by tracking the "Bohr neighbourhood"
  inside an arithmetic progression.
- **A3.** Bourgain's `r₃(N) ≤ N (log log N)^2 / log N`. *Now we need Bohr sets.*
  This is the first true "Phase B" target, but a careful formalization of
  Bourgain's argument in Mathlib would itself be a significant contribution.

### Phase B — "log barrier" (S11…S20+)

- **B1.** Define `BohrSet G Γ ρ` for finite abelian `G`, frequency set `Γ ⊆ Ĝ`,
  width `ρ ∈ [0,1]`. Develop the basic theory: `BohrSet ⊇ {0}`, size lower
  bound `|BohrSet| ≥ ρ^|Γ| |G|` (Plünnecke-style packing).
- **B2.** Spec_ρ(A) := { r : |Â(r)| ≥ ρ |A| } and Chang's theorem
  (`|Spec_ρ(A)| ≤ ρ^{−2} log(1/α)`, dimension version).
- **B3.** Sanders 2011 bound `r₃(N) ≤ N / (log N)^{1−o(1)}` via the
  Spec ↔ Bohr duality and density increment.

### Phase C — "breaking the barrier" (the Bloom–Sisask main theorem)

- **C1.** Croot–Sisask almost-periodicity.
- **C2.** Bloom–Sisask "fractional dimension" of the large spectrum.
- **C3.** Density increment exponent `1 + c` for some explicit `c > 0`.
- **C4.** Final main theorem: `r₃(N) ≤ N / (log N)^{1+c}`.

## What S1 does NOT attempt

- No new Lean files. The parent `RothTheorem.lean` is untouched.
- No commitment to a particular `c` in `(log N)^{1+c}` (the paper achieves
  `c = 1/9` at the time of writing; Mathlib formalization could aim lower).
- No commitment to the *additive* setup (`{1,…,N} ⊆ ℤ`) vs. ZMod (`Z/NZ`).
  The parent file uses `ZMod N`; Bloom–Sisask is stated for both — the
  transfer is routine and a later phase concern.

## Concrete S2 candidates (in priority order)

1. **A1′ (Behrend lower bound via Mathlib wrapper)** — DISCHARGE the existing
   `behrend_lower_bound` sorry at `Proofs/RothTheoremQuantitative.lean:201–204` by
   wrapping `Behrend.roth_lower_bound` (already in Mathlib). This is an
   ~10–30-line build-verified PR. It does *not* directly attack Bloom–Sisask,
   but it cleans the surrounding file (4 sorries → 3) and demonstrates that
   the bridge from `rothNumber N` (the gallery's definition) to
   `Nat.rothNumberNat N` (Mathlib's, in `Mathlib/Combinatorics/Additive/AP/Three/Defs.lean`)
   is solid — that bridge is required for *every* future quantitative result.
2. **Define `BohrSet` (Phase B setup)** — pure-definition session, no proofs
   beyond `BohrSet ∋ 0`. Sets up Phase B; commits to a Mathlib-compatible
   shape `BohrSet (G : Type*) [AddCommGroup G] (Γ : Finset Ĝ) (ρ : ℝ) :
   Finset G` so downstream Bohr-set work can stack without re-definitions.
3. **A2 (Heath-Brown / Szemerédi `r₃ ≤ N · (log log N / log N)^{1/4}`)** —
   incremental sharpening of the parent `density_increment_lemma` to track Bohr
   neighbourhoods inside an AP. Strictly stronger than A1, strictly weaker than
   any Phase B result.

S2 will pick (1) — discharging the Behrend sorry — as the cheapest, most
build-verified-friendly continuation. The Bloom–Sisask sorry itself
(`bloom_sisask_bound`) is **not** an S2 target; it requires the full Phase B
+ Phase C buildup over many sessions.
