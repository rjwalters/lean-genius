# Problem: Quantitative Bounds for 3-AP-Free Sets (Kelley–Meka direction)

**Slug**: szemeredi-theorem-oq-01
**Created**: 2026-04-05
**Status**: Active (Phase: ORIENT)
**Source**: user-request

## Problem Statement

### Formal Statement

Let $r_3(N)$ denote the maximum size of a 3-AP-free subset of $\{1,\dots,N\}$.
The Kelley–Meka theorem (2023) states:

$$
r_3(N) \;\le\; N \cdot \exp\!\big(-c\,(\log N)^{1/12}\big)
$$

for some absolute constant $c > 0$ and all sufficiently large $N$. The
Behrend lower bound (1946) provides $r_3(N) \ge N \cdot \exp(-c'\sqrt{\log N})$,
so the gap between upper and lower bounds is now sub-polynomial in $\log N$
on both sides.

### Plain Language

A 3-term arithmetic progression (3-AP) is a triple $a$, $a+d$, $a+2d$ with
$d \neq 0$. We want to bound how large a subset of $\{1,\dots,N\}$ can be if
it contains no 3-AP. The classical Roth bound (1953) is $N/\log\log N$;
Bloom–Sisask (2020) improved this to $N (\log N)^{-(1+\varepsilon)}$;
Kelley–Meka (2023) finally broke the "logarithmic barrier" with the
quasi-polynomial bound above. The question is whether this near-optimal
bound can be formalized in Lean 4 / Mathlib.

### Why This Matters

- The Kelley–Meka bound is the most significant advance in additive
  combinatorics since Gowers' 2001 work, closing a long-standing gap.
- A formalization would establish a working pipeline in Mathlib for
  higher-order Fourier / spectral combinatorics arguments.
- Downstream consequences include sharper bounds in cap-set, sumset
  density, and progression-counting problems.
- The full proof uses ideas (sifted spectral structure, dimensional
  amplification, density increment via Bohr sets) that have wide
  applicability beyond AP-free sets.

## Known Results

### What's Already Proven (in this gallery / Mathlib)

- **Roth's theorem (k=3, qualitative)**: `Proofs/SzemerediTheorem.lean`
  proves the full Szemerédi statement for `k=3` via Mathlib's chain
  Regularity → Triangle Removal → Corners → Roth. Status: `axiomatized`
  only because k ≥ 4 requires hypergraph regularity; the k=3 piece itself
  is fully proved.
- **Roth quantitative bound (corners-based)**: Mathlib exposes
  `cornersTheoremBound` (`Mathlib.Combinatorics.Additive.Corner.Roth`),
  which gives an effective (tower-type) bound. This is far weaker than
  Kelley–Meka but is the only quantitative bound currently in scope.
- **Behrend lower bound**: present in Mathlib via the
  `addSalemSpencer_image_iff` and Behrend-construction infrastructure
  (`Mathlib.Combinatorics.Additive.Behrend`).
- **Salem–Spencer / `rothNumberNat`**: full API for the AP-free counting
  function exists in Mathlib.

### What's Still Open (Mathlib)

- **Bloom–Sisask (2020)**: `r_3(N) \le N (\log N)^{-(1+\varepsilon)}`.
  Not formalized. Uses the "almost periodicity" framework of Croot–Sisask.
- **Kelley–Meka (2023)**: the target bound above. Not formalized.
- **Quantitative version with explicit constants**: Mathlib's
  `cornersTheoremBound` is qualitative-quantitative; the explicit
  log–log–log constants from Roth's original proof are not extracted.

### Our Goal

Choose one of three concrete formalizable targets:

1. **AXIOMATIZED-STATEMENT** (Survey deliverable): state the Kelley–Meka
   theorem inside the gallery's `Szemeredi*` namespace as an `axiom` (or
   structure-encoded hypothesis), with a Lean-level lemma chain showing
   how it specializes/strengthens existing Mathlib results. Roughly
   30 lines, dependent on nothing new.
2. **WEAKER-EXPONENTIAL-BOUND** (1–2 sessions): formalize the
   Salem–Spencer (1942) bound `r_3(N) = O(N / \log\log N)` as a corollary
   of `cornersTheoremBound` with explicit constants. ~150 lines.
3. **KM-LEMMA-PORT** (long-horizon, 1+ week per lemma): pick a single
   stand-alone lemma from the Kelley–Meka paper (e.g. the Croot–Sisask
   almost-periodicity lemma, or a Bohr-set density-increment step) and
   formalize it in isolation. Each lemma is ~200–500 lines.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `szemeredi-theorem` | Direct parent (k=3 qualitative settled, k≥4 axiomatized) | Mathlib corners chain |
| `szemeredi-regularity` | Underlies the k=3 → k=4 step but irrelevant to Kelley–Meka's spectral approach | Regularity lemma |
| `szemeredi-counting` | Counting lemma for AP detection (1196 lines, 0 sorries) | Combinatorial counting |
| `szemeredi-hypergraph-core` | k≥4 infrastructure direction (orthogonal to KM) | Hypergraph regularity |
| `szemeredi-core-oq-04` | Active branch with 21 sorries — distinct line | (varies) |

The Kelley–Meka direction is **methodologically separate** from the
regularity / corners / hypergraph lines that dominate the existing
`Szemeredi*` gallery work. It needs higher-order Fourier and spectral
sifting machinery that is not currently developed in this gallery.

## Initial Thoughts

### Potential Approaches

1. **Approach A — Axiomatized statement (tractable, low value)**
   - State `kelleyMeka_3AP : ∃ c > 0, ∀ N ≥ N₀, r_3(N) ≤ N * exp(-c * (log N)^(1/12))` as an `axiom`.
   - Prove it implies `cornersTheoremBound` (qualitatively).
   - Cost: ~30–50 lines; provides a citeable handle but no actual mathematical progress.
   - Per the role guide on axiom integrity, this should be marked
     `axiomatized`, badge `axiom`, and be honest about what it adds.

2. **Approach B — Salem–Spencer quantitative (medium value)**
   - Extract `O(N / log log N)` from `cornersTheoremBound` with explicit
     constants. The qualitative version exists; the bookkeeping for
     explicit constants is what's missing.
   - ~150–300 lines. Risk: Mathlib's corners bound may already be a
     tower-type bound (in which case extracting log-log is the gap, not
     the corners proof itself).

3. **Approach C — Croot–Sisask almost periodicity lemma (high value, far reach)**
   - The CS lemma states: for $A \subseteq \mathbb{F}_p^n$ of density $\alpha$,
     there exist many $t$ such that $\|1_A * 1_{-A}(\cdot+t) - 1_A * 1_{-A}\|_{L^p}$
     is small. This is the core "almost-periodicity" ingredient of both
     Bloom–Sisask and Kelley–Meka.
   - ~500–1000 lines depending on how much Mathlib's L^p convolution API
     covers. Currently `Mathlib.Analysis.Convolution` exists but I have
     not audited whether the discrete-cyclic case has full API.

### Key Difficulties

- Higher-order Fourier (Gowers norms) infrastructure is partial in
  Mathlib: `Mathlib.Analysis.InnerProductSpace.GowersUniformity` has
  $U^2$ but not the full $U^k$ tower.
- Bohr sets and density-increment arguments are entirely absent — and
  these are the heart of Kelley–Meka.
- The Kelley–Meka proof relies on a delicate combination of spectral and
  combinatorial arguments; even the paper is ~30 pages of dense
  argument.
- This gallery's `Szemeredi*` line so far follows the qualitative /
  regularity / hypergraph direction, so there is no Bohr-set or sifted
  Fourier infrastructure to build on.

### What Would a Proof Need?

- Key lemma 1: Bohr-set machinery (definition, regularity of Bohr sets,
  Plünnecke-type sumset bounds for Bohr sets).
- Key lemma 2: Croot–Sisask almost-periodicity (in the $\mathbb{F}_p^n$
  model or $\mathbb{Z}/N\mathbb{Z}$).
- Key lemma 3: Density-increment lemma — if $A$ has no 3-AP, there is a
  Bohr set $B$ on which $A$ has density $\ge \alpha (1 + \varepsilon)$.
- Technical: discrete Fourier on $\mathbb{Z}/N\mathbb{Z}$ with
  explicit constants; convolution-norm interpolation;
  $\ell^p$-spectral sifting (the new Kelley–Meka ingredient).

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Approach A (axiomatize) is trivial but provides little value beyond
  documentation.
- Approach B (Salem–Spencer quantitative) is medium difficulty and
  bounded scope — a strong candidate for a 1–2 session sprint.
- Approach C (Croot–Sisask) is a multi-week project even for a single
  lemma; the full Kelley–Meka proof is a multi-month project
  comparable to formalizing PNT or Roth's original proof.
- Mathlib lacks the Bohr-set + sifted-Fourier infrastructure that
  underlies the entire Kelley–Meka argument. Building this from scratch
  is its own ~5000-line project.

**Estimated Effort**:
- Approach A: 1 session (~2 hours)
- Approach B: 1–2 sessions (~10 hours)
- Approach C single lemma: 1–2 weeks
- Full Kelley–Meka: multi-month, multi-PR, multi-author project

## References

### Papers

- Behrend, "On sets of integers which contain no three terms in arithmetic progression" (1946)
- Roth, "On certain sets of integers" (1953)
- Bloom & Sisask, "Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions" (2020), arXiv:2007.03528
- Kelley & Meka, "Strong bounds for 3-progressions" (2023), arXiv:2302.05537
- Bloom & Sisask, "An improvement to the Kelley-Meka bounds on three-term arithmetic progressions" (2023), arXiv:2309.02353

### Online Resources

- Terence Tao blog post on Kelley–Meka (2023) — exposition of the proof structure
- Quanta Magazine article (March 2023) — popular overview

### Mathlib

- `Mathlib.Combinatorics.Additive.Corner.Roth` — Mathlib's quantitative Roth via corners
- `Mathlib.Combinatorics.Additive.AP.Three.Defs` — `ThreeAPFree` predicate
- `Mathlib.Combinatorics.Additive.SalemSpencer` — `addSalemSpencer`, `rothNumberNat`
- `Mathlib.Combinatorics.Additive.Behrend` — Behrend's construction (lower bound)
- `Mathlib.Analysis.Convolution` — convolution API (continuous; discrete coverage to be audited)

## Metadata

```yaml
tags:
  - combinatorics
  - additive-combinatorics
  - arithmetic-progressions
  - quantitative-bounds
  - fourier-analysis
related_proofs:
  - szemeredi-theorem
  - szemeredi-regularity
  - szemeredi-counting
  - szemeredi-core-oq-01
difficulty: high
source: user-request
created: 2026-04-05
```

**Significance**: 8/10
**Tractability**: 4/10
