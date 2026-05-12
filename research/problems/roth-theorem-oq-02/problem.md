# Problem: Formalize the Bloom–Sisask bound r₃(N) = O(N / (log N)^{1+c})

## Statement

### Plain Language

Roth's theorem says that any subset of `{1, …, N}` with positive density (i.e.
`|A| ≥ δN` for fixed `δ > 0`) contains a 3-term arithmetic progression once `N`
is large enough. The *quantitative* form asks for the largest possible
3-AP-free subset of `{1, …, N}`, denoted `r₃(N)`.

For decades the best known upper bound stayed at `r₃(N) ≤ N / (log N)^{1 − ε}`
(Bourgain) or `r₃(N) ≤ N · (log log N)^4 / log N` (Sanders, Bloom).
In 2020 **Thomas F. Bloom and Olof Sisask** (arXiv:2007.03528) broke the
"logarithmic barrier" for the first time, proving

$$
r_3(N) \le \frac{N}{(\log N)^{1+c}}
$$

for some absolute constant `c > 0`. Their proof refined the density-increment
strategy on Bohr sets with a quantitative Bogolyubov–Ruzsa lemma that produces
a much larger structured subset than earlier arguments allowed.

The Bloom–Sisask bound was later superseded by **Kelley–Meka (2023)** with
`r₃(N) ≤ N · exp(−c (log N)^{1/12})`, but Bloom–Sisask remains the canonical
"first proof past the log barrier" and a natural mid-strength formalization
target sitting between the elementary Roth bound (`N / log log N`) and the
Kelley–Meka exponential bound (which requires substantial new machinery).

### Formal Statement

In Lean (target shape, not yet formalized):

```lean
/--
**Bloom–Sisask (2020).** There exists an absolute constant `c > 0` such that
for every sufficiently large `N`, every 3-AP-free subset
`A ⊆ ZMod N` (equivalently `A ⊆ {0, …, N-1}`) satisfies
`|A| ≤ N / (log N)^{1 + c}`.
-/
theorem r3_bloom_sisask :
    ∃ c > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ (A : Finset (ZMod N)),
        ThreeAPFree (A : Set (ZMod N)) →
        (A.card : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + c)
```

The companion *direct-integers* formulation uses `A ⊆ Finset.range N` and the
standard 3-AP-freeness notion from `Mathlib.Combinatorics.Additive.AP.Three`.

## Classification

```yaml
tier: B
significance: 7
tractability: 4
tags:
  - combinatorics
  - additive-combinatorics
  - arithmetic-progressions
  - fourier-analysis
  - szemeredi
  - density-increment
  - bohr-sets
  - bogolyubov-ruzsa
  - roth
  - bloom-sisask
  - seeker-selected
  - landmark-formalization
```

**Significance**: 7/10 — first quantitative break past `N / log N`; Bloom and
Sisask received the European Prize in Combinatorics (2021) in part for this
work.

**Tractability**: 4/10 — proof spans ~90 pages of paper math and depends on a
quantitative Bogolyubov–Ruzsa lemma which is **not** in Mathlib v4.26.0.
Realistic S1 OBSERVE deliverable: precise formal statement + literature /
Mathlib survey + roadmap. Full proof formalization is a multi-month,
multi-PR effort and benefits from waiting for Mathlib's Bohr-set
infrastructure to mature.

## Why This Matters

1. **Landmark in additive combinatorics** — first proof past the logarithmic
   barrier for `r₃`, a problem open since Roth (1953).
2. **Stepping stone to Kelley–Meka** — the Bohr-set and Bogolyubov machinery
   formalized here is reused (and refined) by Kelley–Meka 2023.
3. **Mathlib gap-filler** — would force a clean Lean development of
   *Bogolyubov–Ruzsa for `ZMod N`* and *density increment on Bohr sets*, both
   of which are major missing infrastructure pieces flagged in
   `roth-theorem-k3-oq-01` annotations.
4. **Bridges with sibling gallery entries** — `roth-theorem-k3-oq-01` already
   *states* the Bloom–Sisask bound formally (as one of four landmark bounds);
   this slug provides the *proof* target, closing one sorry in that scaffold.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `roth-theorem` | Qualitative Roth: any AP-free set has density `o(1)`. |
| `roth-theorem-k3` | Roth's quantitative bound `r₃(N) = o(N)` via dyadic intervals. |
| `roth-theorem-k3-oq-01` | Bloom–Sisask **stated** (as one of 4 landmark bounds); proof left as a sorry. |
| `roth-theorem-k3-oq-02` | Roth via triangle removal lemma (Ruzsa–Szemerédi). |
| `roth-theorem-k3-oq-03` | Cap set / `ℤ/3ℤ^n` analogue (Croot–Lev–Pach, Ellenberg–Gijswijt). |
| `szemeredi-theorem` | k-AP generalization of Roth (k ≥ 4). |

## References

- T. F. Bloom and O. Sisask, *Breaking the logarithmic barrier in Roth's
  theorem on arithmetic progressions*, arXiv:2007.03528 (2020).
- K. F. Roth, *On certain sets of integers*, J. London Math. Soc. **28** (1953).
- T. Sanders, *On Roth's theorem on progressions*, Annals of Math. **174**
  (2011), 619–636.
- J. Bourgain, *Roth's theorem on progressions revisited*, J. Anal. Math.
  **104** (2008), 155–192.
- Z. Kelley and R. Meka, *Strong bounds for 3-progressions*, arXiv:2302.05537
  (2023).
- Annotations in `src/data/proofs/roth-theorem-k3-oq-01/annotations.json`
  (gallery historical context).
