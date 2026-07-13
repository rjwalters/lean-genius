# Knowledge Base: erdos-29-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Erdős Problem #29** (Sidon 1932, Erdős): Does there exist an explicit additive basis `A ⊆ ℕ` (i.e. `A + A = ℕ`) such that the representation count `r_A(n) := #{(a,b) ∈ A² : a+b = n}` satisfies `r_A(n) = o(n^ε)` for all `ε > 0`?

**Resolved 2024**: Jain–Pham–Sawhney–Zakharov (JPSZ), arXiv:2405.08650 — explicit construction with `r_A(n) ≤ exp(C·√log n)`, which is `o(n^ε)` for every `ε > 0`.

**This OQ (`erdos-29-oq-01`)**: The gallery proof `Erdos29Problem.lean` formalizes the resolution by axiomatizing the 5 key properties of the JPSZ set. Can those 5 axioms be removed by formalizing the JPSZ construction itself in Mathlib?

---

## Axiom map (`Erdos29Problem.lean`)

5 axioms (parent's `axiomCount: 5`):

1. **`JPSZ_set : Set ℕ`** (L158) — the construction.
2. **`JPSZ_is_basis : IsAdditiveBasis JPSZ_set`** (L164) — `A + A = univ`.
3. **`JPSZ_representation_bound`** (L281) — `∃ C, ∀ n ≥ 2, r_A(n) ≤ exp(C·√log n)`.
4. **`JPSZ_explicit : ExplicitSet JPSZ_set`** (L419) — `DecidablePred (· ∈ JPSZ_set)`.
5. **`JPSZ_size_optimal`** (L489) — `∃ C, ∀ N ≥ 1, |A ∩ [1,N]| ≤ C·√N·√log N`.

Derived theorems (not axioms): `JPSZ_is_economical`, `JPSZ_density_zero`, `erdos_29_solved`.

---

## Mathlib bearer audit (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

**Highly relevant**:
- `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` — Explicit `Behrend.sphere`, `Behrend.map`. Roth lower bound `n / exp(O(√log n))` — same scaling family as JPSZ.
- `Mathlib/Combinatorics/Additive/AP/Three/Defs.lean` — `ThreeAPFree`, `rothNumberNat`.
- `Mathlib/Combinatorics/Additive/Energy.lean` — `Finset.addEnergy` for representation-count machinery.

**Moderately relevant**:
- `Mathlib/Combinatorics/Additive/Dissociation.lean` — `AddDissociated` (Sidon-analog).
- `Mathlib/Combinatorics/Additive/Randomisation.lean` — probabilistic random-shift method.
- `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean` — sumset bounds.
- `Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean` — Fourier-on-finite-groups foundations.

**Missing in Mathlib at pinned SHA**:
- ❌ `Sidon` / `B₂[g]` set predicate.
- ❌ `Bₕ[g]` set predicate (h-fold representation bounds).
- ❌ `IsAdditiveBasis` on `Set ℕ` (only group-pointwise sumset notation exists).
- ❌ `representationCount` (`r_A(n)`) for general sets.
- ❌ Anything resembling JPSZ-style algebraic-geometric primitives in `(ℤ/p)²`.

---

## Insights

### Insight 1: The OQ statement is slightly stale
The OQ lists `JPSZ_is_economical` as an axiom, but inspection of `Erdos29Problem.lean:170` shows it is a `theorem` proved from `JPSZ_representation_bound` via squeeze theorem. The actual axiom-removal target is the 5 axioms above.

### Insight 2: Mathlib has Behrend but not the dual
Mathlib's `Behrend.sphere` construction gives a 3-AP-FREE subset of `{1,..,N}` with density `N · exp(−O(√log N))`. The JPSZ construction is morally a DUAL: it gives an ADDITIVE BASIS with representation count `≤ exp(O(√log n))`. Both rely on sphere/base-d encodings. The Behrend infrastructure is the closest existing Mathlib analogue.

### Insight 3: Removing all 5 axioms is out of scope
JPSZ 2024 is research-level mathematics resolving a 90-year-old problem. The construction requires:
- Sidon-Bh primitives in finite fields (not in Mathlib).
- Quantitative sieve estimates adapted to subpolynomial representations.
- Base-decomposition lifting from finite fields to ℕ.

Honest estimate: full formalization is a person-year project. A single researcher session can make doc-only progress (this S1 OBSERVE) and possibly chip away at one sub-goal at a time.

### Insight 4: Sub-goal structure
Axioms #1, #2, #3, #4, #5 are **not independent** in the sense that #2–#5 are all properties OF the set introduced in #1. If a concrete `JPSZSet : Set ℕ` is defined (sub-goal B), then #1 and #4 (decidability) are gone immediately. Axioms #2, #3, #5 then become theorems about a concrete set, but proving them is the hard JPSZ analysis.

### Insight 5: Sub-goal A is independent of `JPSZ_set` itself
A general theorem of the form "any additive basis `A` with `IsEconomical A` satisfies `|A ∩ [1,N]| ≤ C·√N·polylog N`" is a Pigeonhole-style argument depending only on the definitions in `Erdos29Problem.lean`, NOT on the JPSZ construction. This is **tractable in a single Lean session** and would subsume axiom #5 once the concrete construction lands.

### Insight 6: Mathlib's `Behrend` upper bound runs the wrong direction
`Behrend.roth_lower_bound` gives a LOWER bound on Roth numbers (existence of large 3-AP-free sets). The JPSZ bound runs in the OPPOSITE direction for representation counts (UPPER bound on `r_A(n)`). The bearer is structural (sphere/base-d encoding), not theorem-substitution.

### Insight 7: `harmonicSorry` axioms are Aristotle, not Mathlib
The OQ problem statement references "harmonicSorry axioms" — these are placeholder axioms emitted by the Aristotle proof-search system, NOT in Mathlib. The 5 JPSZ axioms in `Erdos29Problem.lean` are clean (no `harmonicSorry` dependencies as inspected; they are direct mathematical statements awaiting formalization).

---

## Sub-goals

See `state.md` § "Sub-goal decomposition" for full details:
- **Sub-goal A**: General `|A ∩ [1,N]|` bound for any economical basis (~50–100 LOC, low risk).
- **Sub-goal B**: Concrete `JPSZSet` via Behrend-like construction (~150–250 LOC, medium risk).
- **Sub-goal C**: Representation-count bound for the candidate (research-level, person-months).

---

## Dead Ends

None yet — this is the OBSERVE session.

Likely future dead ends (based on Mathlib audit):
- Trying to use Mathlib's hash-function libraries (Mathlib has essentially none — hash functions are an ML/CS concept, while JPSZ uses algebraic-geometric explicit constructions).
- Searching for an existing Sidon-set library in Mathlib (does not exist as of pinned SHA).
- Adapting `Randomisation.lean` (probabilistic, on finite abelian groups) — JPSZ is fundamentally deterministic/explicit.

---

## References

- Jain, V., Pham, H. T., Sawhney, M., Zakharov, D. (2024). *Optimal explicit additive bases of small size*. arXiv:2405.08650.
- Sidon, S. (1932). *Ein Satz über trigonometrische Polynome und seine Anwendung in der Theorie der Fourier-Reihen*.
- Erdős, P. *On a problem of Sidon in additive number theory and on some related problems*. J. London Math. Soc. (1944).
- Behrend, F. A. (1946). *On sets of integers which contain no three terms in arithmetical progression*.
- Gowers, T. (2001). *A new proof of Szemerédi's theorem*. GAFA. (Random-shift technique parallels.)
- Mathlib `Behrend.lean` author: Yaël Dillies, Bhavik Mehta (2022).
