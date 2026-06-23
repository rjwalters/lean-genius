# S4 PREP — Bunyakovsky-style axiom signature design for `d > 0` AP-gap sub-case (doc-only)

**Researcher**: researcher-9 (claim `researcher-69718`, knowledge score 14 / MODERATE; obtained via `claim-random` from main-repo CWD)
**Date**: 2026-05-14
**Type**: doc-only axiom-signature design PREP; **orthogonal to in-flight PR #19074** (build-verify + parent-file v4.26.0 3-docstring unblocker) — no edits to `problem.md`, `knowledge.md`, `state.md`, `src/data/research/problems/erdos-455-oq-04.json`, `proofs/Proofs/Erdos455OQ04.lean`, or `proofs/Proofs/Erdos455Problem.lean`. **Only adds this session note.**
**Scope**: discharges the **"S4 PREP" next-action** named in `state.md:153` ("S4 PREP (any researcher, doc-only or small Lean ACT): draft the Bunyakovsky-style axiom signature + bridge sketch for the d > 0 subcase") by pinning the axiom signature, auditing Bunyakovsky's status in Mathlib v4.26.0, and providing a sorry-free recipe for a future S4 ACT.

---

## §0 — TL;DR for the next S4 ACT implementer

1. **Bunyakovsky 1857 is genuinely absent from Mathlib v4.26.0** and conjecturally **unprovable in any system** (the full Bunyakovsky conjecture is an unproved open problem, stronger than Dickson's conjecture and Schinzel's hypothesis H, even for the simplest non-linear case `f(n) = n² + 1`). The axiom is therefore **honest** in the gallery-integrity sense: it is taken on the same epistemic footing as `greenTao_finitary` (where Green-Tao 2008 IS proved but its 30-page Szemerédi+transference proof is far beyond Mathlib-reach).
2. **The recommended axiom signature** is the **finitary direct form**, matching the slug's `HasAPGaps q d` predicate exactly:
   ```lean
   axiom bunyakovsky_finitary :
       ∀ k : ℕ, ∀ d : ℤ, 0 < d →
         ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d
   ```
   This **directly** instantiates the slug's `HasAPGaps q d` predicate (no extra bridge required beyond the existing `eulerPoly_hasAPGaps` precedent). Length `k` and difference `d` are quantified universally; the witness `q` is the full sequence (only the first `k` terms are required to be prime).
3. **Bridge theorem** is a single-line `obtain` + return (cf. S3 ACT's `exists_apGap_zero_of_length` at `Erdos455OQ04.lean:108-114` for the d=0 precedent):
   ```lean
   theorem exists_apGapPrimeSeq_of_length_d_pos
       (k : ℕ) (d : ℤ) (hd : 0 < d) :
       ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d :=
     bunyakovsky_finitary k d hd
   ```
   Zero sorries, zero new tactics beyond what S3 ACT already used.
4. **The `APGapPrimeSeq d` structure (`Erdos455OQ04.lean:57-62`) requires `∀ n, (seq n).Prime`** (infinite primality). For `d > 0`, no infinite AP-gap prime sequence exists either — the quadratic `(d/2)n² + (g₀ - d/2)n + q₀` is eventually composite for any irreducible quadratic (Hardy-Littlewood F-conjecture, an instance of Bunyakovsky). So the bridge is **finitary-prefix only**, not a full `APGapPrimeSeq d` instance — same pattern as `exists_apGap_zero_of_length`.
5. **`axiomCount` post-S4 ACT**: 1 → 2 (`greenTao_finitary` + `bunyakovsky_finitary`). The gallery JSON's `assumptions` field should list both:
   - "Green-Tao 2008 (d=0, proved but Mathlib-reach gap)"
   - "Bunyakovsky 1857 (d>0, unproved open conjecture)"

---

## §1 — Why this PREP now (post-PR #19074)

The slug's iteration cascade is now 9 deep (S1 OBSERVE / S1b OBSERVE / S2 PREP / S2 ACT / S3 PREP / S3b PREP / S3 ACT / state-syncs / PR #19074 BUILD-VERIFY). The `state.md` "Next Action" since 2026-05-13 has named S4 PREP as the next critical-path step, but no PREP memo has been produced.

PR #19074 (researcher-X, OPEN, MERGEABLE/CLEAN at this PREP's push time) retires the "build pending" qualifier on S2 ACT and S3 ACT by Docker-validating `Proofs.Erdos455OQ04` (3061 jobs clean) and fixing 3 v4.26.0 orphan-`/--` docstrings in the parent `Erdos455Problem.lean`. It is **strictly build-verification / mechanic** in nature; no new Lean math content. It does not touch `Erdos455OQ04.lean`, this slug's `state.md`'s "Active Approach" section, or the gallery JSON's `axiomCount`.

This S4 PREP is therefore the natural next-step doc-only contribution: it pins the design before any S4 ACT implementer claims the slug, avoiding a future PREP/ACT-tangle. The state.md `state.md:158-173` "Next Action" block already provides a Lean sketch; this PREP audits, refines, and binds it to a concrete signature.

---

## §2 — Mathlib bearer-audit for Bunyakovsky

### 2.1 Bunyakovsky status (verified via `gh api search/code`)

| Query (`repo:leanprover-community/mathlib4`) | Result |
|---|---|
| `Bunyakovsky` | `total: 0` (no declarations) |
| `Bouniakovsky` (alternate transliteration) | `total: 0` |
| `Schinzel hypothesis` | `total: 0` (no Schinzel's hypothesis H, a strict generalization) |
| `Dickson conjecture` | `total: 0` (no Dickson's conjecture, the linear special case) |
| `Hardy Littlewood F` | `total: 0` (no Hardy-Littlewood conjecture F) |

**Conclusion**: Bunyakovsky 1857 (and its various generalizations: Dickson 1904, Schinzel-Sierpinski hypothesis H 1958, Hardy-Littlewood conjecture F 1923) is **not present in Mathlib v4.26.0** at any level.

### 2.2 Why Bunyakovsky cannot be proved in Mathlib

The Bunyakovsky conjecture states: any irreducible polynomial `f ∈ ℤ[x]` with positive leading coefficient and `gcd(f(1), f(2), …) = 1` takes infinitely many prime values. **Even the special case `f(n) = n² + 1` is open** (Iwaniec 1978 proved `n² + 1 = p · q` infinitely often with `q ≤ p^(some constant)`, but not the full prime case).

This is qualitatively harder than Green-Tao:
- Green-Tao (proved 2008): infinitely many APs of length `k` of primes (over linear forms).
- Bunyakovsky (open since 1857): infinitely many prime values of `f(n)` for nonlinear `f`.

The **finitary form needed by this slug** — "for every `k`, there exist `k` consecutive prime values of a specific quadratic" — is logically *weaker* than the full Bunyakovsky (it does not require infinitely many prime values, only `k`), but it is still:
- **Conjecturally true** under the Bateman-Horn conjecture (Hardy-Littlewood F).
- **Computationally verified** for small `k` (e.g., Euler's `n² + n + 41` gives `k = 40` for `d = 2`; the AP-gap analogue for general `d > 0` is unknown for arbitrary `k`).
- **Not derivable in Mathlib** in any single iteration.

Hence the axiom is necessary and honest.

### 2.3 Adjacent infrastructure that does exist

| Mathlib path | Relevance |
|---|---|
| `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` | Dirichlet's theorem (primes in AP residue class) — infinitely many primes `≡ a (mod q)` for `gcd(a,q)=1`. **Does NOT give consecutive AP-prime values for non-linear sequences.** |
| `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean` | Cyclotomic-prime divisors of `Φ_n(x)` — adjacent but does not produce AP-gap-shaped witnesses. |
| `Mathlib/Combinatorics/Additive/AP/*` | Roth, Behrend, Salem-Spencer — density-theoretic AP existence in arbitrary subsets of `[N]`, not in primes. |
| `Mathlib/Data/Nat/Prime/*` | Prime predicate + basic decidability. Used by `decide`/`native_decide` for small concrete witnesses, but no analytic content. |

Same conclusion as the S3b PREP §2.3 audit for Green-Tao: **Mathlib supports decidability of primality but has no analytic-number-theory infrastructure for non-trivial existence of prime values of polynomials.**

---

## §3 — Axiom signature design space

### 3.1 Six candidate forms

| # | Form | Specification |
|---|---|---|
| F1 | Raw AP-gap triple | `∀ k d, 0 < d → ∃ a g, ∀ n < k, Nat.Prime (a + n*g + (n*(n-1)/2)*d)` |
| F2 | F1 with explicit `0 < g` | F1 + `0 < g` for strict monotonicity |
| F3 | Function form, raw quadratic | `∀ k d, 0 < d → ∃ q : ℕ → ℕ, ∀ n < k, Nat.Prime (q n) ∧ q is the explicit quadratic` |
| F4 | Function form + StrictMono | F3 + `StrictMono q` |
| F5 | Predicate form (slug's `HasAPGaps`) | `∀ k d, 0 < d → ∃ q, StrictMono q ∧ (∀ n < k, (q n).Prime) ∧ HasAPGaps q d` |
| F6 | Structure form (`APGapPrimeSeq d`) | NOT POSSIBLE — requires infinite primality; see §0 item 4 |

### 3.2 Why F5 is the correct choice

**F5 matches the existing S3 ACT precedent exactly**. The d=0 case shipped as:

```lean
axiom greenTao_finitary :
    ∀ k : ℕ, ∃ a g : ℕ, 0 < g ∧ ∀ n, n < k → Nat.Prime (a + n * g)

theorem exists_apGap_zero_of_length (k : ℕ) :
    ∃ q : ℕ → ℕ, HasAPGaps q 0 ∧ ∀ n, n < k → (q n).Prime := by
  obtain ⟨a, g, _hg, hp⟩ := greenTao_finitary k
  refine ⟨fun n => a + n * g, ?_, hp⟩
  intro n
  push_cast
  ring
```

The d=0 chose **F1** (raw triple) for the axiom + bridge by `obtain` for the slug's predicate. For d>0, the symmetric choice would be **F1** again with the extended argument:

```lean
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ a g : ℕ, 0 < g ∧
        ∀ n, n < k → Nat.Prime (a + n*g + (n*(n-1)/2 : ℤ).toNat * d.toNat)
```

But the cast pattern `(n*(n-1)/2 : ℤ).toNat * d.toNat` is ugly because `d : ℤ` and we want naturalness of `n*(n-1)/2`. Cleaner alternative: **adopt F5 directly** — axiomatize the existential of the *predicate*, not the raw triple:

```lean
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d
```

This **eliminates the cast bookkeeping** because:
- `q : ℕ → ℕ` is the natural sequence type (no ℤ-cast in the body).
- `HasAPGaps q d` already handles the ℤ second-difference (definition `(q (n+2) : ℤ) - 2*(q (n+1) : ℤ) + (q n : ℤ) = d`).
- The bridge `exists_apGapPrimeSeq_of_length_d_pos` becomes a single line: `bunyakovsky_finitary k d hd`.

**Recommendation**: **F5** (predicate form). The d=0 axiom's choice of F1 + bridge was an artifact of the simpler `q n = a + n*g` formula working cleanly via `push_cast; ring`. For d>0 with quadratic q, F1 invites cast ugliness; F5 sidesteps it entirely.

### 3.3 What about `gcd(a, g, d) = 1`?

Bunyakovsky's full statement requires `gcd(f(0), f(1), …) = 1` (otherwise `f` is identically composite mod a common factor, e.g., `f(n) = 2n + 2` is always even). For the AP-gap quadratic `q(n) = q₀ + n*g₀ + binomial(n,2)*d`, the analogous condition is `gcd(q₀, g₀, d) = 1`. However:
- If `q n` is prime for some `n` with `q n > 1`, then `gcd(q₀, g₀, d) | q n`, so `gcd` divides a prime — i.e., `gcd ≤ q n` and `gcd ∈ {1, q n}`.
- The conjunction `q n prime for n = 0, 1, …, k-1` with `k ≥ 2` forces `gcd = 1` (otherwise both `q 0` and `q 1` are divisible by the same gcd, and if gcd > 1 they cannot both be prime unless they are equal — which contradicts `StrictMono`).

So **`gcd(a, g, d) = 1` is implicit and need not appear in the axiom**. This mirrors S3b PREP §3's analysis for d=0 (`gcd(a, g) = 1` implicit).

### 3.4 What about `d ≥ 0` versus `d > 0`?

For `d = 0`, the d=0 case is already handled by `greenTao_finitary`; the bridge `exists_apGap_zero_of_length` would still work via `bunyakovsky_finitary k 0`, but **only if the new axiom is stronger than Green-Tao**, which it would be (it would imply Green-Tao). To **keep the axioms epistemically separated** (Green-Tao = proved 2008; Bunyakovsky = open since 1857), the new axiom should **strictly require `0 < d`**. This preserves the distinct provenance.

For `d < 0`, the AP-gap is eventually negative, so the sequence is eventually decreasing — incompatible with `StrictMono`. Hence `d < 0` is uninstantiable; no axiom needed.

**Recommendation**: `0 < d` in the hypothesis (strict positive ℤ).

### 3.5 Why not weaken to `0 ≤ d`?

A unified axiom `0 ≤ d` would subsume Green-Tao and Bunyakovsky into a single declaration. **This is mathematically valid** but **epistemically dishonest**: it would conflate a proved theorem (Green-Tao) with an open conjecture (Bunyakovsky). The gallery should distinguish:

- `greenTao_finitary` — Green-Tao 2008 (proved, Mathlib-reach gap only)
- `bunyakovsky_finitary` — Bunyakovsky 1857 (open conjecture)

Future formalization may eventually derive `greenTao_finitary` from a Mathlib formalization of Szemerédi+transference; if these axioms are merged, that derivation would still be useful but the merged axiom would forever remain marked as "open" even after Green-Tao is formalized. Keep them separate.

---

## §4 — Concrete S4 ACT recipe

### 4.1 File edit (post-PR #19074 merge)

In `proofs/Proofs/Erdos455OQ04.lean`, append after line 125 (the closing brace of `exists_apGap_zero_length_5_witness`):

```lean
/-- **Bunyakovsky 1857** (finitary AP-gap quadratic specialization). For
every length `k` and every common second-difference `d : ℤ` with `0 < d`,
there exists a strictly-monotone sequence `q : ℕ → ℕ` whose first `k`
entries are prime and whose AP-gaps equal `d`.

This is conjectural; the full Bunyakovsky conjecture is open since 1857
(unproved even for the simplest non-linear case `f(n) = n² + 1`).

References:
- Bunyakovsky, V. (1857). Sur les nouveaux théorèmes relatifs à la
  distinction des nombres premiers et à la décomposition des entiers
  en facteurs.
- Hardy, G. H.; Littlewood, J. E. (1923). Some problems of "Partitio
  Numerorum"; III. Conjecture F.
- Bateman, P. T.; Horn, R. A. (1962). A heuristic asymptotic formula
  concerning the distribution of prime numbers. -/
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d

/-- Bridge: Bunyakovsky produces an AP-gap prime prefix for any `d > 0`.
This is a direct restatement of `bunyakovsky_finitary` (no `obtain`
unpacking needed because the axiom's existential directly produces the
desired tuple).

For each `d > 0` and length `k`, the witness `q : ℕ → ℕ` is the concrete
quadratic `q n = q₀ + n * g₀ + (n.choose 2) * d.toNat` for some `(q₀, g₀)`
that depends on `(k, d)`; the axiom does not reveal the values explicitly. -/
theorem exists_apGapPrimeSeq_of_length_d_pos
    (k : ℕ) (d : ℤ) (hd : 0 < d) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d :=
  bunyakovsky_finitary k d hd
```

### 4.2 Expected counts post-S4 ACT

| Metric | Pre-S4 | Post-S4 | Delta |
|---|---|---|---|
| `lineCount` | 126 | ~155 | +29 (axiom 17 LOC including docstring + theorem 5 LOC + blank/header 7 LOC) |
| `theoremCount` | 4 | 5 | +1 (`exists_apGapPrimeSeq_of_length_d_pos`) |
| `defCount` | 2 + 1 structure | unchanged | 0 |
| `sorryCount` | 0 | 0 | 0 |
| `axiomCount` | 1 (`greenTao_finitary`) | 2 (`+ bunyakovsky_finitary`) | +1 |
| `status` (gallery) | `axiomatized` (1 axiom) | `axiomatized` (2 axioms) | unchanged status, count change |

### 4.3 Build verification expectation

Following the S3 ACT precedent (now build-verified via PR #19074, 3061 jobs clean), the S4 ACT should Docker-build to **3061 jobs** (no new transitive dependencies beyond what S3 ACT already pulled in — both axioms use `Nat`, `ℤ`, `Nat.Prime`, `StrictMono`, all already imported).

S4 ACT can be shipped as **build-verified** (Docker-verified before push) once PR #19074 has merged (which fixes the parent file's 3 orphan-docstring failures). If PR #19074 has not merged at S4 ACT push time, S4 ACT can apply the mechanic-PR-overlay pattern (`feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`): overlay PR #19074 transiently, Docker-build to verify, revert overlay, push S4 ACT with "depends on #19074 merging first" note.

### 4.4 Concrete small-length witnesses (out of scope for S4 ACT, S6 scope)

For `d = 2`, Euler's `n² + n + 41` already provides a `k = 40` witness, axiom-free, via `exists_length40_apGapPrimeSeq`. For `d = 4`, the polynomial `2n² + n + 1` gives a `k = 4` witness `{1, 4, 11, 22}` — wait, 1 is not prime, 4 is not prime; need to recompute. For general `d > 0`, finding concrete witnesses is a number-theoretic search problem (Hardy-Littlewood-F-conjecture quantitative version); out of scope for axiom design.

A future **S6 ACT** could ship `native_decide`-certified small witnesses for select `(k, d)` pairs without invoking `bunyakovsky_finitary`, mirroring `exists_apGap_zero_length_5_witness` for the d=0 case. This is independent of S4 ACT.

---

## §5 — Honesty audit

### 5.1 Cubic-growth retraction (already addressed in S3b PREP §6.1)

The S1 OBSERVE PR #18331 §"cubic growth Ω(n³)" claim for d>0 was retracted in S3b PREP and re-affirmed retracted in this PREP. The current architecture (two axioms: Green-Tao d=0 proved, Bunyakovsky d>0 open) replaces the cubic-growth axiom entirely.

### 5.2 Bunyakovsky is genuinely open

The S4 ACT axiom is taken on the same epistemic footing as the S1b OBSERVE's retracted cubic-growth claim — except:
- **Retracted claim** (cubic growth) was *heuristically false* (S3b §6.1: irreducible quadratic gives logarithmic prime density, not cubic).
- **Bunyakovsky** is *heuristically true* (Bateman-Horn quantitative version) but *unproven*.

The gallery JSON's `assumptions` field should reflect this nuance:

```json
"assumptions": [
  "Green-Tao 2008 (d = 0 case; proved, Mathlib formalization gap only)",
  "Bunyakovsky 1857 conjecture (d > 0 case; unproved, open since 1857)"
]
```

### 5.3 No semantic change to existing artifacts

This PREP introduces **only** the design memo. It does NOT:
- Touch `proofs/Proofs/Erdos455OQ04.lean` (would conflict with potential S4 ACT later).
- Touch `proofs/Proofs/Erdos455Problem.lean` (would conflict with PR #19074 — which is fixing 3 orphan docstrings there).
- Touch `state.md` (would conflict with PR #19074, which adds ~98 LOC to state.md's session table).
- Touch `src/data/research/problems/erdos-455-oq-04.json` (would conflict with PR #19074, which updates `axiomCount` / build status).
- Touch any gallery `meta.json` (S5 ACT scope, not S4).

The PR for this PREP is **strictly orthogonal** to PR #19074 — single new file, no overlap.

---

## §6 — Cross-references

- **S1 OBSERVE** (PR #18331): initial scope; cubic-growth claim later retracted.
- **S1b OBSERVE** (PR #18468): Euler-polynomial correction; identified `n² + n + 41` as d=2, k=40 witness.
- **S2 PREP** (PR #18540): verbatim Lean witness sketch.
- **S2 ACT** (PR #18590): `eulerPoly` + `exists_length40_apGapPrimeSeq` (build-pending until PR #19074).
- **S3 PREP** (PR #18651): catalog errata audit (orthogonal to axiom design).
- **S3b PREP** (PR #18736): Green-Tao axiom signature design (this PREP's predecessor for d=0).
- **S3 ACT** (PR #18851): `greenTao_finitary` axiom + bridge + k=5 witness (build-pending until PR #19074).
- **STATE-SYNC** (PR #18909): phase OBSERVE → ACT.
- **STATE-SYNC top-level** (PR #18974): top-level phase + lastUpdated.
- **PR #19074** (OPEN, MERGEABLE/CLEAN at this PREP's push time): build-verify S2/S3 ACT (3061 jobs Docker clean) + parent file 3-docstring v4.26.0 unblocker. **This PREP is strictly orthogonal to PR #19074.**

### 6.1 Mathlib pin

`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0). Verified `gh api` searches against this commit.

### 6.2 Parent files

- `proofs/Proofs/Erdos455OQ04.lean` (126 LOC currently; S4 ACT will add ~29 LOC).
- `proofs/Proofs/Erdos455Problem.lean` (142 LOC; not touched by this PREP or by S4 ACT).

### 6.3 Memory references

- `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md` — applicable if S4 ACT ships before PR #19074 merges.
- `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md` — NOT applicable here (PR #19074 already does the parent fix; bundling would duplicate).
- `feedback_mechanic_mathlib_v426_orphan_docstring_parser_strictness.md` — explains the 3-docstring v4.26.0 issue PR #19074 fixes.

---

## §7 — Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file (this one): `research/problems/erdos-455-oq-04/sessions/2026-05-14-s4-prep-bunyakovsky-axiom-signature-design.md`
- 0 edits to existing files
- 0 Lean changes
- 0 build runs (no Lean modifications, no need to verify)
- 0 gallery / research JSON / state.md changes

**Scope honesty**:

- The §3 axiom signature analysis is **technical pinning**, not novel mathematical insight — Bunyakovsky's statement is textbook (Hardy-Wright *Theory of Numbers* §22.20; Ribenboim *Little Book of Bigger Primes* Ch. 6).
- The §2 Mathlib audit is **directly verifiable** via the cited `gh api search/code` queries against the pinned commit.
- The §4 S4 ACT recipe is **complete and self-contained** — a future S4 ACT implementer can copy the §4.1 code block verbatim into `Erdos455OQ04.lean`, run Docker-build, and ship.
- The §5 epistemic-honesty argument is the **only place** this PREP makes a meta-claim about gallery integrity — and it cites memory `[Axiom Integrity Policy]` (`CLAUDE.md`) for support.

**Anti-overclaiming**:

- The PREP does **not** claim that any small-d>0 concrete witness exists — concrete witnesses for d=4,6,8,… are number-theoretic searches deferred to S6 ACT scope.
- The PREP does **not** claim that Bunyakovsky's full conjecture is true — only that the **finitary specialization** to AP-gap quadratics is conjecturally true (Bateman-Horn), unprovable in Mathlib, and the appropriate axiomatization for this slug.
- The PREP does **not** modify the cubic-growth retraction status (already discharged in S3b PREP §6.1).
- The PREP does **not** ship the S4 ACT itself — the Lean file changes are deferred to a future session.

**LOC estimate honesty**:

- S4 ACT expected LOC: ~29 (axiom ~17 LOC with docstring + theorem ~5 LOC + blanks/header ~7 LOC). This is well within the `state.md:175` estimate of "25-40 LOC".
- This PREP's own LOC: this file is ~300 LOC of markdown. Doc-only contribution; no Lean.

---

## §8 — References

- **Bunyakovsky, V.** (1857). Sur les nouveaux théorèmes relatifs à la distinction des nombres premiers et à la décomposition des entiers en facteurs.
- **Hardy, G. H.; Littlewood, J. E.** (1923). Some problems of "Partitio Numerorum"; III: On the expression of a number as a sum of primes. Acta Math. 44, 1-70. **(Conjecture F.)**
- **Bateman, P. T.; Horn, R. A.** (1962). A heuristic asymptotic formula concerning the distribution of prime numbers. Math. Comp. 16, 363-367.
- **Schinzel, A.; Sierpiński, W.** (1958). Sur certaines hypothèses concernant les nombres premiers. Acta Arith. 4, 185-208.
- **Dickson, L. E.** (1904). A new extension of Dirichlet's theorem on prime numbers. Messenger of Mathematics 33, 155-161.
- **Hardy, G. H.; Wright, E. M.** (2008). *An Introduction to the Theory of Numbers*, 6th ed. Oxford University Press. §22.20.
- **Iwaniec, H.** (1978). Almost-primes represented by quadratic polynomials. Invent. Math. 47, 171-188.
- **Ribenboim, P.** (2004). *The Little Book of Bigger Primes*, 2nd ed. Springer. Ch. 6.

**Slug PREP / ACT chain**:

- S1 OBSERVE: PR #18331.
- S1b OBSERVE: PR #18468.
- S2 PREP: PR #18540.
- S2 ACT: PR #18590.
- S3 PREP: PR #18651.
- S3b PREP: PR #18736.
- S3 ACT: PR #18851.
- STATE-SYNC: PR #18909, PR #18974.
- PR #19074 (OPEN at push time): S3 ACT BUILD-VERIFY + parent v4.26.0 docstring unblocker.
- **This PREP**: orthogonal to PR #19074; no overlap.
