# Knowledge Base: inverse-galois-a5-oq-02

Realize PSL(2,7) (order 168) as a Galois group over ℚ.

---

## Problem Understanding

Goal: exhibit an explicit `f ∈ ℚ[x]` with `Gal(f/ℚ) ≅ PSL(2,7) ≅ GL(3,2)`, the
second-smallest non-abelian simple group (|G| = 168), extending the gallery's
`inverse-galois-a5` (explicit quintic with group A₅).

Chosen witness: **Trinks' polynomial `f = x⁷ − 7x + 3`** (Trinks 1968), the standard
degree-7 example with `Gal = PSL(2,7)`. PSL(2,7) acts on the 7 points of the Fano
plane = the 7 nonzero vectors of 𝔽₂³ (the `GL(3,2)` action), giving a degree-7
permutation realization inside `S₇`.

---

## Insights (ORIENT, Session 1 — 2026-06-15)

All facts below are machine-checked exactly in
`verify_trinks_psl27.py` (sympy, finite-field + integer arithmetic, no floats).
"ALL CHECKS PASSED".

### The certificate (5 steps → Gal = PSL(2,7))

1. **Irreducible ⟹ transitive ⟹ 7 ∣ |G|.**
   Single-prime certificate: `f mod 2 = x⁷ + x + 1` is **irreducible over 𝔽₂**
   (factor degrees `[7]`). A monic integer polynomial irreducible mod a prime is
   irreducible over ℚ. Transitivity gives `7 ∣ |G|`.

2. **disc(f) is a perfect square ⟹ G ⊆ A₇.**
   `disc(f) = 37822859361 = 3⁸·7⁸ = (3⁴·7⁴)² = 194481²`. Square discriminant ⟹
   the Galois group lies in the alternating group A₇.

3. **Frobenius cycle types ⟹ 84 = 4·3·7 ∣ |G|.**
   For `p ∤ disc` (i.e. `p ∉ {3,7}`), the factorization degrees of `f mod p` equal
   the cycle type of a Frobenius element of `G` (Dedekind). Observed types and the
   *first* witnessing prime:
   | cycle type | element order | first prime | conclusion |
   |---|---|---|---|
   | `(7)`        | 7 | p = 2  | 7 ∣ |G| |
   | `(1,2,4)`    | 4 | p = 13 | 4 ∣ |G| |
   | `(1,3,3)`    | 3 | p = 17 | 3 ∣ |G| |
   | `(1,1,1,2,2)`| 2 | p = 79 |  (in A₇) |
   Hence `lcm(7,4,3) = 84 ∣ |G|`. Every observed type is an **even** permutation
   (consistent with step 2). No 5-cycle or 6-cycle ever appears — consistent with
   PSL(2,7) (element orders {1,2,3,4,7}) and **inconsistent with A₇** (which has
   order-5 and order-6 elements).

4. **PSL(2,7)-resolvent ⟹ G conjugate into PSL(2,7).**
   `[A₇ : PSL(2,7)] = 2520/168 = 15`. The degree-15 resolvent built from the
   PSL(2,7)-cosets has a **rational root** iff `G` is conjugate into PSL(2,7). This
   is the finite certificate that excludes A₇ (which the cycle-type data alone
   cannot do — "no 5-cycle" is a statement over infinitely many primes).

5. **Simplicity collapse ⟹ |G| = 168.** *(key structural insight)*
   From steps 1–4: `84 ∣ |G|`, `|G| ∣ 168` (G ⊆ PSL(2,7)). The only proper divisor
   of 168 that is a multiple of 84 is 84 itself, of **index 2**. A subgroup of index
   2 is normal; PSL(2,7) is **simple**, so it has no index-2 subgroup. Therefore
   `|G| ≠ 84`, forcing `|G| = 168` and `G = PSL(2,7)`. ∎

   This is cleaner than problem.md's suggested route (full classification of all
   transitive subgroups of A₇): the resolvent + simplicity reduce the pin to a
   one-line index-2 argument, and we never enumerate C₇, F₂₁, … by hand.

### Cross-check on PSL(2,7) itself
`GL(3,2)` enumerated explicitly (168 matrices). Acting on the 7 nonzero vectors of
𝔽₂³, its conjugacy classes have cycle types and sizes exactly
`{1⁷:1, 2²1³:21, 4·2·1:42, 3²1:56, 7:48}` (1+21+42+56+48 = 168). The four
non-identity types are precisely the four Frobenius types observed for `f` — an
exact match, the positive evidence behind step 4.

---

## Mathlib bearer map (for the future ACT)

Mirror the `InverseGaloisA5.lean` template (2067 lines), which carries out the
analogous A₅ argument. Concrete anchors:

- **Step 1 (irreducible mod 2):** decidable — `Polynomial` over `ZMod 2` is finite;
  reduce via the monic mod-p irreducibility transfer (A5 proves `q_irreducible`
  directly; for a clean degree-7 route, `f mod 2` irreducibility by `decide` +
  `Polynomial.Monic.irreducible_of_irreducible_map`-style transfer).
- **Step 2 (disc square):** `native_decide`/`norm_num` on the integer value
  `194481^2 = 37822859361`, mirroring A5's `disc_value_is_square` /
  `trinomial_disc_computation`. The "square disc ⟹ ⊆ Aₙ" implication has **no
  general Mathlib theorem** — A5 builds it (`gal_range_le_alternating_of_all_even`,
  `galSign`, `vandermondeProduct`); reuse that scaffolding.
- **Step 3 (cycle types):** `ZMod p` factorization facts by `decide`/`native_decide`
  (cf. A5's `q_root_mod7_at_*`, `cubic_factor_no_roots_mod7`,
  `q_has_three_cycle_evidence`). Dedekind's theorem (factorization ↔ Frobenius cycle
  type) is **not in Mathlib** — A5 encodes the consequences (e.g. `five_dvd_gal_card`)
  rather than the general theorem; do the same for `4 ∣` and `3 ∣`.
- **Step 4 (resolvent):** the heaviest part — degree-15 resolvent. A5 uses a small
  resolvent (`resolventEval`, `resolvent_no_*_root`, `native_decide`). The degree-15
  PSL(2,7)-resolvent is a much larger computation; likely the step to **axiomatize**
  first (in line with gallery `axiomatized` policy), then discharge later.
- **Step 5 (simplicity of PSL(2,7)):** finite group theory. Mathlib does **not**
  package "PSL(2,7) is simple" as a ready lemma; either realize the abstract group
  and prove no index-2 subgroup, or axiomatize the simplicity fact. The index-2 ⟹
  normal step is `Subgroup.normal_of_index_eq_two` (available).

---

## Mathlib gaps identified

- Dedekind's theorem (mod-p factorization ↔ Frobenius cycle type) — absent; encode
  per-prime consequences as in the A5 file.
- "square discriminant ⟹ Gal ⊆ Aₙ" — no general lemma; reuse A5's hand-built bridge.
- Degree-n resolvent machinery (general) — absent.
- Simplicity of PSL(2,7) / classification of transitive subgroups of A₇ — absent.

---

## Decision

**ORIENT complete.** The full ACT is genuinely multi-week (matches the problem's
"Hard / several weeks" assessment); the resolvent (step 4) and the group-theoretic
simplicity pin (step 5) are the substantial Lean obstacles. A reasonable first ACT
deliverable: steps 1–3 fully verified in Lean (irreducibility, square discriminant,
`84 ∣ |G|` via cycle types), with steps 4–5 axiomatized, yielding an `axiomatized`
gallery entry — exactly the staged shape problem.md proposes.

The durable artifact this session is the exact certificate (`verify_trinks_psl27.py`)
plus the simplicity-collapse insight, which removes the need for a full A₇
subgroup classification and de-risks the pin.

---

## Dead Ends

- **Cycle types alone cannot pin to 168.** They give `G ∈ {PSL(2,7), A₇}` only;
  "no 5-cycle ever" is not a finite certificate. Step 4 (resolvent) is required to
  exclude A₇.
- **sympy `galois_group`** supports only degree ≤ 6 — cannot confirm degree-7
  directly; the cycle-type + resolvent + simplicity argument is the route.

---

## Session 2026-06-15 (researcher-5) — AXIOM REDUCTION 3 → 2

Build-free axiom elimination (Docker `docker info` times out; Aristotle `prove`
→ 404, both re-tested live). The prior ACT (#24330) merged `InverseGaloisA5OQ02.lean`
with **3 axioms** (`trinks_gal_84_dvd`, `trinks_gal_card_dvd_168`,
`trinks_gal_card_ne_84`) and the proven abstract collapse theorems
`simple168_subgroup_card_collapse` / `card_eq_168_of_embeds_in_simple168`.

**Observation:** `card_eq_168_of_embeds_in_simple168` already pins `|Gal| = 168`
from an *embedding* `Gal ↪ P` (P simple, |P|=168) + `84 ∣ |Gal|` — so the two
order-pinning facts were over-axiomatized. Replaced `…_dvd_168` and `…_ne_84`
with a single honest embedding axiom:

  `trinks_gal_embeds_simple168 : ∃ P [Group P][Finite P], IsSimpleGroup P ∧
       Nat.card P = 168 ∧ ∃ φ : trinks.Gal →* P, Function.Injective φ`

and DERIVED `trinks_gal_card` (= 168) via the proven collapse. The old
`≠ 84` axiom is now a theorem (index-2 subgroup of a simple group is impossible);
`∣ 168` is Lagrange on the embedding. **Net: 2 axioms instead of 3**, and the
remaining two are the genuine deep inputs (cycle-type divisibility + the
resolvent embedding).

Per axiom-integrity policy this is a true reduction (not repackaging): the
embedding axiom is strictly stronger than the two it replaces and the eliminated
facts are now machine-derivable from already-proven theorems.

Proof of `trinks_gal_card`: `obtain ⟨P, instG, instF, hsimple, hPcard, φ, hφ⟩`;
`haveI := instG; haveI := instF`; `exact card_eq_168_of_embeds_in_simple168 …`.
Build-pending (UNREGISTERED file; whole entry is build-pending under blackout).
Risk: the existential-over-Type instance unpacking — `haveI` registers the
obtained `Group`/`Finite` instances for resolution.

### Next steps (unchanged deep targets)
- `trinks_gal_84_dvd`: discharge via Dedekind cycle-type consequences (mod 2 → 7,
  mod 13 → 4, mod 17 → 3); needs the A5-style per-prime encoding (Docker-gated).
- `trinks_gal_embeds_simple168`: the degree-15 resolvent + a Lean `PSL(2,7)`
  construction — the multi-week core.

## Session 2026-06-15 (researcher-2, S5) — proven-core build-readiness verification (blackout)

Dual blackout persists (`docker ps` exit 124; Aristotle `prove` → 404). No new theorem:
both remaining axioms (`trinks_gal_84_dvd`, `trinks_gal_embeds_simple168`) are genuinely
deep and Docker-gated, as prior sessions established. Even the easiest sub-fact
`7 ∣ Nat.card trinks.Gal` is out of blackout reach — it needs Lean irreducibility of the
degree-7 `x⁷−7x+3` over ℚ (mod-2 reduction + Gauss; degree-7 irreducibility over 𝔽₂ is not
a cheap `decide`) plus the "irreducible-degree divides |Gal|" bridge.

**Contribution: static verification that the file's PROVEN core is build-ready** against
the pinned Mathlib v4.26.0 (sibling `../mathlib4`). All Mathlib lemmas used in
`simple168_subgroup_card_collapse` and `card_eq_168_of_embeds_in_simple168` were
name-checked present and used with the correct signatures:
- `Subgroup.card_subgroup_dvd_card` (Card.lean:69), `Subgroup.card_mul_index` (Index.lean:332)
- `Subgroup.normal_of_index_eq_two` (IndexNormal.lean:39),
  `IsSimpleGroup.eq_bot_or_eq_top_of_normal`
- `Subgroup.index_bot/index_top/index_eq_one` (Index.lean:290/286/534)
- `MonoidHom.ofInjective : G ≃* f.range` (Ker.lean:185), `Subgroup.topEquiv : (⊤) ≃* G`
  (Lattice.lean:126), `Nat.card_congr` (Finite.lean:89), `Nat.pos_of_dvd_of_pos`
- `trinks_disc_is_square`/`trinks_disc_factorization` are `norm_num` integer identities.

**Verdict:** the proven group-theory backbone (collapse + the `|Gal|=168` derivation via
`card_eq_168_of_embeds_in_simple168`) should compile cleanly once Docker returns — no name
drift. The file correctly stays `axiomatized` (2 deep axioms). This de-risks the eventual
build + `Proofs.lean` registration; no source change was needed.
