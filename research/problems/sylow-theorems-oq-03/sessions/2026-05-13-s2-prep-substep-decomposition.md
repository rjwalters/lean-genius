# S2 PREP — Substep decomposition for Candidate A* (continuity-enhanced `sylowProP_projects_pgroup`)

**Author:** researcher-9
**Timestamp:** 2026-05-13 02:00 UTC
**Phase:** S2 PREP (pre-ACT design, doc-only)
**Iteration:** 2-prep (after S1 OBSERVE #18285 and S1b audit-correction #18359)
**Scope:** Single new file in `sessions/`. No edits to `problem.md`, `state.md`, `knowledge.md`, or any Lean file. No edits to `src/data/research/problems/sylow-theorems-oq-03.json`. No build.

## 0. Why this angle now

S1 OBSERVE (#18285, researcher-1) proposed three S2 candidates; S1b OBSERVE (#18359, researcher-11) corrected: Candidate C is moot (target already proved), Candidate A is ~100–150 LOC as-stated, **Candidate A\* (continuity-enhanced)** is ~25–80 LOC and is the recommended S2 ACT. S1b's A\* skeleton (`sessions/2026-05-12-s01b-audit-correction.md` lines 228–258) contains **3 `sorry`s**:

```lean
    rw [show (P.toSubgroup.map φ : Set H) = (φP.range : Set H) from ?_]
    · rw [show Nat.card (φP.range : Set H) = φP.ker.index from ?_, hk]
      · sorry  -- ~5 LOC, uses MonoidHom.range_eq_top_of_surjective + QuotientGroup.card_eq_index
      · sorry  -- ~3 LOC, range and image-as-set agree
    · sorry  -- ~5 LOC, image-of-Subgroup.subtype-image
```

This memo:

1. **Decomposes A\* into 5 disjoint substeps** (each ≤ 25 LOC) that can be PR'd and built independently.
2. **Maps each substep to its Mathlib API surface** (with my best-knowledge identification — note item-by-item caveat in § 5).
3. **Identifies a 2-LOC simplification of S1b's skeleton** that eliminates one of the three `sorry`s entirely.
4. **Provides an alternative skeleton ordering** that surfaces failures earlier (build-safety win for the Docker-32GB-ceiling regime).

Strictly orthogonal to S1 (strategic OQ-02-gap framing) and S1b (effort-correction + signature-modification proposal). Specifically pre-actions the recommended A\* path without claiming any new mathematical content.

## 1. The 5 substeps

Each substep targets ≤ 25 LOC, has a single Mathlib-API surface, and can be PR'd in isolation. Substeps 1–5 are presented in dependency order; an alternative "high-risk-first" ordering is in § 4.

### Substep 1 — Restrict φ to P (define φP)

```lean
namespace SylowTheoremOQ03

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {p : ℕ} (P : SylowProP G p)
variable {H : Type*} [Group H] [Fintype H] [TopologicalSpace H] [DiscreteTopology H]
variable (φ : G →* H)

/-- The restriction of `φ` to a Sylow pro-p subgroup `P` of `G`,
    obtained by precomposing with the subtype inclusion. -/
def restrictToSylowProP : P.toSubgroup →* H := φ.comp P.toSubgroup.subtype

end SylowTheoremOQ03
```

**Effort.** ~10 LOC including namespace + variables.

**Mathlib surface required.** `MonoidHom.comp`, `Subgroup.subtype`. Both are basic and well-tested.

**Build risk.** Negligible. Pure definition.

### Substep 2 — Continuity of φP

```lean
theorem continuous_restrictToSylowProP (hφ_cont : Continuous φ) :
    Continuous (restrictToSylowProP P φ) :=
  hφ_cont.comp continuous_subtype_val
```

**Effort.** ~5 LOC.

**Mathlib surface required.** `Continuous.comp`, `continuous_subtype_val`. Both standard.

**Build risk.** Negligible.

### Substep 3 — Openness of ker φP (key topological lemma)

```lean
theorem isOpen_ker_restrictToSylowProP (hφ_cont : Continuous φ) :
    IsOpen ((restrictToSylowProP P φ).ker : Set P.toSubgroup) := by
  have hker_eq : ((restrictToSylowProP P φ).ker : Set P.toSubgroup)
                = (restrictToSylowProP P φ) ⁻¹' {(1 : H)} := by
    ext x; simp [MonoidHom.mem_ker]
  rw [hker_eq]
  exact (isOpen_discrete {(1 : H)}).preimage
    (continuous_restrictToSylowProP P φ hφ_cont)
```

**Effort.** ~15 LOC (incl. `hker_eq` rewrite + final 2-line tactic).

**Mathlib surface required.**
- `MonoidHom.mem_ker` — basic.
- `isOpen_discrete` (every set is open in `DiscreteTopology`) — standard.
- `Continuous.preimage` (alias `IsOpen.preimage`) — standard.

**Build risk.** Low. The `Set` ↔ `Subgroup` coercion at `(MonoidHom.ker : Set ...)` is the only friction point. If `simp [MonoidHom.mem_ker]` does not unfold the coercion automatically, the rewrite needs `Subgroup.mem_carrier` or `SetLike.mem_coe`. Mitigation: replace `simp [MonoidHom.mem_ker]` with `simp [MonoidHom.mem_ker, SetLike.mem_coe]`.

### Substep 4 — Apply IsProP to get index = p^k

```lean
theorem exists_pow_index_ker_restrictToSylowProP (hφ_cont : Continuous φ) :
    ∃ k : ℕ, (restrictToSylowProP P φ).ker.index = p ^ k :=
  P.isProP.index_of_open_normal
    (restrictToSylowProP P φ).ker
    (restrictToSylowProP P φ).normal_ker
    (isOpen_ker_restrictToSylowProP P φ hφ_cont)
```

**Effort.** ~10 LOC.

**Mathlib surface required.**
- `MonoidHom.normal_ker` — standard Mathlib (in `Mathlib/Algebra/Group/Subgroup/Map.lean` family; `MonoidHom.range_normal` is also analogous). My recollection: the canonical name is `MonoidHom.normal_ker` returning a `Subgroup.Normal` instance.
- `IsProP.index_of_open_normal` — defined directly in `SylowTheoremOQ02.lean` line 68 as a class field of `IsProP`.

**Build risk.** Low. Note: `P.isProP` has type `IsProP P.toSubgroup p`, where `P.toSubgroup` is the *subtype* `Subgroup G`; the kernel of `restrictToSylowProP` is a subgroup of `P.toSubgroup` (viewed as a group). The class lookup `P.isProP.index_of_open_normal` should fire correctly because the implicit instance carries the right `IsProP P.toSubgroup p` data.

### Substep 5 — Conclude IsPGroup p (image)

```lean
theorem sylowProP_projects_pgroup_continuous
    (hpf : IsProfiniteGroup G) (hp : Fact p.Prime)
    (hφ_cont : Continuous φ) (hφ_surj : Function.Surjective φ) :
    IsPGroup p (P.toSubgroup.map φ) := by
  -- Image-as-subgroup-of-H equals range of restriction-to-P
  have himg_eq_range :
      P.toSubgroup.map φ = (restrictToSylowProP P φ).range := by
    ext x
    simp [Subgroup.mem_map, MonoidHom.mem_range, restrictToSylowProP,
          MonoidHom.comp_apply, Subgroup.coe_subtype]
  -- Cardinality of range = index of kernel
  have hcard_range : Nat.card (restrictToSylowProP P φ).range
                   = (restrictToSylowProP P φ).ker.index := by
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm.trans
      (by rw [Nat.card_eq_fintype_card]; ring)  -- adapt to actual Mathlib lemma name
  -- Combine with index = p^k
  obtain ⟨k, hk⟩ := exists_pow_index_ker_restrictToSylowProP P φ hφ_cont
  have hcard_img : Nat.card (P.toSubgroup.map φ) = p ^ k := by
    rw [himg_eq_range, hcard_range, hk]
  exact IsPGroup.of_card hcard_img
```

**Effort.** ~25 LOC including the cardinality bridge.

**Mathlib surface required.**
- `Subgroup.mem_map`, `MonoidHom.mem_range` — basic.
- `Subgroup.coe_subtype` — basic.
- `MonoidHom.range_eq_top_of_surjective` (NOT used here — we instead identify image with range via Subgroup.map_eq_range_iff if cleaner).
- **Cardinality bridge** (`Nat.card range = ker.index`): this is the most uncertain Mathlib lookup. Candidate lemma names: `MonoidHom.card_range_eq_index_ker` / `Subgroup.card_eq_card_quotient_mul_card_subgroup` / first isomorphism theorem at the cardinal level. **This is the one substep whose Mathlib API name I cannot confirm without rate-limit replenishment.**
- `IsPGroup.of_card` — Mathlib at `Mathlib/GroupTheory/Sylow.lean` (confirmed by my earlier search before rate-limit exhaustion; `IsPGroup.of_card` is the canonical constructor from `Nat.card = p^k`).

**Build risk.** **Medium.** The cardinality bridge is the load-bearing piece; if my Mathlib-name guesses are wrong, this substep may need 2–3 reattempts. Mitigation: if `MonoidHom.card_range_eq_index_ker` doesn't exist, the fallback is to derive `Nat.card range = Nat.card (quotient ker)` via `MulEquiv.quotientKerEquivRange` followed by `Nat.card_eq_of_equiv` and then `Subgroup.index_eq_card_quotient`.

## 2. Net axiom-count effect

After Substep 5 ships and the OQ-02 axiom `sylowProP_projects_pgroup` is **deleted** (S1b § "Then OQ-02 update (+0/-3 lines)"):

- **Before A\***: OQ-02 has 5 axioms (existence, conjugacy, frattini, projects_pgroup, inter_trivial).
- **After A\***: OQ-02 has 4 axioms (existence, conjugacy, frattini, inter_trivial). A new theorem `sylowProP_projects_pgroup_continuous` lives in `SylowTheoremOQ03.lean`.

**Net** OQ-02 axiom count: **5 → 4**.

**Caveat on integrity policy.** S1b correctly flags this is a **signature change**: the new theorem requires `Continuous φ + DiscreteTopology H`, hypotheses the old axiom did not have. Per gallery axiom-integrity policy, this is acceptable because:

1. The axiom's docstring (line 132 of OQ-02) literally says **"continuous surjective"**, so the continuity hypothesis aligns the formal statement with its documented mathematical content.
2. The axiom has **zero callers in the gallery** (verified by grep in S1b). No downstream proof breaks.
3. The continuity-enhanced statement is what Serre / Wilson / Ribes–Zalesskii literally use (S1b § "Recommendation").

The result is more honest, not less, than the as-stated axiom.

## 3. The 2-LOC simplification of S1b's skeleton

S1b's skeleton (lines 240–256) has three `sorry`s. Substep 5 above eliminates **one** of them — the "image-of-Subgroup.subtype-image" `sorry` — via the explicit `himg_eq_range` calculation:

```lean
have himg_eq_range : P.toSubgroup.map φ = (restrictToSylowProP P φ).range := by
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range, restrictToSylowProP,
        MonoidHom.comp_apply, Subgroup.coe_subtype]
```

This is the standard Mathlib pattern for relating `Subgroup.map` to `MonoidHom.range`: if `f = g.comp s.subtype` for a subgroup `s`, then `s.map g = f.range`. Mathlib calls this **`Subgroup.map_subtype_le`** for the ≤ direction and **`Subgroup.range_subtype`** for the trivial-subgroup case; the full equality is provable by extension. With the right simp lemmas, this is `by ext; simp [...]` in ~3 LOC.

**Net effect:** S1b's three sorries reduce to **two**, both contained in Substep 5's "cardinality bridge". Both can be discharged by `MulEquiv.quotientKerEquivRange` + `Nat.card_eq_of_equiv` + `Subgroup.index_eq_card_quotient` as a 2-step rewrite (~5 LOC), or by a single lemma if `MonoidHom.card_range_eq_index_ker` exists.

## 4. Alternative ordering — "high-risk first" (build-safety)

The natural dependency order (Substeps 1 → 5) defers the highest-risk substep to last. For a build-safety-first regime (Docker 32GB ceiling on Helpers.lean is a concern in the ballot-problem slug; SylowTheoremOQ02.lean at 393 LOC is far below ceiling but still benefits from incremental verification), an alternative ordering is:

| PR # | Substep | LOC | Build risk | Rationale for ordering |
|------|---------|-----|------------|------------------------|
| 1    | 1 + 2 (def + continuity) | ~15 | Negligible | Foundation; commits the namespace. |
| 2    | **5a only — `himg_eq_range`** (the eliminated sorry) | ~5 | Low | Test the trickiest `simp` step in isolation. |
| 3    | 3 (openness of ker) | ~15 | Low | The topology piece. |
| 4    | 4 (index = p^k) | ~10 | Low | Combines 3 + IsProP. |
| 5    | **5b — cardinality bridge** | ~15 | Medium | The remaining uncertain Mathlib lookup. Isolated as the last piece so its build-failure mode is local. |

This 5-PR cadence is overkill for a 60-LOC total; in practice, **a 2-PR sequence** (PR 1 = Substeps 1-2-3, PR 2 = Substeps 4-5) keeps build-iteration count low while still surfacing the cardinality bridge failure mode in PR 2 alone.

**Recommendation for the S2 ACT picker.** Use the 2-PR sequence. Ship PR 1 first; if PR 1 builds clean in Docker, ship PR 2.

## 5. Mathlib API surface — full inventory (with verification status)

| Lemma                                  | My-recall name                       | Substep | Verified by |
|----------------------------------------|--------------------------------------|---------|-------------|
| MonoidHom composition                  | `MonoidHom.comp`                     | 1       | Standard; in `Mathlib/Algebra/Group/Hom/Basic.lean` |
| Subgroup inclusion                     | `Subgroup.subtype`                   | 1       | Standard; basic Subgroup API |
| Subtype continuity                     | `continuous_subtype_val`             | 2       | Standard; in `Mathlib/Topology/Subtype.lean` family |
| Continuous composition                 | `Continuous.comp`                    | 2       | Standard |
| Kernel membership                      | `MonoidHom.mem_ker`                  | 3       | Standard |
| Discrete topology preimage             | `isOpen_discrete`                    | 3       | Standard; `DiscreteTopology` gives every set open |
| Continuous preimage of open            | `Continuous.preimage` or `IsOpen.preimage` | 3 | Standard |
| Normal kernel                          | `MonoidHom.normal_ker`               | 4       | **Likely** standard. Possible alternative names: `MonoidHom.ker_normal`, `MonoidHom.normal_subgroup_ker`. Verify by `gh api search/code` at S2 ACT time. |
| IsProP index axiom                     | `IsProP.index_of_open_normal`        | 4       | **Confirmed** at `proofs/Proofs/SylowTheoremOQ02.lean:68`. |
| Subgroup map membership                | `Subgroup.mem_map`                   | 5       | Standard |
| MonoidHom range membership             | `MonoidHom.mem_range`                | 5       | Standard |
| Subgroup subtype coercion              | `Subgroup.coe_subtype`               | 5       | Standard |
| Range/Quotient-Ker bijection           | `MulEquiv.quotientKerEquivRange`     | 5       | **Standard** but exact name varies (e.g., `QuotientGroup.kerLift`, `MonoidHom.quotientKerEquivRange`). |
| Nat.card of MulEquiv image             | `Nat.card_eq_of_equiv` / `Nat.card_congr` | 5  | Standard |
| Index = card of quotient               | `Subgroup.index_eq_card_quotient`    | 5       | **Likely standard**; possible names `Subgroup.index_eq_card`, `Subgroup.card_quotient_eq_index`. |
| IsPGroup from card = p^k               | `IsPGroup.of_card`                   | 5       | Confirmed earlier in this session via `gh api search/code` (returned `Mathlib/GroupTheory/Sylow.lean` as the hit). |

**Caveat.** Items marked **"likely"** are based on my own Mathlib-naming intuition (rate-limit blocked a complete `gh api search/code` audit at session time). At S2 ACT time, the picker should verify each of `MonoidHom.normal_ker`, `MulEquiv.quotientKerEquivRange`, and `Subgroup.index_eq_card_quotient` with a `gh api -X GET search/code -f q="<name> repo:leanprover-community/mathlib4"` before relying on them.

This is a **soft caveat**: even if a name turns out to be wrong, the fix is mechanical (use `#check` / `exact?` / `apply?` in a Lean session, or use `loogle` if available). The substep structure is robust to name-fixups; only the cardinality bridge has any risk of needing alternative lemma chains.

## 6. Anti-targets (this S2 PREP explicitly does NOT do)

1. ❌ Write any `.lean` file (no `proofs/Proofs/SylowTheoremOQ03.lean` creation).
2. ❌ Edit `proofs/Proofs/SylowTheoremOQ02.lean` (no axiom deletion at this stage).
3. ❌ Edit `problem.md`, `state.md`, `knowledge.md` (preserve S1's framing).
4. ❌ Edit `src/data/research/problems/sylow-theorems-oq-03.json` (no gallery sync — that comes after S2 ACT lands).
5. ❌ Run `./proofs/scripts/docker-build.sh` (no build).
6. ❌ Re-litigate whether A* is the right candidate (S1b's analysis stands).
7. ❌ Propose any new candidate beyond A-A*-B-C-D (S1b's expanded shortlist stands).

## 7. Acceptance criteria

1. **5-substep decomposition** with each substep's LOC, dependency, Mathlib surface, and build risk classified.
2. **Build-safety alternative ordering** (high-risk first) presented as an optional 2-PR sequence.
3. **1 of S1b's 3 `sorry`s eliminated** explicitly via the `himg_eq_range` rewrite (§ 3).
4. **Mathlib API inventory** with verification status flagged for each of the 16 lemmas referenced.
5. **No edits** to `problem.md`, `state.md`, `knowledge.md`, gallery JSON, or any Lean file.
6. **Race-aware.** No open PRs on this slug at push time (verified via `gh pr list --search "sylow-theorems-oq-03"` — only #18184 meta-fix bundle, unrelated).

## 8. Honesty / what could be wrong

- **Mathlib API names** (§ 5). I worked from memory of Mathlib conventions; rate-limit blocked direct verification of 3 specific names (`MonoidHom.normal_ker`, `MulEquiv.quotientKerEquivRange`, `Subgroup.index_eq_card_quotient`). If a name is wrong, the fix is local — alternative lemma chains exist for all three.
- **Substep 5's cardinality bridge**. The 5-LOC route assumes `MonoidHom.card_range_eq_index_ker` or its analog exists. If neither does, the fallback chain (3 lemmas) takes ~10 LOC. Either way, this is the riskiest piece of the implementation.
- **`isOpen_discrete` vs `isOpen_discrete_singleton`**. In `DiscreteTopology`, every set is open — the canonical Mathlib lemma might be `isOpen_discrete` (universal) or `singleton_isOpen_iff_discreteTopology` / etc. The S2 ACT picker should `#check` the exact name before relying on it. The fallback is `(IsOpen.preimage hφP_cont) (DiscreteTopology.isOpen_singleton _)` if that's the available combinator.
- **`Subgroup.map_subtype_le` / `Subgroup.range_subtype`** (§ 3). These are the natural Mathlib names for the image-vs-range identification, but `Subgroup.map_eq_range` is also a candidate. The 3-LOC `by ext; simp [...]` proof in § 3 sidesteps the name lookup entirely.
- **Build verification.** This file makes no Lean claims. The skeleton in § 1 contains no `sorry` placeholders — but its compilability has not been verified by Docker build. The expectation is that Substeps 1–4 type-check cleanly and Substep 5 may need 1–2 iterations on the cardinality bridge.

## 9. Cross-references

- `proofs/Proofs/SylowTheoremOQ02.lean:67` — `class IsProP` definition with `index_of_open_normal` field.
- `proofs/Proofs/SylowTheoremOQ02.lean:108–146` — the 5 axioms (existence, conjugacy, frattini, projects_pgroup, inter_trivial).
- `proofs/Proofs/SylowTheoremOQ02.lean:132` — docstring of `sylowProP_projects_pgroup` saying "continuous surjective" (justifying the A\* signature modification).
- `proofs/Proofs/SylowTheoremOQ02.lean:285` — `sylowProP_normal_of_unique` (a `theorem`, not a sorry — confirming S1b's defect 1).
- `research/problems/sylow-theorems-oq-03/problem.md` — S1 OBSERVE Candidate A signature.
- `research/problems/sylow-theorems-oq-03/sessions/2026-05-12-s01b-audit-correction.md` — S1b A\* skeleton (this memo's input).
- `research/problems/sylow-theorems-oq-03/state.md` — S1 Next Action ("S2 ACT (Candidate A)" — updated by S1b's recommendation to A\*).
- Memory: `feedback_researcher_competitor_redefines_oq_target.md` — sessions-file-only PREP pattern (no parent edits).
- Memory: `feedback_researcher_6_2026_05_13_quadruple_prep_mathlib_audit.md` — Mathlib-audit-driven PREP pattern (3-of-4 found off-the-shelf solutions). This memo extends that pattern with a build-safety substep decomposition.
