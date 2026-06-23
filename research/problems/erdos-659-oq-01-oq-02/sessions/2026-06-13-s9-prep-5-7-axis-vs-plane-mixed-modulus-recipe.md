# Session — S9 PREP: `(5, 7)` axis-vs-plane safety (mixed-modulus recipe)

**Slug.** `erdos-659-oq-01-oq-02`
**Researcher.** researcher-2
**Date.** 2026-06-13
**Mode.** PREP (doc-only; no `.lean` / `meta.json` edits).
**Iteration.** 16 (after S8 ACT, Iteration 15).

## 1. Why a PREP (and why this is *not* a routine analog)

S8 ACT (researcher-1, 2026-06-09) discharged `(2, 13)`, the 3rd of the
seven safe pairs `{(2,5),(2,13),(3,5),(5,7),(5,13),(7,13),(11,13)}` from
S2a OBSERVE PR #18494. The S8 next-action menu lists `(5, 7)` as item 1:

> **`(5, 7)` axis-vs-plane safety** — needs mod-7 reduction (49-case
> `decide` per helper). Lowest new-API surface remaining.

**This PREP corrects that characterisation.** The `(2,5)/(3,5)/(2,13)`
discharges all worked by reducing every equation **mod the larger prime
`q`**, because for those pairs both `q` and `−p` / `p` land on
non-residues mod `q`. **For `(5, 7)` the uniform mod-`q=7` route fails on
equation A**, because `−5 ≡ 2 (mod 7)` is a *quadratic residue* mod 7.
The fix is a **mixed-modulus** discharge (eq A and C reduce mod 5, eq B
reduces mod 7), which has the pleasant side effect of needing **only one
new helper**, not two. Details below.

This is exactly the kind of subtlety that must be settled on paper before
an ACT: a blind "mod-7 analog of (2,13)" paste would not elaborate.

**Build constraint.** Docker is **down** on this host (`docker
info`/`version` hang) and the worktree `.lake` symlink loop persists, so
no `decide`/`lake build` could be run this session. Every QR fact and
descent step below is **hand-computed** and explicitly flagged; the new
`decide` helper and the full file MUST be Docker-verified before/at the
S10 ACT paste.

## 2. The `(5, 7)` equations

`SafePrimePair_AxisVsPlane p q` (file line 318) unfolds at `(p,q)=(5,7)`
to three integer equations, each asserting only the trivial solution:

```
(A)   7 c² = a² + 5 b²
(B)   5 b² = a² + 7 c²
(C)   a²   = 5 b² + 7 c²
```

## 3. Quadratic-residue tables (hand-computed — VERIFY with `decide`)

```
squares in ZMod 5 = {0, 1, 4}        non-residues = {2, 3}
squares in ZMod 7 = {0, 1, 2, 4}     non-residues = {3, 5, 6}
```

(Mod 7: 1²=1, 2²=4, 3²=2, 4²=2, 5²=4, 6²=1.)

Relevant facts:
- `2` is a **non-residue** mod 5  → drives eq A and eq C (since `7 ≡ 2 (mod 5)`).
- `5` is a **non-residue** mod 7  → drives eq B.
- `−5 ≡ 2` is a **residue** mod 7 → this is *why* the uniform mod-7
  route fails for eq A, forcing the mixed-modulus choice.

## 4. Per-equation modulus selection and the descent

For each equation, reduce modulo the prime that makes the *isolated*
square's coefficient vanish, so the surviving relation is
`a² ≡ (non-residue) · (other)²` and forces both ≡ 0.

| Eq | Reduce mod | Surviving relation | Helper | Forces | Then derive | Descend on |
|----|-----------|--------------------|--------|--------|-------------|------------|
| A `7c²=a²+5b²` | **5** (kills `5b²`) | `a² ≡ 2c² (mod 5)` | `zmod_5_a_sq_eq_two_b_sq_iff` *(EXISTING, line 82)* | `5∣a, 5∣c` | `5∣b` | `c.natAbs` |
| B `5b²=a²+7c²` | **7** (kills `7c²`) | `a² ≡ 5b² (mod 7)` | `zmod_7_a_sq_eq_five_b_sq_iff` *(NEW)* | `7∣a, 7∣b` | `7∣c` | `b.natAbs` |
| C `a²=5b²+7c²` | **5** (kills `5b²`) | `a² ≡ 2c² (mod 5)` | `zmod_5_a_sq_eq_two_b_sq_iff` *(EXISTING, line 82)* | `5∣a, 5∣c` | `5∣b` | `a.natAbs` |

**Key efficiency finding: only ONE new helper is required.** Equations A
and C both reduce mod 5 to `a² ≡ 2c²` (because `7 ≡ 2 (mod 5)`), reusing
the existing `zmod_5_a_sq_eq_two_b_sq_iff` with the second slot bound to
`c`. Only equation B needs the new mod-7 helper. No `_plus_`-form helper
is needed at all (the eq-A `a²+5b²≡0` form is unusable mod 7, and mod 5
it becomes the `_eq_`-form instead).

This differs structurally from S4/S7/S8: there the helper handed back the
two *non-isolated* variables `(a,b)` and the third was derived; here for
A and C the helper hands back `(a,c)` and `b` is derived. The descent
variable is still the isolated LHS variable (so the base case is a clean
"sum of non-negatives = 0").

## 5. The new helper (paste-ready; VERIFY `decide`)

Insert alongside the existing mod-5/mod-13 helpers (after line ~121):

```lean
/-- **(S10 ACT, mod-7 step for equation B on the prime pair `(5, 7)`)**
    `a² ≡ 5 b² (mod 7)` iff both `a ≡ 0` and `b ≡ 0` in `ZMod 7`.
    Equivalent to the assertion that `5` is not a square in `ZMod 7`
    (squares mod 7 are `{0, 1, 2, 4}`; `5` is not among them).
    49-case `decide` check. -/
lemma zmod_7_a_sq_eq_five_b_sq_iff (a b : ZMod 7) :
    a ^ 2 = 5 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide
```

## 6. Paste-ready descent theorems (skeletons — mirror existing, VERIFY)

All three mirror the **Docker-verified** `safe_{A,B,C}_3_5_holds` /
`safe_{A,B,C}_2_13_holds` template (file lines 348–681). The deltas from
that template are only: (i) the modulus and helper named in §4, (ii) the
order in which the helper's two outputs map to variables, (iii) the
derived-divisibility algebra. The `Nat.strong_induction_on` skeleton,
base case, `ZMod.intCast_zmod_eq_zero_iff_dvd`, `Prime.dvd_of_dvd_pow`,
and `Int.natAbs_mul` measure-decrease are **verbatim** from the template.

### 6.1 Equation A — `safe_A_5_7_holds` (reduce mod 5)

```lean
theorem safe_A_5_7_holds :
    ∀ a b c : ℤ, (7 : ℤ) * c ^ 2 = a ^ 2 + 5 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ n : ℕ, ∀ a b c : ℤ, c.natAbs = n →
      (7 : ℤ) * c ^ 2 = a ^ 2 + 5 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c hc heq
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · -- base: c = 0  ⟹  0 = a² + 5 b²  ⟹  a = b = 0
        have hc0 : c = 0 := Int.natAbs_eq_zero.mp (by omega)
        subst hc0
        refine ⟨?_, ?_, rfl⟩
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a))
        · exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b))
      · -- mod 5: a² ≡ 2 c²  (note 7 ≡ 2, 5 b² ≡ 0)
        have hz : (a : ZMod 5) ^ 2 = 2 * (c : ZMod 5) ^ 2 := by
          have h : ((a ^ 2 + 5 * b ^ 2 : ℤ) : ZMod 5) = ((7 * c ^ 2 : ℤ) : ZMod 5) := by
            rw [heq]
          push_cast at h
          -- 5 ≡ 0, 7 ≡ 2 in ZMod 5; rearrange h to a² = 2 c²
          rw [show (5 : ZMod 5) = 0 from by decide,
              show (7 : ZMod 5) = 2 from by decide, zero_mul, add_zero] at h
          linear_combination -h          -- VERIFY: orient a² = 2 c²
        rw [zmod_5_a_sq_eq_two_b_sq_iff] at hz       -- hz : (a:ZMod5)=0 ∧ (c:ZMod5)=0
        have hda : (5 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp hz.1
        have hdc : (5 : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mp hz.2
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨c', rfl⟩ := hdc
        -- derive 5 ∣ b from 7 c² = a² + 5 b²  ⟹  5 b² = 25(7c'² - a'²)
        have h5b : (5 : ℤ) * b ^ 2 = 5 * (5 * (7 * c' ^ 2 - a' ^ 2)) := by
          linear_combination heq          -- VERIFY coefficient/sign
        have hb2 : b ^ 2 = 5 * (7 * c' ^ 2 - a' ^ 2) :=
          mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5b
        have hdb : (5 : ℤ) ∣ b := by
          have hp : Prime (5 : ℤ) := by norm_num
          exact hp.dvd_of_dvd_pow (⟨7 * c' ^ 2 - a' ^ 2, hb2⟩ : (5 : ℤ) ∣ b ^ 2)
        obtain ⟨b', rfl⟩ := hdb
        -- reduced equation 7 c'² = a'² + 5 b'²
        have heq' : (7 : ℤ) * c' ^ 2 = a' ^ 2 + 5 * b' ^ 2 := by
          have h25 : (7 : ℤ) * (5 * c' ^ 2) = 5 * (a' ^ 2 + 5 * b' ^ 2) := by
            linear_combination hb2          -- VERIFY
          exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h25
        have hmeas : c'.natAbs < n := by
          have h5nat : (5 : ℤ).natAbs = 5 := by decide
          rw [Int.natAbs_mul, h5nat] at hc
          omega
        obtain ⟨ha0, hb0, hc0⟩ := ih c'.natAbs hmeas a' b' c' rfl heq'
        subst ha0; subst hb0; subst hc0
        refine ⟨by ring, by ring, by ring⟩
  intro a b c heq
  exact key c.natAbs a b c rfl heq
```

### 6.2 Equation B — `safe_B_5_7_holds` (reduce mod 7, NEW helper)

1:1 with `safe_B_2_13_holds` (line 575) but mod 7 and the new helper:
- descend on `b.natAbs`; base case `b = 0 ⟹ 0 = a² + 7c² ⟹ a = c = 0`;
- `hz : (a:ZMod 7)^2 = 5 * (b:ZMod 7)^2` from `5b²=a²+7c²` (use
  `show (7 : ZMod 7) = 0 from by decide`, `zero_mul`, `add_zero`);
- `rw [zmod_7_a_sq_eq_five_b_sq_iff] at hz` → `7∣a, 7∣b`;
- derive `7∣c` from `5b²=a²+7c² ⟹ 7c² = 5b²−a² ⟹ 7c² = 25·…` after
  substituting `a=7a', b=7b'`; `Prime (7:ℤ)` via `by norm_num`;
- reduced eq `5 b'² = a'² + 7 c'²`; measure `b'.natAbs < n`.

### 6.3 Equation C — `safe_C_5_7_holds` (reduce mod 5, EXISTING helper)

1:1 with `safe_C_2_13_holds` (line 627) but mod 5 / `_eq_two_` helper:
- descend on `a.natAbs`; base case `a = 0 ⟹ 0 = 5b² + 7c² ⟹ b = c = 0`;
- `hz : (a:ZMod 5)^2 = 2 * (c:ZMod 5)^2` from `a²=5b²+7c²` (mod 5:
  `5b²≡0`, `7≡2`);
- `rw [zmod_5_a_sq_eq_two_b_sq_iff] at hz` → `5∣a, 5∣c`;
- derive `5∣b`; substitute; reduced eq `a'² = 5 b'² + 7 c'²`; measure
  `a'.natAbs < n`.

### 6.4 The composite

```lean
/-- **The main axis-vs-plane safety theorem for the prime pair `(p, q) = (5, 7)`.** -/
theorem safe_5_7_axis_vs_plane : SafePrimePair_AxisVsPlane 5 7 :=
  ⟨safe_A_5_7_holds, safe_B_5_7_holds, safe_C_5_7_holds⟩
```

## 7. Estimated ACT delta (S10)

- +1 helper lemma (`zmod_7_a_sq_eq_five_b_sq_iff`, ~6 LOC + docstring).
- +3 descent theorems (~50 LOC each) + 1 composite.
- File ~683 → ~860 LOC; `theorem`s 12 → 16; `lemma`s 6 → 7.
- 0 sorries / 0 axioms delta.
- Cumulative safe pairs: 4/7 → if landed, but note 5/7 already counting
  this would make it the **4th** discharged pair.

## 8. Failure-mode register (because nothing was build-verified)

1. **`linear_combination` coefficients/signs** in §6.1 (`hz` orientation,
   `h5b`, `h25`) are the only unverified algebra. If a step fails, run
   `nlinarith [sq_nonneg …]` or flip the sign / adjust the scalar; the
   true identities are `5b² = 25(7c'²−a'²)` and `7·5c'² = 5(a'²+5b'²)`.
2. **`show (7 : ZMod 5) = 2 from by decide`** — if `decide` is slow or
   the coercion mismatches, use `by norm_num` or `by rfl`.
3. **New helper `decide`** — 49 cases, trivially fast; if `revert a b;
   decide` strains, `Finset`-enumerate via `Decidable.decide` is the
   fallback (not expected).
4. **QR facts** (§3) hand-computed — the `decide` helper *is* the machine
   check; if it fails to close, the residue table is wrong and the whole
   `(5,7)` discharge must be re-derived (low risk: `5 ∉ {0,1,2,4}` is
   immediate).

## 9. Race-safety log

- **Pre-claim probe**: `gh pr list --search "erdos-659 in:title"
  --state open` → (to confirm at ACT) 0 open PRs on this slug expected.
- **Pre-edit probe**: `proofs/Proofs/Erdos659OQ01OQ02.lean` byte-identical
  to `origin/main` at session start; this PREP makes **no** `.lean` edit.
- **Branch**: doc-only work on `research/erdos-659-oq-01-oq-02-s9-prep-5-7`
  off `origin/main` (`fa1c4d27aa8`).

## 10. Next action register

- **Immediate (S10 ACT, Docker-available session)**: paste §5 + §6,
  `./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02`, apply §8
  fallbacks, commit + PR. The mixed-modulus correction in §1/§4 is the
  load-bearing insight — do **not** attempt a uniform mod-7 paste.
- **After `(5,7)`**: `(5,13)` (reuses mod-13 helpers carrying coeff `2`?
  — re-audit: `(5,13)` equations carry coeff `5`, and `−5`/`5` mod 13
  must be re-checked; `(5,13)` likely also mixed-modulus since `13 ≡ 3
  (mod 5)` and `5 ≡ 5 (mod 13)`), then `(7,13)`, `(11,13)`.
- **Blocked (deferred)**: full-rank safety (ternary Hasse-Minkowski, not
  in Mathlib v4.26.0) and the Θ(n^{2/3}) assembly.

## 11. Iteration history extension

| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|----|
| 15 | ACT | `.lean` | (S8) | `(2,13)` axis-vs-plane discharged; Docker GREEN. |
| **16** | **PREP** | **doc** | **(this)** | **S9 PREP: `(5,7)` mixed-modulus recipe. Corrects the menu's "mod-7 analog" assumption — eq A's `−5 ≡ 2` is a QR mod 7, so eq A/C reduce mod 5 (reusing `zmod_5_a_sq_eq_two_b_sq_iff`) and only eq B needs the new `zmod_7_a_sq_eq_five_b_sq_iff`. ONE new helper, not two. Doc-only (Docker down); paste-ready skeletons + failure register in §5–§8.** |
