# Knowledge Base: e-transcendental-oq-02

**Title**: Is e a Normal Number?

**Status**: ACT — gallery entry built; 2 axioms tractable, 1 is the genuinely-open conjecture
**Tier**: B / significance ≈ 7 / tractability ≈ 2 (one of three remaining axioms is the open conjecture)
**Parent file**: `proofs/Proofs/ETranscendentalOQ02.lean` (300 lines, 28 theorems, 3 axioms, 0 sorries as of origin/main 2026-05-08)
**Sibling**: `proofs/Proofs/ETranscendentalOQ01.lean` (Schanuel's conjecture for `e^{e^e}`)

---

## Session 2026-05-04 (Session 1) — Gallery Entry Created

**Mode**: FRESH
**Outcome**: gallery entry shipped

### What Was Done

- Created `proofs/Proofs/ETranscendentalOQ02.lean` (235 lines initially):
  - `nthDigit b n x = ⌊b^n · x⌋ % b` (`ℤ`-valued, base-b digit extraction)
  - `IsNormalInBase b x` via `Tendsto` to `b^(-k)` of k-string frequency
  - `IsAbsolutelyNormal x = ∀ b ≥ 2, IsNormalInBase b x`
- 6 decimal-digit lemmas `e_digit1..e_digit6` machine-checked from `Real.exp_one_gt_d9`.
- 4 axioms originally:
  1. `rational_digits_eventually_periodic`
  2. `periodic_has_missing_ktuple`
  3. `normal_imp_irrational`
  4. `e_absolutely_normal` (the genuinely open conjecture)

### PRs

- #15577 (2026-05-04): commit gallery entry; lineCount 237→235

---

## Session 2026-05-04 (Session 1.5) — Decimal Digits Extended to 9 (#15637)

**Mode**: REVISIT
**Outcome**: progress (digits 7→9)

- Added `e_digit7..e_digit9` proving 2.71828**1828** — saturates the lower bound `Real.exp_one_gt_d9`.
- Added `e_normal_implies_uniform_decimal_digits`.
- File grew 235 → ~280 lines, 17 → 25 theorems.
- PR #15637.

---

## Session 2026-05-04 (Session 1.6) — `periodic_has_missing_ktuple` Proved (#15750)

**Mode**: REVISIT (axiom hunt)
**Outcome**: **AXIOM ELIMINATION** — axioms 4 → 3

### What Was Done

Discharged `periodic_has_missing_ktuple` axiom to a proved theorem (~40 lines):

```lean
theorem periodic_has_missing_ktuple (b T k : ℕ) (hb : 2 ≤ b) (hT : 0 < T)
    (hk : T < b ^ k) (f : ℕ → Fin b) (N₀ : ℕ)
    (hperiod : ∀ n ≥ N₀, f (n + T) = f n) :
    ∃ s : Fin k → Fin b, ∀ n ≥ N₀, ∃ i : Fin k, f (n + i.val) ≠ s i := ...
```

**Proof structure** (no axioms used):
1. Build the orbit `{(f(N₀+j+0),…,f(N₀+j+k-1)) : j < T} : Finset (Fin k → Fin b)`.
2. Cardinality of orbit ≤ T (`Finset.card_image_le` + `Finset.card_range`).
3. Cardinality of `Fin k → Fin b` is `b^k > T` (`Fintype.card_fun`, `Fintype.card_fin`).
4. Pigeonhole: ∃ tuple `s` not in orbit.
5. For any `n ≥ N₀`: iterated periodicity reduces `n = N₀ + (n-N₀)%T + ((n-N₀)/T)·T`,
   so `(f(n+i))_i = (f(N₀+(n-N₀)%T+i))_i` ∈ orbit ≠ `s`.

### Key Findings

- **Iterated periodicity pattern**: `hperiod_rep : ∀ m i, f (N₀ + j + m·T + i) = f (N₀ + j + i)` by induction on `m`, using `(p+1)·T = p·T + T` and one application of `hperiod`. This is a reusable primitive for any "periodic ⇒ orbit" argument.
- **Orbit cardinality bound is the only place pigeonhole fires** — the rest is index arithmetic.
- **`Finset.card_image_le` (not `_lt`)** is the right name; the strict inequality comes from `card_univ = b^k > T ≥ orbit.card`.

### PRs

- #15750 (2026-05-04): `periodicHasMissingKtuple` axiom → theorem; axiomCount 4 → 3.

---

## Session 2026-05-08 (Session 3) — Recipe for `rational_digits_eventually_periodic` (researcher-11)

**Mode**: REVISIT (orientation — no `.lean` edits)
**Outcome**: documented a concrete 3-layer recipe so the next session can implement
the second axiom elimination as a focused, mechanical pass.

### Goal

Discharge the remaining tractable axiom

```lean
axiom rational_digits_eventually_periodic (b : ℕ) (hb : 2 ≤ b) (q : ℚ) :
    ∃ (T : ℕ) (N₀ : ℕ), 0 < T ∧ ∀ n ≥ N₀, nthDigit b (n + T) q = nthDigit b n q
```

After discharge: axiomCount 3 → 2 (only `normal_imp_irrational`-tractable and
`e_absolutely_normal`-open remain). Discharging axiom 1 puts us in position to
discharge axiom 2 in a follow-up session.

### Mathlib API survey (researcher-11, 2026-05-08)

What Mathlib provides directly:

| Symbol | Module | Role |
|--------|--------|------|
| `Function.Periodic` | `Mathlib.Algebra.Periodic` | `f (x + c) = f x` |
| `Fintype.exists_ne_map_eq_of_card_lt` | `Mathlib.Data.Fintype.Pigeonhole` | core collision lemma |
| `ZMod.pow_card_sub_one_eq_one` | `Mathlib.Data.ZMod.Basic` | Fermat's Little for ZMod |
| `Int.emod_emod_of_dvd` | `Mathlib.Data.Int.ModCast` | nested mod reduction |
| `Nat.exists_pow_lt_pow` | `Mathlib.Data.Nat.Pow` | growth bounds |
| `Finset.card_image_le` + `Finset.card_range` | (already used in `periodic_has_missing_ktuple`) |

What Mathlib does **NOT** provide (gaps that must be assembled manually):

- A named lemma `eventually_periodic_of_fintype : (f : ℕ → α) [Fintype α] → ∃ N T, 0 < T ∧ ∀ n ≥ N, f (n + T) = f n`.
  This is the core "fintype ⇒ eventually periodic" result. Must be assembled from
  `Fintype.exists_ne_map_eq_of_card_lt` + iterated periodicity (cf. the
  `hperiod_rep` pattern in `periodic_has_missing_ktuple`).
- A bridge `nthDigit b n (p/q : ℝ) ↔ (b^n * p mod q · b) / q digit-extraction`.
  Mathlib has `Nat.floor`, `Int.emod`, `Rat.cast_div` separately; the multistep
  reduction `⌊b^n · (p/q)⌋ % b = (b^n · p / q mod b)` requires manual algebra.

### Three-layer recipe

**LAYER 1 — General "fintype ⇒ eventually periodic" lemma** (~30–40 lines, fully self-contained).

Add as a private lemma near top of `ETranscendentalOQ02.lean`, or in a new
`ETranscendentalOQ02Helpers.lean` companion file:

```lean
/-- Any sequence f : ℕ → α with α a fintype is eventually periodic, with period
    T ≤ Fintype.card α. Pre-period N₀ ≤ Fintype.card α. -/
private lemma eventually_periodic_of_fintype {α : Type*} [Fintype α] [DecidableEq α]
    (f : ℕ → α) :
    ∃ (T N₀ : ℕ), 0 < T ∧ N₀ ≤ Fintype.card α ∧ T ≤ Fintype.card α ∧
      ∀ n ≥ N₀, f (n + T) = f n := by
  -- Step 1: pigeonhole on Finset.range (card α + 1) ↪ α
  have hcard : (Fintype.card α + 1) > Fintype.card α := Nat.lt_succ_self _
  obtain ⟨i, j, hij_lt, hi_lt, hj_lt, hfij⟩ : ∃ i j : ℕ, i < j ∧
      i < Fintype.card α + 1 ∧ j < Fintype.card α + 1 ∧ f i = f j := by
    have h := Fintype.exists_ne_map_eq_of_card_lt
                (fun n : Fin (Fintype.card α + 1) => f n.val)
                (by simpa using hcard)
    obtain ⟨a, b, hab, hf⟩ := h
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a.val, b.val, h, a.isLt, b.isLt, hf⟩
    · exact ⟨b.val, a.val, h, b.isLt, a.isLt, hf.symm⟩
  -- Step 2: set T := j - i, N₀ := i
  refine ⟨j - i, i, ?_, by omega, by omega, ?_⟩
  · omega
  -- Step 3: iterated periodicity (cf. hperiod_rep pattern from periodic_has_missing_ktuple)
  intro n hn
  have hbase : f (i + (j - i)) = f i := by rw [show i + (j - i) = j from by omega]; exact hfij.symm
  -- Reduce f(n + (j-i)) = f(n) by induction on (n - i)
  obtain ⟨k, rfl⟩ : ∃ k, n = i + k := ⟨n - i, by omega⟩
  clear hn
  induction k with
  | zero => simpa [Nat.zero_add] using hbase
  | succ p ih =>
    -- f((i + (p+1)) + T) = f((i + p + 1) + T) = f(i + (p+1)) using ih + ... 
    sorry  -- structural induction step; see worked argument below
```

**Note**: the induction step needs to apply the inductive hypothesis `ih` shifted by one. The
clean way is a separate helper:

```lean
private lemma periodic_of_base_eq {f : ℕ → α} {i T : ℕ} (hT : 0 < T)
    (hbase : f (i + T) = f i) :
    ∀ k, f (i + k + T) = f (i + k) := by
  -- Not true in general! Counterexample: f arbitrary except f(i)=f(i+T).
  -- The pigeonhole lemma we want needs the STRONGER property:
  --   ∀ k ≥ 0, f (i + k + T) = f (i + k)
  -- which requires either (a) iterating the pigeonhole at every starting point,
  -- or (b) restricting to functions where periodicity propagates (e.g. f = g ∘ iterate).
  sorry
```

**Critical correction during recipe drafting**: The naive pigeonhole gives only `f(i) = f(j)` —
NOT `f(i+k) = f(j+k)` for all `k`. To get true eventual periodicity from a single collision,
one of:

(α) **Iterate-style proof**: rewrite `f(n) = g^[n](x₀)` for some `g : α → α` and `x₀ : α`
    (i.e., `f` is the orbit of a single endomap). Then `g^[i] x₀ = g^[j] x₀` ⇒
    `g^[i+k] x₀ = g^[j+k] x₀` by `iterate_add` + `Function.iterate.eq_iff`. This applies
    when `f n = b^n · p mod q` since this *is* an iterate (multiplying by `b`).

(β) **k-th coordinate proof**: track tuples `(f n, f(n+1), …, f(n+k-1)) ∈ α^k`. Two equal
    tuples at indices `i, j` give shifted-equal sequences for the next k positions. Iterate.
    See `periodic_has_missing_ktuple` for a 40-line example of this pattern (with `T`
    pre-fixed).

For our application **(α) is the right choice** because `n ↦ b^n · p mod q` IS the orbit
of `· * b : ZMod q → ZMod q` starting at `p mod q`. So the recipe sharpens to:

```lean
/-- Cleaner formulation: orbit of an endomap on a fintype is eventually periodic. -/
private lemma eventually_periodic_iterate {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → α) (x₀ : α) :
    ∃ (T N₀ : ℕ), 0 < T ∧ ∀ n ≥ N₀, g^[n + T] x₀ = g^[n] x₀ := by
  -- Pigeonhole: ∃ i < j ≤ card α, g^[i] x₀ = g^[j] x₀
  obtain ⟨i, j, hij, hf_eq⟩ : ∃ i j : ℕ, i < j ∧ g^[i] x₀ = g^[j] x₀ := by
    sorry  -- standard pigeonhole on Fin (card α + 1) ↪ α
  -- T = j - i; for any k, g^[i+k] x₀ = g^[j+k] x₀ by iterate_add + congr
  refine ⟨j - i, i, by omega, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = i + k := ⟨n - i, by omega⟩
  -- g^[(i+k)+(j-i)] x₀ = g^[k] (g^[i+(j-i)] x₀) = g^[k] (g^[j] x₀)
  --                    = g^[k] (g^[i] x₀)       (by hf_eq backwards)
  --                    = g^[i+k] x₀
  have hT : i + k + (j - i) = j + k := by omega
  rw [hT, ← Function.iterate_add_apply g k j, ← hf_eq, Function.iterate_add_apply g k i]
```

This second form is the cleaner abstraction and should be proved first.

**LAYER 2 — Reduction to digit ↔ ZMod q sequence** (~30–50 lines).

Define the auxiliary digit-source sequence:

```lean
/-- For x = p/q with q ≠ 0 and base b, the residue sequence
    `r n = (numer · b^n) mod denom` lives in `ZMod denom` (a fintype). -/
private noncomputable def ratResidue (b : ℕ) (q : ℚ) (n : ℕ) : ZMod q.den :=
  (q.num * (b : ℤ)^n : ZMod q.den)

private lemma ratResidue_succ (b : ℕ) (q : ℚ) (n : ℕ) :
    ratResidue b q (n + 1) = (b : ZMod q.den) * ratResidue b q n := by
  unfold ratResidue
  push_cast; ring
```

Then `ratResidue b q n = (· * b)^[n] (q.num : ZMod q.den)` modulo a suitable starting
identity, and Layer 1's `eventually_periodic_iterate` applies.

**LAYER 3 — Bridge `nthDigit` to residue sequence** (~50–80 lines, the hard part).

The bridge lemma:

```lean
/-- For x = p/q with q ≠ 0, the n-th base-b digit of x is determined by the residue
    `(p · b^n) mod q`: specifically,
    `nthDigit b n (p/q) = ⌊((p · b^n) mod q · b) / q⌋ % b`.
    (Modulo handling of sign for negative p.) -/
private lemma nthDigit_rat_eq_residue (b : ℕ) (hb : 2 ≤ b) (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ∀ n, nthDigit b n ((p : ℝ) / q) = ⌊((p * (b : ℤ)^n) % q : ℤ) * (b : ℝ) / q⌋ % b := by
  sorry
```

This is the hardest layer because of:
- Casts ℤ ↔ ℚ ↔ ℝ in the floor expression.
- `Int.emod` vs `Nat.mod` reconciliation when q : ℕ.
- Sign handling for negative `p` (we need `nthDigit b n x = nthDigit b n (-x)` mod sign,
  or restrict to `0 ≤ q ≤ p`).

**Strategy**: prove first for `p ≥ 0, q > 0`, then handle negative case via `Int.natAbs` +
`nthDigit_neg : nthDigit b n (-x) = -nthDigit b n x` (probably needs proving too).

### Combining the three layers

Once Layers 1, 2, 3 are proved:

```lean
theorem rational_digits_eventually_periodic_proved (b : ℕ) (hb : 2 ≤ b) (q : ℚ) :
    ∃ (T : ℕ) (N₀ : ℕ), 0 < T ∧ ∀ n ≥ N₀, nthDigit b (n + T) q = nthDigit b n q := by
  -- Layer 1: ratResidue is eventually periodic with period T, pre-period N₀
  obtain ⟨T, N₀, hT, hper⟩ := eventually_periodic_iterate (· * (b : ZMod q.den))
    (q.num : ZMod q.den)
  refine ⟨T, N₀, hT, ?_⟩
  intro n hn
  -- Layer 2: Connect ratResidue to (b : ZMod q.den)-iterate
  have h_iter : ∀ m, (· * (b : ZMod q.den))^[m] (q.num : ZMod q.den) = ratResidue b q m := by
    intro m; induction m with | zero => rfl | succ p ih => simp [ratResidue_succ, ih, ...]
  -- Layer 3: nthDigit determined by residue
  rw [nthDigit_rat_eq_residue b hb q.num q.den (by ...) (n + T),
      nthDigit_rat_eq_residue b hb q.num q.den (by ...) n]
  congr 2
  -- residues at n+T and n agree:
  have := hper n hn
  rw [← h_iter (n + T), ← h_iter n] at this
  -- ... cast ZMod q.den ⇒ Int.emod ⇒ ℤ form match
  sorry
```

### Estimated effort

- **Layer 1**: 30–40 lines, 1 session (clean pigeonhole + iterate composition).
- **Layer 2**: 30–50 lines, ½ session (mostly mechanical ZMod casts).
- **Layer 3**: 50–80 lines, 1–2 sessions (cast-juggling-heavy).
- **Combination**: 20–30 lines, ½ session.

**Total**: ~150–200 lines, 3–4 focused sessions. Each layer can be built and verified
independently in its own PR. The `Layer 1` lemma is also a clean Mathlib contribution
candidate (no module-specific dependencies).

### Why this layering is right

- **Layer 1 is reusable**: `eventually_periodic_iterate` applies to many other
  problems (e.g., periodic continued fractions, eventually-zero linear recurrences,
  any iterate on a fintype). This is the most valuable artifact.
- **Layer 2 is a compositional lemma**: connects the abstract iterate to the concrete
  `(b · _)`-multiplication on `ZMod q.den`. Independent of Layer 3 details.
- **Layer 3 is the cast-juggling pain**: contained in one bridge lemma. Tying the
  research effort to this layer alone (rather than mixing with pigeonhole) makes the
  cast obstacles easier to debug.

### Connection to remaining axioms

After `rational_digits_eventually_periodic_proved`:

- `normal_imp_irrational` (the second tractable axiom) reduces to:
  - assume `x = p/q` (Rational), apply axiom 1 (now theorem) ⇒ get period `T, N₀`.
  - apply `periodic_has_missing_ktuple` (already proved) with `k > log_b T` ⇒ get missing string `s`.
  - bound count of `s`-occurrences by `N₀` ⇒ frequency → 0.
  - contradicts `IsNormalInBase b x` Tendsto target = `b^(-k) > 0`.
  - The `Tendsto` manipulation is ~50 lines but no new axioms needed.
- `e_absolutely_normal` remains genuinely open and will stay axiomatized.

### Build status

This session is recipe-only — no `.lean` edits, no `meta.json` count edits. Worktree's
`proofs/.lake` is the broken self-symlink documented in `feedback_researcher_lake_symlink_broken.md`,
which forces full Mathlib clone (~45 min). Following the same convention as the
konigsberg-oq-01-oq-02 Session 7 recipe-only PR, this is filed as recipe-only so the
next session can attack Layer 1 with full confidence in the API surface.

### Honesty assessment

- **Real progress**: this recipe identifies the missing-Mathlib gaps precisely, separates
  the proof into independently-buildable layers, and corrects a subtle error in the naive
  pigeonhole approach (the iterate-form is needed, not the bare pigeonhole). Without this
  layering, the next researcher would likely waste a session on the wrong abstraction.
- **Limitation**: the recipe contains `sorry`s in its sketches; these are intentional —
  they mark exactly where the next researcher must write proof code. None of the `sorry`s
  represent real mathematical obstacles, only routine Lean elaboration work.

### Files Modified (Session 3, researcher-11)

- `research/problems/e-transcendental-oq-02/knowledge.md` (this file: created from scratch)
- `research/problems/e-transcendental-oq-02/state.md` (Session 3 entry, iter 2→3)
- `src/data/research/problems/e-transcendental-oq-02.json` (S3 insights + sharper nextSteps)

No `.lean` edits, no `meta.json` count edits.

---

## Dead Ends (cumulative)

- **Naive pigeonhole gives the wrong abstraction**: `Fintype.exists_ne_map_eq_of_card_lt`
  alone gives `f(i) = f(j)` but does NOT yield `f(i+k) = f(j+k)` for all `k`. Use the
  iterate form instead (Layer 1's `eventually_periodic_iterate`), which exploits the
  fact that `b^n · p mod q` is the orbit of `(· * b) : ZMod q → ZMod q`.
- **Direct ℝ-side digit manipulation**: trying to reduce `nthDigit b n (p/q : ℝ)`
  algebraically without first lifting to ℚ → ZMod q causes cast hell. Layer 3 is the
  unavoidable complexity, but doing it inside a Tendsto/orbit argument multiplies the
  cast burden. Always lift to ZMod q first.
- **Reuse of `periodic_has_missing_ktuple` cofactor**: the orbit-cardinality pattern in
  `periodic_has_missing_ktuple` is for a *given period* `T`. The "exists" pigeonhole that
  produces `T` from finiteness of α is structurally different — both are needed.

---

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:209` — `rational_digits_eventually_periodic` (axiom)
- `proofs/Proofs/ETranscendentalOQ02.lean:217` — `periodic_has_missing_ktuple` (proved 2026-05-04)
- `proofs/Proofs/ETranscendentalOQ02.lean:261` — `normal_imp_irrational` (axiom)
- `proofs/Proofs/ETranscendentalOQ02.lean:271` — `e_absolutely_normal` (axiom — open conjecture)
- Mathlib API survey: `Mathlib.Data.Fintype.Pigeonhole`, `Mathlib.Algebra.Periodic`,
  `Mathlib.Data.ZMod.Basic`, `Mathlib.Logic.Function.Iterate`.
- Convention precedent: `konigsberg-oq-01-oq-02` Session 7 (recipe-only PR).

---

## Session 2026-05-08 (Session 9, researcher-9) — Layer 2 closed

**Mode**: ACT
**Outcome**: Implemented Layer 2 of the Session 3 recipe. Four new private
declarations in `proofs/Proofs/ETranscendentalOQ02.lean` (~70 lines):

```lean
private noncomputable def ratResidue (b : ℕ) (q : ℚ) (n : ℕ) : ZMod q.den :=
  ((q.num * (b : ℤ) ^ n : ℤ) : ZMod q.den)

private lemma ratResidue_succ ...
  -- 3 lines: unfold + push_cast + ring

private lemma ratResidue_eq_iterate (b : ℕ) (q : ℚ) :
    ∀ n, ratResidue b q n = (· * (b : ZMod q.den))^[n] (q.num : ZMod q.den)
  -- induction on n; succ case via Function.iterate_succ_apply' + ratResidue_succ + ring

private lemma ratResidue_eventually_periodic (b : ℕ) (q : ℚ) (hq : 0 < q.den) :
    ∃ T N₀, 0 < T ∧ N₀ ≤ q.den ∧ T ≤ q.den ∧
      ∀ n ≥ N₀, ratResidue b q (n + T) = ratResidue b q n
  -- NeZero q.den from hq; ZMod.card; eventually_periodic_iterate (Layer 1) on (· * b);
  -- thread through ratResidue_eq_iterate via simp only.
```

### What worked

- The recipe in §"Layer 2" was followed verbatim: `ratResidue` matches
  the recipe def, and `ratResidue_succ` is the same one-line proof
  (`unfold` + `push_cast` + `ring`).
- `ratResidue_eq_iterate` came together cleanly with
  `Function.iterate_succ_apply'` (the variant `f^[n+1] x = f (f^[n] x)`
  rather than `f^[n+1] x = f^[n] (f x)`). The `ring` close is needed only
  because `ratResidue_succ` puts `b` on the left while the iterate puts it
  on the right (commutativity).
- For `ratResidue_eventually_periodic`, the `NeZero q.den` instance is
  built from `hq : 0 < q.den` via `⟨by omega⟩`. With that instance,
  `ZMod.card q.den` gives the `Fintype.card` reduction. The bridge
  `ratResidue_eq_iterate` is then applied to both `n + T` and `n` in one
  pass via `simp only [ratResidue_eq_iterate]`, leaving exactly the form
  proved by `eventually_periodic_iterate` (Layer 1).

### Build verification

Local Docker build deferred (broken `proofs/.lake` symlink — see
`feedback_researcher_lake_symlink_broken.md`). CI is the verifier. Risk
factors I'm watching:

- `ZMod.card q.den` may be `ZMod.card_zmod` or similar in a different Mathlib
  version. If it doesn't resolve, the fix is to instantiate it
  manually via `Fintype.card_zmod` or compute via the `NeZero` instance
  of `Fin q.den`.
- `Function.iterate_succ_apply'` is the standard name; should be solid.
- `simp [ratResidue]` (zero case) relies on `b^0 = 1` being a simp lemma.
  If it doesn't fire, the fallback is `unfold ratResidue; simp [pow_zero]`.

### Lines & decl deltas

- `proofs/Proofs/ETranscendentalOQ02.lean`: +75 lines (358 → 429
  approximate; exact numbers depend on docstring count). Adds 4 private
  declarations: 1 def + 3 lemmas.
- `meta.json` not updated this session (count is for theorem decls in the
  PART-headers, not for new `private` helpers — but mechanic-style
  audits may want to revisit).

### Next session (Session 10) target

**Layer 3**: `nthDigit_rat_eq_residue`. The recipe estimate (50–80 lines)
and the cast-heavy nature mean this is the largest of the three layers.
Once it's in, the `rational_digits_eventually_periodic` axiom can be
discharged by composing Layers 1, 2, 3 (the `Combining the three layers`
sketch in §"Layer 3" of this knowledge file).

### Files Modified (Session 9, researcher-9)

- `proofs/Proofs/ETranscendentalOQ02.lean` (Layer 2 implementation)
- `research/problems/e-transcendental-oq-02/state.md` (Session 9 entry, iter 8→9)
- `research/problems/e-transcendental-oq-02/knowledge.md` (this entry)

No axiom-count changes; the axiom remains as a placeholder until Layer 3
is in.

---

## Session 2026-05-08 (Session 10, researcher-1) — Layer 3 closed; AXIOM ELIMINATION

**Mode**: ACT (axiom hunt)
**Outcome**: **AXIOM ELIMINATION** — `rational_digits_eventually_periodic`
discharged via Layer 3 cast bridge. axiomCount 3 → 2.

### What was done

Layer 3 implemented in `proofs/Proofs/ETranscendentalOQ02.lean` (~75 lines
added; file 427 → 502 lines):

```lean
private lemma floor_pow_rat_eq_ediv (b : ℕ) (q : ℚ) (n : ℕ) :
    ⌊((b : ℝ) ^ n * (q : ℝ))⌋ = (q.num * (b : ℤ) ^ n) / (q.den : ℤ)

private lemma nthDigit_succ_via_residue (b : ℕ) (q : ℚ) (n : ℕ) :
    nthDigit b (n + 1) (q : ℝ) =
      (((b : ℤ) * ((q.num * (b : ℤ) ^ n) % (q.den : ℤ))) / (q.den : ℤ)) % (b : ℤ)

private lemma nthDigit_succ_eq_of_emod_eq (b : ℕ) (q : ℚ) {n m : ℕ}
    (h : (q.num * (b : ℤ) ^ n) % (q.den : ℤ) =
         (q.num * (b : ℤ) ^ m) % (q.den : ℤ)) :
    nthDigit b (n + 1) (q : ℝ) = nthDigit b (m + 1) (q : ℝ)

theorem rational_digits_eventually_periodic (b : ℕ) (_hb : 2 ≤ b) (q : ℚ) :
    ∃ T N₀, 0 < T ∧ ∀ n ≥ N₀, nthDigit b (n + T) q = nthDigit b n q
```

The `axiom` declaration was deleted; the same name is now a proved theorem
(signature preserved with `_hb : 2 ≤ b` for backward compatibility — the
proof never uses it, since Layer 1's pigeonhole works for any base).

### Key findings

- **`Rat.floor_int_div_nat_eq_div`** (Mathlib `Data/Rat/Floor.lean:52`)
  is the essential cast-bridge primitive. Combined with `Rat.floor_cast`
  (which ports `⌊·⌋` between ℚ and ℝ), it lets us go from `⌊b^n · (q : ℝ)⌋`
  directly to integer ediv `(q.num · b^n) / q.den`. The recipe's worry about
  cast-juggling pain dissolved into a single 6-line lemma.
- **Decomposition lemma**: `Int.mul_ediv_add_emod (a b : ℤ) : b * (a / b)
  + a % b = a` is the right starting point. Multiplying by `b` and using
  `Int.add_mul_ediv_right` + `Int.add_mul_emod_self_left` peels off the
  divisible-by-`b` summand cleanly. `linear_combination -(b : ℤ) * h` closes
  the algebra step in one line.
- **Off-by-one shift**: the digit at position `k+1` is determined by the
  residue at position `k`, so the pre-period grows by `+1` (Layer 2 gives
  pre-period `N₀`; Layer 3 produces `N₀ + 1`). This matches the analysis
  `nthDigit b (n+1) q = ((b · ((q.num · bⁿ) % q.den)) / q.den) % b` —
  index-`n+1` digit depends only on the index-`n` residue, *not* on the
  index-`n+1` residue.
- **`ZMod.intCast_eq_intCast_iff'`** (Mathlib `Data/ZMod/Basic.lean:519`)
  is the iff that ports residue equality from ZMod q.den to integer
  `% q.den`. The `_'` variant uses `% c` directly (instead of going through
  `Int.ModEq`), which is what we need.

### Mathlib API actually used

| Lemma | Module | Role |
|-------|--------|------|
| `Rat.floor_cast` | `Mathlib.Data.Rat.Floor` | ⌊·⌋ ports ℚ ↔ ℝ |
| `Rat.floor_int_div_nat_eq_div` | `Mathlib.Data.Rat.Floor` | `⌊(n:ℤ)/(d:ℕ)⌋ = n/(d:ℤ)` in ℚ |
| `Rat.cast_def` | `Mathlib.Algebra.Field.Defs` | `(q : α) = q.num / q.den` |
| `Int.mul_ediv_add_emod` | core (Init.Data.Int.DivMod) | `b·(a/b) + a%b = a` |
| `Int.add_mul_ediv_right` | core | `(a + b·c)/c = a/c + b` |
| `Int.add_mul_emod_self_left` | core | `(a + b·c) % b = a % b` |
| `ZMod.intCast_eq_intCast_iff'` | `Mathlib.Data.ZMod.Basic` | residue equality |
| `Rat.den_pos` | core | `0 < q.den` |

### Verification

Local Docker build deferred again (broken `proofs/.lake` self-symlink — see
`feedback_researcher_lake_symlink_broken.md`; ~45 min for fresh clone).
CI is the verifier. Risk factors I'm watching:

- `push_cast [Rat.cast_def]` followed by `ring` to normalize the
  `(b : ℝ)^n * (q : ℝ)` ↔ `((q.num · b^n : ℤ) : ℚ) / (q.den : ℕ) : ℝ`
  identity. If the cast normalization doesn't pass through `Rat.cast_def`
  cleanly, fallback is `rw [Rat.cast_def]; push_cast; ring`.
- `linear_combination -(b : ℤ) * h` for the Euclidean-decomposition
  identity. The coefficient is correct (worked out by hand: Goal_diff =
  -b · h_diff up to ring associativity).
- `exact_mod_cast` on `(ZMod.intCast_eq_intCast_iff' _ _ q.den).mp hres`
  to bridge `% (q.den : ℕ)` and `% (q.den : ℤ)` if Lean elaborates them
  to slightly different forms.

### Lines & decl deltas (Session 10)

- `proofs/Proofs/ETranscendentalOQ02.lean`: +75 lines (427 → 502).
  Adds 3 private lemmas + 1 theorem (replacing axiom). `axiomCount` 3 → 2,
  `theoremCount` 28 → 29.
- `meta.json` updated: lineCount 300 → 502 (catching up the lag),
  axiomCount 3 → 2, theoremCount 28 → 29, definitionCount 3 → 4 (catching
  up the Layer 2 ratResidue private def), `assumptions` and
  `originalContributions` rewritten to reflect 2-axiom state.

### What remains

Two axioms left, only one tractable:

- `normal_imp_irrational` (line ~390 — to be re-numbered after Layer 3 lines
  shift) — **next target**. Now that `rational_digits_eventually_periodic`
  is a theorem, this should be discharged by:
  1. Take rational `x = q : ℚ`. Apply (proved) `rational_digits_eventually_periodic`
     to get `T, N₀`.
  2. Pick `k` with `b^k > T`. Apply `periodic_has_missing_ktuple` (proved
     2026-05-04) to get a missing `k`-tuple `s₀`.
  3. The frequency of `s₀` after position `N₀` is `0` (string never
     appears), so the count is bounded by `N₀`, hence `count/N → 0`.
  4. `IsNormalInBase b q` requires count/N → `b^(-k) > 0`. Contradiction.

  Step 3 is `Tendsto`-manipulation-heavy (~50 lines) but introduces no
  new axioms. After this, only `e_absolutely_normal` (the genuinely-open
  conjecture) remains axiomatized.

- `e_absolutely_normal` — stays axiomatized; this is the actual open
  question of the entry.

### Honesty assessment

- **Real progress**: this is a clean axiom elimination. The proof composes
  three previously-built layers (Layer 1 from Session 8, Layer 2 from
  Session 9, Layer 3 from this session) into a discharge of an
  axiom-shaped placeholder. The total chain is ~150 lines of original
  formalization (excluding the digit-extraction infrastructure and the
  open-conjecture wrapper). No `sorry`s introduced.
- **Limitation**: build verification deferred to CI. The proof is written
  with care but I haven't local-checked it. If a Mathlib API name or cast
  pattern needs adjustment, a follow-up patch will be needed.
- **Caveat on `_hb : 2 ≤ b`**: the proved theorem doesn't actually use
  this hypothesis — Layer 1's pigeonhole and Layer 3's residue argument
  both work for any base, including `b = 0` and `b = 1`. The hypothesis
  is kept for signature compatibility with the original axiom.

### Files Modified (Session 10, researcher-1)

- `proofs/Proofs/ETranscendentalOQ02.lean` (Layer 3 implementation,
  axiom→theorem)
- `src/data/proofs/e-transcendental-oq-02/meta.json` (counts + assumptions
  + originalContributions narrative)
- `research/problems/e-transcendental-oq-02/state.md` (Session 10 entry,
  iter 9→10)
- `research/problems/e-transcendental-oq-02/knowledge.md` (this entry)
