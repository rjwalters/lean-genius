import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Rat.Cardinal
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountable

-- Mathlib v4.26.0 introduced `Rat.instEncodable` (via `Mathlib.Data.Rat.Encodable`,
-- transitively imported), which competes with the `Encodable ℚ` instance derived
-- from `Primcodable.ofDenumerable ℚ`. `Computable.encode` synthesises the latter,
-- but Lean prefers the former at standalone `Encodable.encode (q : ℚ)` sites,
-- creating a mismatch in the `decodeReal` proof chain. Disabling the standalone
-- `Rat.instEncodable` in this file forces both routes to use the Primcodable-
-- derived instance, keeping the proof's encode/decode round-trip coherent.
attribute [-instance] Rat.instEncodable

/-
# Countability of Computable Real Numbers

## Open Question (algebraic-numbers-countable-oq-02-oq-04)

Prove that the set of *computable* real numbers is countable.

A real number is **computable** if there exists a Turing machine that, given
`n : ℕ`, outputs a rational `q n : ℚ` such that the sequence `q 0, q 1, q 2, ...`
converges to it. This formalizes the intuition that the "describable" reals form
a countable subfamily of ℝ: each is named by a finite Turing-machine description,
and finite descriptions form a countable set.

The set of computable reals sits between algebraic and ℝ in the cardinality
hierarchy:

    ℚ  ⊊  algebraic  ⊊  computable  ⊊  ℝ
    ↑          ↑              ↑       ↑
    ℵ₀         ℵ₀             ℵ₀      𝔠

Both ℚ ⊊ algebraic ⊊ computable are strict (computable contains transcendentals
like π and e), but all three are countable. The final inclusion is strict by
cardinality (computable is countable but ℝ has cardinality 𝔠).

## Main Results

* `computable_reals_countable` (S3, build pending): the set `{r : ℝ | IsComputable r}`
  is countable.
* `card_computable_reals_le_aleph0` (cardinal upper bound, now unconditional).
* `aleph0_le_card_computable_reals` (cardinal lower bound, unconditional).
* `card_computable_reals_eq_aleph0` (exact ℵ₀, now unconditional).

## Proof Strategy (upper bound — S3, this PR)

The proof rests on the Mathlib infrastructure for partial recursive functions:

1. **Encoded sequence is computable**: For `f : ℕ → ℚ` with `Computable f`, the
   composition with the rational encoding gives `Computable (fun n => encode (f n))`,
   a function `ℕ → ℕ`. (`Computable.encode.comp`)

2. **Total computable ⊆ partial recursive**: A total computable function `ℕ → ℕ`,
   coerced to a partial function, is `Partrec` (and hence `Nat.Partrec` by
   `Partrec.nat_iff`).

3. **Codes exist**: Every `Nat.Partrec` function is the evaluation of some
   `Nat.Partrec.Code`. (`Nat.Partrec.Code.exists_code`)

4. **Codes are countable**: `Nat.Partrec.Code` is `Denumerable` (in particular,
   `Countable`).

5. **Decoded reals cover the computable reals**: We define
   `decodeReal : Nat.Partrec.Code → ℝ` to send each code to the limit of its
   evaluated rational sequence (when defined, via `Classical.choice`), or to 0
   otherwise. Every computable real lies in the range of `decodeReal`, because a
   code witness exists by steps 1-3 above, and the limit witness from `IsComputable`
   provides the `dif_pos` branch.

6. **Range is countable**: The range of any function from a countable type into ℝ
   is countable (`Set.countable_range`), so the computable reals (a subset of this
   range) are countable (`Set.Countable.mono`).

## Status

- **S1**: SCAFFOLD — `IsComputable` definition + main theorem (sorry).
- **S2** (researcher-1, #17759): unconditional lower bound `ℵ₀ ≤ #(computable reals)`
  via rational embedding; five concrete computable witnesses (rat/int/nat/0/1);
  exact equality stated (contingent on the S1 sorry).
- **S3** (#17768): full proof of `computable_reals_countable` via `decodeReal` +
  `Nat.Partrec.Code.exists_code` pipeline. **Build pending** — verification
  relies on the named Mathlib API (`Computable.encode`, `Computable.comp`,
  `Partrec.nat_iff`, `Nat.Partrec.Code.exists_code`, `Set.countable_range`,
  `Set.Countable.mono`, `tendsto_nhds_unique`, `Encodable.encode_injective`,
  `Part.some_injective`). With S3 landed, `card_computable_reals_le_aleph0`
  and `card_computable_reals_eq_aleph0` (from S2) become unconditional.
- **S4** (#17806): strict-inclusion + `#(non-computable) = 𝔠` via partition +
  ℵ₀-absorption mirroring the OQ02OQ03 transcendental cardinality argument.
- **S5** (#17860): cross-cardinal consolidation (`card_computable_reals_eq_card_algebraic_reals`,
  `card_nonComputableReals_eq_card_reals`, `cardinality_trichotomy`).
- **S6** (this PR): Set-level structural API derived from the S2-S4 cardinal
  results — `computable_reals_nonempty/_infinite` and
  `nonComputableReals_nonempty/_uncountable/_infinite`. Five short corollaries,
  no new Mathlib API dependencies beyond `Set.infinite_range_of_injective`,
  `Rat.cast_injective`, and `Set.Finite.countable`.

## References

- Mathlib `Computable`: `Mathlib.Computability.Partrec`
- Mathlib `Nat.Partrec.Code`: `Mathlib.Computability.PartrecCode`
- Pour-El & Richards, *Computability in Analysis and Physics* (1989)
- Weihrauch, *Computable Analysis: An Introduction* (2000)
- Turing, "On Computable Numbers" (1936) — the original definition

Tags: set-theory, cardinality, real-analysis, computability, computable-analysis
-/

namespace AlgebraicNumbersCountableOQ02OQ04

open Cardinal Filter Classical

/-- A real number `r` is **computable** if there exists a `Computable` function
    `f : ℕ → ℚ` (in Mathlib's `Computable` sense) such that the real-valued
    sequence `(f n : ℝ)` converges to `r`.

    Equivalently: there is a Turing machine that, on input `n`, halts and
    outputs a rational approximation `q_n`, with the sequence `q_0, q_1, q_2, ...`
    converging to `r`. The Turing-machine description is the "name" of `r`. -/
def IsComputable (r : ℝ) : Prop :=
  ∃ f : ℕ → ℚ, Computable f ∧ Tendsto (fun n => (f n : ℝ)) atTop (nhds r)

/-! ## S3 — Upper bound: codeReal pipeline

The lower bound from S2 gave `ℵ₀ ≤ #{r | IsComputable r}`. To complete the
cardinality (and originally to discharge the S1 `sorry` in
`computable_reals_countable`), we use the `decodeReal : Nat.Partrec.Code → ℝ`
map: every computable real is the image of some code under this map.

The construction has three pieces:
* `decodeReal` — a noncomputable decoder using `Classical.choose` on the
  existence of (r, f) with `c.eval n = Part.some (encode (f n))` and `(f n : ℝ) → r`.
* `exists_code_of_computable_rat_seq` — the pipeline lemma: every
  `Computable (ℕ → ℚ)` has a `Nat.Partrec.Code` with matching encoded eval.
* `computable_real_mem_range_decodeReal` — every `IsComputable` real is in
  the range of `decodeReal`. Combined with `Set.countable_range` (Code is
  `Denumerable`) and `Set.Countable.mono`, this closes `computable_reals_countable`.
-/

/-- Decoder from a partial-recursive code into a real number.

    Given `c : Nat.Partrec.Code`, attempts to interpret its evaluation as the
    encoding of a convergent rational sequence: if there is some `f : ℕ → ℚ`
    such that `c.eval n = Part.some (Encodable.encode (f n))` for all `n` and
    the sequence `(f n : ℝ)` converges to some `r : ℝ`, then `decodeReal c = r`;
    otherwise `decodeReal c = 0`.

    Noncomputable because we use `Classical.choose` on the existence of the
    limit and witnessing sequence. -/
noncomputable def decodeReal (c : Nat.Partrec.Code) : ℝ :=
  if h : ∃ r : ℝ, ∃ f : ℕ → ℚ,
      (∀ n, c.eval n = Part.some (Encodable.encode (f n))) ∧
      Tendsto (fun n => (f n : ℝ)) atTop (nhds r)
  then h.choose
  else 0

/-- **Pipeline lemma**: every computable rational sequence is the evaluation of
    some `Nat.Partrec.Code`.

    This is the key Mathlib API call. It assembles three facts:
    (i) `Computable.encode` — encoding is computable;
    (ii) `Computable.comp` — composition preserves computability;
    (iii) `Partrec.nat_iff` and `Nat.Partrec.Code.exists_code` — every partial
    recursive function on ℕ has an explicit code. -/
lemma exists_code_of_computable_rat_seq {f : ℕ → ℚ} (hf : Computable f) :
    ∃ c : Nat.Partrec.Code, ∀ n, c.eval n = Part.some (Encodable.encode (f n)) := by
  -- (i) + (ii): The encoded sequence n ↦ encode (f n) is Computable ℕ → ℕ.
  have hg : Computable (fun n : ℕ => Encodable.encode (f n)) :=
    Computable.encode.comp hf
  -- (iii): As a partial-recursive function ℕ →. ℕ, this is `Nat.Partrec`.
  have h_nat_partrec : Nat.Partrec
      (fun n : ℕ => Part.some (Encodable.encode (f n))) :=
    Partrec.nat_iff.mp hg.partrec
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp h_nat_partrec
  -- `hc : c.eval = fun n => Part.some (encode (f n))`.
  exact ⟨c, fun n => congrFun hc n⟩

/-- **Key lemma**: every computable real is the image under `decodeReal` of
    some `Nat.Partrec.Code`.

    Given `IsComputable r`, we extract the witness sequence `f`, obtain a code
    `c` via `exists_code_of_computable_rat_seq`, and show `decodeReal c = r`
    by uniqueness of limits. -/
lemma computable_real_mem_range_decodeReal {r : ℝ} (hr : IsComputable r) :
    r ∈ Set.range decodeReal := by
  obtain ⟨f, hf, hl⟩ := hr
  obtain ⟨c, hc_eval⟩ := exists_code_of_computable_rat_seq hf
  refine ⟨c, ?_⟩
  -- Goal: decodeReal c = r.
  have h_exists : ∃ r' : ℝ, ∃ f' : ℕ → ℚ,
      (∀ n, c.eval n = Part.some (Encodable.encode (f' n))) ∧
      Tendsto (fun n => (f' n : ℝ)) atTop (nhds r') :=
    ⟨r, f, hc_eval, hl⟩
  show decodeReal c = r
  unfold decodeReal
  rw [dif_pos h_exists]
  -- Goal: h_exists.choose = r.
  -- The Classical.choose for h_exists picks some r' with a witness sequence
  -- f' satisfying the same eval-encoding constraint. Combined with `hc_eval`,
  -- we get f n = f' n pointwise, so the limit is unique: r = h_exists.choose.
  obtain ⟨f_chosen, h_eval_chosen, h_lim_chosen⟩ := h_exists.choose_spec
  have hf_eq : ∀ n, f n = f_chosen n := by
    intro n
    have hen : Part.some (Encodable.encode (f n)) =
        Part.some (Encodable.encode (f_chosen n)) := by
      rw [← hc_eval n, ← h_eval_chosen n]
    have he : Encodable.encode (f n) = Encodable.encode (f_chosen n) :=
      Part.some_injective hen
    exact Encodable.encode_injective he
  have h_lim_to_chosen :
      Tendsto (fun n => (f n : ℝ)) atTop (nhds h_exists.choose) := by
    have hfn : (fun n => (f n : ℝ)) = (fun n => (f_chosen n : ℝ)) := by
      funext n; rw [hf_eq]
    rw [hfn]
    exact h_lim_chosen
  exact (tendsto_nhds_unique hl h_lim_to_chosen).symm

/-- **Main Theorem (S3 proof, build pending)**: The set of computable real
    numbers is countable.

    Proof: `{r | IsComputable r} ⊆ Set.range decodeReal` (by
    `computable_real_mem_range_decodeReal`), and the range of any function
    from `Nat.Partrec.Code` is countable since `Code` is `Denumerable` (hence
    `Countable`). -/
theorem computable_reals_countable :
    Set.Countable {r : ℝ | IsComputable r} :=
  (Set.countable_range decodeReal).mono fun _r hr =>
    computable_real_mem_range_decodeReal hr

/-- **Cardinal form**: the cardinality of the computable reals is at most ℵ₀.

    Direct consequence of `computable_reals_countable` via
    `le_aleph0_iff_set_countable`. -/
theorem card_computable_reals_le_aleph0 :
    (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) ≤ ℵ₀ :=
  le_aleph0_iff_set_countable.mpr computable_reals_countable

/-! ## S2 — Lower bound: every rational is computable

The lower bound `ℵ₀ ≤ #{r | IsComputable r}` is unconditional: it follows
from the embedding `ℚ ↪ {r | IsComputable r}` via `q ↦ (q : ℝ)`, witnessed
by the constant rational sequence.

This S2 deliverable adds, with no new axioms or sorries:

* `rat_isComputable q : IsComputable (q : ℝ)` — every rational is a computable
  real, via the constant sequence `fun _ => q`. Uses `Computable.const`
  (with `Primcodable ℚ` from `Mathlib.Data.Rat.Denumerable`) and
  `tendsto_const_nhds`.
* Specialisations to ℕ, ℤ, 0, 1.
* `aleph0_le_card_computable_reals : ℵ₀ ≤ #{r | IsComputable r}` — cardinal
  lower bound. The injection `ℚ → {r | IsComputable r}` sends `q ↦ ⟨(q : ℝ), …⟩`;
  injectivity uses `Rat.cast` injectivity on ℝ; the count uses `Cardinal.mk_rat`.
* `card_computable_reals_eq_aleph0` — exact ℵ₀ equality. With S3 landed
  (this PR), this is unconditional.
-/

/-- **S2 lemma**: every rational real is computable, witnessed by the constant
    sequence `fun _ => q`.

    *Proof*. Take `f := fun _ => q`. Then `Computable f` is
    `Computable.const q` (uses `Primcodable ℚ` via
    `Mathlib.Data.Rat.Denumerable`), and the limit of `(f n : ℝ)` is just
    `tendsto_const_nhds`. -/
theorem rat_isComputable (q : ℚ) : IsComputable (q : ℝ) :=
  ⟨fun _ => q, Computable.const q, tendsto_const_nhds⟩

/-- **S2 lemma** — every integer is computable, via `rat_isComputable` and the
    integer-to-rational cast `(n : ℤ) → (n : ℚ) → (n : ℝ)`. -/
theorem int_isComputable (n : ℤ) : IsComputable (n : ℝ) := by
  have h := rat_isComputable (n : ℚ)
  simpa using h

/-- **S2 lemma** — every natural number is computable. -/
theorem nat_isComputable (n : ℕ) : IsComputable (n : ℝ) := by
  have h := rat_isComputable (n : ℚ)
  simpa using h

/-- **S2 lemma** — zero is computable. -/
theorem zero_isComputable : IsComputable (0 : ℝ) := by
  simpa using rat_isComputable 0

/-- **S2 lemma** — one is computable. -/
theorem one_isComputable : IsComputable (1 : ℝ) := by
  simpa using rat_isComputable 1

/-- **S2 main result — cardinal lower bound**: there are at least ℵ₀ computable
    real numbers.

    *Proof*. The map `ι : ℚ → {r : ℝ | IsComputable r}` defined by
    `q ↦ ⟨(q : ℝ), rat_isComputable q⟩` is injective: if
    `ι q₁ = ι q₂` then their underlying real values are equal, and
    `Rat.cast` is injective on ℝ. Hence `#ℚ ≤ #{r | IsComputable r}`,
    and `Cardinal.mk_rat : #ℚ = ℵ₀` finishes. -/
theorem aleph0_le_card_computable_reals :
    ℵ₀ ≤ (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) := by
  let ι : ℚ → ({r : ℝ | IsComputable r} : Set ℝ) :=
    fun q => ⟨(q : ℝ), rat_isComputable q⟩
  have hinj : Function.Injective ι := by
    intro q₁ q₂ hq
    have hv : ((q₁ : ℝ)) = ((q₂ : ℝ)) := by
      have := congrArg Subtype.val hq
      simpa [ι] using this
    exact_mod_cast hv
  have hcard : (#ℚ : Cardinal) ≤ #({r : ℝ | IsComputable r} : Set ℝ) :=
    Cardinal.mk_le_of_injective hinj
  simpa [Cardinal.mkRat] using hcard

/-! ## Exact ℵ₀ equality

Combining the upper bound (S3, this PR — proved via `decodeReal`) with the
unconditional lower bound (S2) yields the exact cardinality.
-/

/-- **Corollary** (unconditional after S3): the computable reals have
    cardinality exactly ℵ₀.

    A pure consequence of `card_computable_reals_le_aleph0` (now unconditional
    after S3 discharged the main `sorry`) and `aleph0_le_card_computable_reals`
    (unconditional, S2). -/
theorem card_computable_reals_eq_aleph0 :
    (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) = ℵ₀ :=
  le_antisymm card_computable_reals_le_aleph0 aleph0_le_card_computable_reals

/-! ## S4 — Strict inclusion `{r | IsComputable r} ⊊ ℝ` and `#non-computable = 𝔠`

Turing's negative observation: there exist non-computable real numbers, in fact
continuum-many. The argument is purely cardinal — no explicit Cantor diagonal
or Chaitin-Ω construction is needed:

  𝔠 = #ℝ ≤ #(computable) + #(non-computable)
        ≤ ℵ₀ + #(non-computable)
        = #(non-computable)                       (absorption, when ℵ₀ ≤ #(nc))

The bootstrap `ℵ₀ ≤ #(non-computable)` itself follows by contradiction: if
#(non-computable) < ℵ₀ then #ℝ ≤ ℵ₀ + ℵ₀ = ℵ₀, contradicting `ℵ₀ < 𝔠`. The
construction parallels the sibling result for transcendentals
(`AlgebraicNumbersCountableOQ02OQ03.continuum_le_card_transcendentals`).

This S4 deliverable adds:

* `nonComputableReals` — the complement set `{r : ℝ | ¬ IsComputable r}`.
* `card_nonComputableReals_eq_continuum` — exact cardinality 𝔠.
* `exists_non_computable_real` — Turing's negative result, formalised.
* `computable_reals_strict_ssubset_univ` — strict subset of `ℝ`.
-/

/-- The set of **non-computable** real numbers, i.e. those not arising as the
    limit of any Mathlib-`Computable` rational sequence. This is the complement
    of `{r : ℝ | IsComputable r}` inside `ℝ`. -/
def nonComputableReals : Set ℝ := {r : ℝ | ¬ IsComputable r}

/-- The computable and non-computable reals partition `ℝ`. -/
private theorem computable_nonComputable_partition :
    ({r : ℝ | IsComputable r} : Set ℝ) ∪ nonComputableReals = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq, nonComputableReals, Set.mem_univ, iff_true]
  exact Classical.em _

/-- Disjointness of the partition. -/
private theorem computable_nonComputable_disjoint :
    Disjoint ({r : ℝ | IsComputable r} : Set ℝ) nonComputableReals := by
  rw [Set.disjoint_left]
  intro x hx hnx
  exact hnx hx

/-- Cardinal absorption: `ℵ₀ + κ = κ` whenever `ℵ₀ ≤ κ`.

    Proof: `ℵ₀ + κ ≤ κ + κ = κ` (by `Cardinal.add_eq_self`); the other direction
    is trivial. Mirrors the helper in
    `AlgebraicNumbersCountableOQ02OQ03.aleph0_add_of_ge`. -/
private theorem aleph0_add_of_ge {κ : Cardinal} (h : ℵ₀ ≤ κ) : ℵ₀ + κ = κ := by
  rw [Cardinal.add_eq_max le_rfl, max_eq_right h]

/-- **Upper bound**: the non-computable reals are a subset of `ℝ`, so their
    cardinality is at most 𝔠. -/
theorem card_nonComputableReals_le_continuum :
    (#(↑nonComputableReals : Set ℝ) : Cardinal) ≤ 𝔠 := by
  calc (#(↑nonComputableReals : Set ℝ) : Cardinal)
      ≤ #ℝ := Cardinal.mk_set_le nonComputableReals
    _ = 𝔠 := Cardinal.mk_real

/-- **Union bound** specialising the partition to `ℝ`:
    `𝔠 = #ℝ ≤ #(computable) + #(non-computable)`. -/
private theorem mk_real_le_computable_add_nonComputable :
    (#ℝ : Cardinal) ≤ (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) +
        (#(↑nonComputableReals : Set ℝ) : Cardinal) := by
  have h1 :
      (#(↑(({r : ℝ | IsComputable r} : Set ℝ) ∪ nonComputableReals) : Set ℝ) : Cardinal) ≤
      (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) +
        (#(↑nonComputableReals : Set ℝ) : Cardinal) :=
    Cardinal.mk_union_le _ _
  rwa [computable_nonComputable_partition, Cardinal.mk_univ] at h1

/-- **Bootstrap lower bound**: the non-computable reals are at least ℵ₀-many.

    Suppose, for contradiction, `#(non-computable) < ℵ₀`. Combined with
    `card_computable_reals_le_aleph0`, the union bound forces `#ℝ ≤ ℵ₀ + ℵ₀ = ℵ₀`,
    contradicting `Cardinal.aleph0_lt_continuum` and `Cardinal.mk_real`. -/
private theorem aleph0_le_card_nonComputableReals :
    ℵ₀ ≤ (#(↑nonComputableReals : Set ℝ) : Cardinal) := by
  by_contra h
  push_neg at h
  have h_lt : (#(↑nonComputableReals : Set ℝ) : Cardinal) ≤ ℵ₀ := h.le
  have h_real_le_aleph0 : (#ℝ : Cardinal) ≤ ℵ₀ := by
    calc (#ℝ : Cardinal)
        ≤ (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) +
            (#(↑nonComputableReals : Set ℝ) : Cardinal) :=
              mk_real_le_computable_add_nonComputable
      _ ≤ ℵ₀ + ℵ₀ := add_le_add card_computable_reals_le_aleph0 h_lt
      _ = ℵ₀ := Cardinal.add_eq_self le_rfl
  rw [Cardinal.mk_real] at h_real_le_aleph0
  exact absurd h_real_le_aleph0 (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **Lower bound** for the main cardinality: `𝔠 ≤ #(non-computable)`.

    Combine the bootstrap `ℵ₀ ≤ #(non-computable)` with the union bound and
    cardinal absorption:
        𝔠 = #ℝ ≤ #(computable) + #(non-computable)
              ≤ ℵ₀ + #(non-computable)
              = #(non-computable). -/
theorem continuum_le_card_nonComputableReals :
    𝔠 ≤ (#(↑nonComputableReals : Set ℝ) : Cardinal) := by
  have h_absorb :
      ℵ₀ + (#(↑nonComputableReals : Set ℝ) : Cardinal) =
        (#(↑nonComputableReals : Set ℝ) : Cardinal) :=
    aleph0_add_of_ge aleph0_le_card_nonComputableReals
  calc 𝔠
      = #ℝ := Cardinal.mk_real.symm
    _ ≤ (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) +
          (#(↑nonComputableReals : Set ℝ) : Cardinal) :=
            mk_real_le_computable_add_nonComputable
    _ ≤ ℵ₀ + (#(↑nonComputableReals : Set ℝ) : Cardinal) :=
          add_le_add_left card_computable_reals_le_aleph0 _
    _ = (#(↑nonComputableReals : Set ℝ) : Cardinal) := h_absorb

/-- **Main S4 theorem — exact cardinality of non-computable reals**: 𝔠.

    The non-computable reals have the same cardinality as ℝ itself. In the
    cardinality sense, "almost all" reals are non-computable: removing the
    countable computable reals from ℝ leaves a set of full cardinality 𝔠. -/
theorem card_nonComputableReals_eq_continuum :
    (#(↑nonComputableReals : Set ℝ) : Cardinal) = 𝔠 :=
  le_antisymm card_nonComputableReals_le_continuum continuum_le_card_nonComputableReals

/-- **Turing's negative observation, formalised**: there exists a real number
    that is *not* computable.

    Proof by contradiction: if every real were computable, then
    `{r : ℝ | IsComputable r} = Set.univ`, hence `#ℝ ≤ ℵ₀` via
    `card_computable_reals_le_aleph0`. This contradicts
    `Cardinal.aleph0_lt_continuum` and `Cardinal.mk_real`.

    No explicit non-computable real (e.g. Chaitin's Ω, halting probability) is
    constructed — the existence is established purely by the cardinality gap. -/
theorem exists_non_computable_real : ∃ r : ℝ, ¬ IsComputable r := by
  by_contra h
  push_neg at h
  -- h : ∀ r, IsComputable r
  have h_eq : ({r : ℝ | IsComputable r} : Set ℝ) = Set.univ := by
    ext r
    simp [h r]
  have h_real_le_aleph0 : (#ℝ : Cardinal) ≤ ℵ₀ := by
    calc (#ℝ : Cardinal)
        = (#(↑({r : ℝ | IsComputable r} : Set ℝ) : Set ℝ) : Cardinal) := by
            rw [h_eq, Cardinal.mk_univ]
      _ ≤ ℵ₀ := card_computable_reals_le_aleph0
  rw [Cardinal.mk_real] at h_real_le_aleph0
  exact absurd h_real_le_aleph0 (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **Strict inclusion** `{r : ℝ | IsComputable r} ⊊ Set.univ`.

    Combines `Set.subset_univ` (the non-strict inclusion) with
    `exists_non_computable_real` (a witness in the complement). -/
theorem computable_reals_strict_ssubset_univ :
    HasSSubset.SSubset ({r : ℝ | IsComputable r} : Set ℝ) Set.univ := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h_univ_sub
  obtain ⟨r, hr⟩ := exists_non_computable_real
  exact hr (h_univ_sub (Set.mem_univ r))

/-- **Strict inequality on cardinalities**: `#(computable) < #ℝ`.

    Direct consequence of `card_computable_reals_eq_aleph0` and
    `Cardinal.mk_real` together with `Cardinal.aleph0_lt_continuum`. -/
theorem card_computable_reals_lt_card_reals :
    (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) < #ℝ := by
  rw [card_computable_reals_eq_aleph0, Cardinal.mk_real]
  exact Cardinal.aleph0_lt_continuum

/-- **Strict inequality on cardinalities**: `#(computable) < #(non-computable)`.

    Together with `card_computable_reals_eq_aleph0` and
    `card_nonComputableReals_eq_continuum`, this records the asymmetry: the
    computable reals are an ℵ₀-sized exception inside an otherwise
    continuum-sized field of non-computable reals. -/
theorem card_computable_lt_card_nonComputable :
    (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) <
      (#(↑nonComputableReals : Set ℝ) : Cardinal) := by
  rw [card_computable_reals_eq_aleph0, card_nonComputableReals_eq_continuum]
  exact Cardinal.aleph0_lt_continuum

/-! ## S5 — Cross-cardinal consolidation across the hierarchy layers

The cardinal results of S2-S4 (`card_computable_reals_eq_aleph0 = ℵ₀`,
`card_nonComputableReals_eq_continuum = 𝔠`) and the imported sibling
`AlgebraicNumbersCountable.card_algebraic_reals_eq_aleph0` together pin the
exact cardinal coordinates of every layer of the hierarchy
`ℚ ⊊ algebraic ⊊ computable ⊊ ℝ`.

This S5 deliverable packages three short consolidation theorems:

* `card_computable_reals_eq_card_algebraic_reals` — algebraic and computable
  reals share cardinality (both ℵ₀); the qualitative inclusion is strict, but
  the cardinal coordinate is the same.
* `card_nonComputableReals_eq_card_reals` — non-computable reals match ℝ
  cardinally; direct from `Cardinal.mk_real` and
  `card_nonComputableReals_eq_continuum`.
* `cardinality_trichotomy` — compact summary stating the three cardinalities
  (algebraic reals subtype, computable reals, non-computable reals).

The constructive (qualitative) inclusion `algebraic ⊆ computable` requires
exhibiting a Mathlib-`Computable` rational sequence converging to each
algebraic real (Sturm-chain or bisection-on-minimal-polynomial witnesses);
that is deferred to a later iteration. The cardinal statement
`#algebraic = #computable` recorded here is the cardinal coordinate of the
(still classical) inclusion.
-/

/-- **S5 lemma — cardinal coincidence of algebraic and computable reals**:
    both have cardinality ℵ₀, so as cardinals they are equal.

    The qualitative inclusion `algebraic ⊆ computable` is strict (every
    rational is algebraic, every algebraic is computable, but π and e are
    computable and not algebraic — the last fact is deferred to a future
    iteration formalising explicit computable transcendentals). At the
    cardinal level, however, both share ℵ₀, mirroring the slogan: "qualitative
    refinement preserves cardinality below 𝔠". -/
theorem card_computable_reals_eq_card_algebraic_reals :
    (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) =
      Cardinal.mk {x : ℝ // IsAlgebraic ℚ x} := by
  rw [card_computable_reals_eq_aleph0,
      AlgebraicNumbersCountable.card_algebraic_reals_eq_aleph0]

/-- **S5 lemma — cardinal coincidence of non-computable reals and ℝ**:
    `#(non-computable) = #ℝ = 𝔠`.

    The countable set of computable reals is a cardinality-zero deletion from
    ℝ: removing it leaves a set with the same cardinality as ℝ. This is the
    cardinal-level analogue of "almost all reals are non-computable". -/
theorem card_nonComputableReals_eq_card_reals :
    (#(↑nonComputableReals : Set ℝ) : Cardinal) = #ℝ := by
  rw [card_nonComputableReals_eq_continuum, Cardinal.mk_real]

/-- **S5 main — cardinality trichotomy across the hierarchy**:
    bundles the three cardinal facts that determine where each layer of
    `ℚ ⊊ algebraic ⊊ computable ⊊ ℝ` sits.

    Reads: algebraic reals and computable reals are both countably infinite
    (cardinality ℵ₀), while the non-computable reals form a continuum-sized
    set (cardinality 𝔠 = #ℝ). The strict cardinal inequality ℵ₀ < 𝔠 then
    explains why the topmost inclusion `computable ⊊ ℝ` must be strict, and
    why no countable enumeration of the computable reals can hope to cover ℝ.

    Compare with the sibling
    `AlgebraicNumbersCountableOQ02OQ03.cardinality_dichotomy`, which bundles
    the algebraic/transcendental dichotomy in the same form. -/
theorem cardinality_trichotomy :
    Cardinal.mk {x : ℝ // IsAlgebraic ℚ x} = ℵ₀ ∧
    (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) = ℵ₀ ∧
    (#(↑nonComputableReals : Set ℝ) : Cardinal) = 𝔠 :=
  ⟨AlgebraicNumbersCountable.card_algebraic_reals_eq_aleph0,
   card_computable_reals_eq_aleph0,
   card_nonComputableReals_eq_continuum⟩

/-! ## S6 — Set-theoretic structural API: nonempty, infinite, uncountable

The cardinal results of S2-S4 (`ℵ₀ ≤ #computable`, `#(non-computable) = 𝔠`)
immediately yield Set-level structural facts that are the natural form for
downstream consumers (e.g. measure theory, descriptive set theory, dense subset
constructions). This deliverable extracts the four standard predicates —
`Nonempty`, `Infinite`, `Countable`/`Uncountable` — across the partition,
keeping each proof as a one-liner that cites the corresponding S2-S4 cardinal
result.

* **Computable side** (cardinality ℵ₀):
  - `computable_reals_nonempty` — 0 is computable, so the set is inhabited.
  - `computable_reals_infinite` — every rational is computable and ℚ is infinite,
    so the set contains an infinite subset.

* **Non-computable side** (cardinality 𝔠):
  - `nonComputableReals_nonempty` — direct from `exists_non_computable_real`.
  - `nonComputableReals_uncountable` — from `#(non-computable) = 𝔠 > ℵ₀`.
  - `nonComputableReals_infinite` — every uncountable set is infinite.

These results round out the API and make the strict-inclusion structure of
`{r | IsComputable r} ⊊ ℝ` available in Set-level form without forcing callers
to round-trip through `Cardinal.mk`. -/

/-- **S6 — computable reals are nonempty**: 0 is a witness (via `zero_isComputable`). -/
theorem computable_reals_nonempty :
    ({r : ℝ | IsComputable r} : Set ℝ).Nonempty :=
  ⟨0, zero_isComputable⟩

/-- **S6 — computable reals are infinite**.

    The image of `Rat.cast : ℚ → ℝ` lies inside the computable reals (every
    rational is computable, by `rat_isComputable`), and the cast is injective,
    so its range is infinite. The computable reals then dominate an infinite
    subset and are themselves infinite. -/
theorem computable_reals_infinite :
    ({r : ℝ | IsComputable r} : Set ℝ).Infinite := by
  have h_subset : Set.range ((↑) : ℚ → ℝ) ⊆ {r : ℝ | IsComputable r} := by
    rintro x ⟨q, rfl⟩
    exact rat_isComputable q
  exact (Set.infinite_range_of_injective Rat.cast_injective).mono h_subset

/-- **S6 — non-computable reals are nonempty**, formalising Turing's negative
    observation in the Set-level form. Direct restatement of
    `exists_non_computable_real`. -/
theorem nonComputableReals_nonempty : nonComputableReals.Nonempty :=
  exists_non_computable_real

/-- **S6 — non-computable reals are uncountable**.

    From `card_nonComputableReals_eq_continuum` and `Cardinal.aleph0_lt_continuum`
    we get `ℵ₀ < #(non-computable)`, which by `le_aleph0_iff_set_countable`
    refutes countability.

    This is the strongest classical statement that "almost all reals are
    non-computable": no enumeration `ℕ → ℝ` can list them all. -/
theorem nonComputableReals_uncountable : ¬ nonComputableReals.Countable := by
  intro h
  have h_le : (#(↑nonComputableReals : Set ℝ) : Cardinal) ≤ ℵ₀ :=
    le_aleph0_iff_set_countable.mpr h
  rw [card_nonComputableReals_eq_continuum] at h_le
  exact absurd h_le (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **S6 — non-computable reals are infinite**.

    Direct from `nonComputableReals_uncountable`: every finite set is countable,
    so an uncountable set is infinite. -/
theorem nonComputableReals_infinite : nonComputableReals.Infinite := fun h =>
  nonComputableReals_uncountable h.countable

/-! ## S7 — Topological structure: the computable reals are dense

Despite being countable (S3) — hence both cardinality- and measure-negligible
inside ℝ — the computable reals are *topologically dense*: every real number is a
limit of computable reals. This is immediate from the density of ℚ in ℝ together
with `rat_isComputable` (every rational is a computable real).

Combined with `computable_reals_countable` (S3), it exhibits
`{r | IsComputable r}` as a **countable dense subset** of ℝ — a constructive
separability witness for ℝ using only computable points, and the topological
counterpart of the cardinality results in S2-S6: the computable reals are
"small" in cardinality (ℵ₀) yet "large" topologically (dense), the precise
combination that makes ℝ separable.

* `computable_reals_dense` — `Dense {r | IsComputable r}`.
* `closure_computable_reals_eq_univ` — closure-form restatement,
  `closure {r | IsComputable r} = Set.univ`.
-/

/-- **S7 — the computable reals are dense in ℝ**.

    The rationals are dense in ℝ (`Rat.denseRange_cast`) and every rational is a
    computable real (`rat_isComputable`), so the computable reals contain a dense
    subset and are therefore dense. -/
theorem computable_reals_dense : Dense {r : ℝ | IsComputable r} := by
  have h_subset : Set.range ((↑) : ℚ → ℝ) ⊆ {r : ℝ | IsComputable r} := by
    rintro x ⟨q, rfl⟩
    exact rat_isComputable q
  have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  exact hd.mono h_subset

/-- **S7 — closure form**: the topological closure of the computable reals is all
    of `ℝ`. A direct restatement of `computable_reals_dense` via
    `Dense.closure_eq`, convenient for downstream consumers that reason about
    closures rather than the `Dense` predicate. -/
theorem closure_computable_reals_eq_univ :
    closure {r : ℝ | IsComputable r} = Set.univ :=
  computable_reals_dense.closure_eq

/-! ## S8-prep — Topological complement: the non-computable reals are also dense

S7 showed `{r | IsComputable r}` is a countable dense subset of `ℝ`. Its complement
`nonComputableReals` is uncountable (S4, `nonComputableReals_uncountable`), yet a
priori one might still ask whether it is *topologically* visible — does it meet
every nonempty open set, or could it sit on a thin closed subset of `ℝ`?

The answer is that **the non-computable reals are dense too**. The argument is
purely cardinality-vs-countability:

* Every nonempty open `U ⊆ ℝ` contains an open interval `Ioo a b` with `a < b`
  (`IsOpen.exists_Ioo_subset`).
* `Ioo a b` has cardinality `𝔠` (`Cardinal.mk_Ioo_real`).
* If `U` missed `nonComputableReals` entirely then `U ⊆ {r | IsComputable r}`, so
  the interval `Ioo a b` would inherit countability from S3, forcing
  `𝔠 ≤ ℵ₀` — a contradiction with `Cardinal.aleph0_lt_continuum`.

Combined with S7, this exhibits `ℝ` as the disjoint union of two **simultaneously
dense** sets: the countable dense set of computable reals and the uncountable
dense set of non-computable reals. Topologically, computability is a
"measure-zero/dense" predicate: countably many points, but everywhere.

* `nonComputableReals_dense` — `Dense nonComputableReals`.
* `closure_nonComputableReals_eq_univ` — closure-form restatement.
-/

/-- **S8-prep — the non-computable reals are dense in `ℝ`**.

    Every nonempty open `U ⊆ ℝ` meets `nonComputableReals`. Proof by contradiction:
    if `U ∩ nonComputableReals = ∅`, then `U ⊆ {r | IsComputable r}`. Pick an
    open interval `Ioo a b ⊆ U` with `a < b` via `IsOpen.exists_Ioo_subset`. The
    interval is then countable (subset of a countable set), but
    `Cardinal.mk_Ioo_real` gives cardinality `𝔠 > ℵ₀`, contradiction. -/
theorem nonComputableReals_dense : Dense nonComputableReals := by
  rw [dense_iff_inter_open]
  intro U hU_open hU_ne
  obtain ⟨a, b, hab, hsub⟩ := hU_open.exists_Ioo_subset hU_ne
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hU_sub : U ⊆ {r : ℝ | IsComputable r} := by
    intro x hx
    by_contra hxn
    have hmem : x ∈ U ∩ nonComputableReals := ⟨hx, hxn⟩
    rw [h] at hmem
    exact hmem.elim
  have hIoo_sub : Set.Ioo a b ⊆ {r : ℝ | IsComputable r} := hsub.trans hU_sub
  have hIoo_count : (Set.Ioo a b).Countable := computable_reals_countable.mono hIoo_sub
  have hIoo_card_le : (#(↑(Set.Ioo a b) : Set ℝ) : Cardinal) ≤ ℵ₀ :=
    le_aleph0_iff_set_countable.mpr hIoo_count
  rw [Cardinal.mk_Ioo_real hab] at hIoo_card_le
  exact absurd hIoo_card_le (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **S8-prep — closure form**: the topological closure of the non-computable
    reals is all of `ℝ`. Direct restatement of `nonComputableReals_dense` via
    `Dense.closure_eq`. Together with S7's `closure_computable_reals_eq_univ`,
    this says both sides of the computable/non-computable partition are
    topologically maximal. -/
theorem closure_nonComputableReals_eq_univ :
    closure nonComputableReals = Set.univ :=
  nonComputableReals_dense.closure_eq

/-! ## S8 — Baire-category sharpening: meagre vs residual

S3 showed `{r | IsComputable r}` is countable (an `ℵ₀`/measure-theoretic
"smallness" statement). S7 and S8-prep showed that, despite countability, both
sides of the partition are topologically *dense*. S8 sharpens the smallness
side into the strongest classical sense of "topologically negligible":

* **Computable reals are meagre** in `ℝ` (first Baire category): they sit inside
  a countable union of nowhere-dense closed sets — explicitly, their singletons.
  This is a strictly stronger statement than countability for `ℝ`: it pins the
  category-theoretic size, not just the cardinality.
* **Non-computable reals are residual** in `ℝ`: they contain a dense `Gδ` set
  (themselves), i.e. they are "topologically generic" in Baire's sense — the
  category-theoretic counterpart of `card_nonComputableReals_eq_continuum`.

Combined with the existing density results, the topological profile is fixed:
the computable reals are **countable, dense, meagre** in `ℝ` — exactly the
profile of `ℚ` itself (cf. `IsGδ.setOf_irrational` /
`eventually_residual_irrational` for the analogous `Irrational` story in
Mathlib). The non-computable reals are then `Gδ`, dense, and comeagre.

Empty-interior corollaries on both sides are recorded for downstream use.

* `nonComputableReals_isGδ` — `IsGδ nonComputableReals`.
* `nonComputableReals_residual` — `nonComputableReals ∈ residual ℝ`.
* `computable_reals_meagre` — `IsMeagre {r : ℝ | IsComputable r}`.
* `interior_computable_reals_eq_empty` — `interior {r | IsComputable r} = ∅`.
* `interior_nonComputableReals_eq_empty` — `interior nonComputableReals = ∅`.
-/

/-- **S8 — the non-computable reals form a `Gδ` set in `ℝ`.**

    Direct from `computable_reals_countable` (S3): the complement of a countable
    set in a `T1` space is `Gδ` (`Set.Countable.isGδ_compl`). Modulo the trivial
    rewrite `nonComputableReals = {r | IsComputable r}ᶜ`, this is immediate.

    Mirror of `IsGδ.setOf_irrational` in `Mathlib.Topology.Instances.Irrational`,
    which is the same construction applied to `ℚ` instead of the computable
    reals. -/
theorem nonComputableReals_isGδ : IsGδ nonComputableReals := by
  have h_compl : nonComputableReals = ({r : ℝ | IsComputable r} : Set ℝ)ᶜ := by
    ext r; rfl
  rw [h_compl]
  exact computable_reals_countable.isGδ_compl

/-- **S8 — the non-computable reals are residual in `ℝ`.**

    Combining the `Gδ` structure (`nonComputableReals_isGδ`) with the density
    result (`nonComputableReals_dense`, S8-prep) via
    `residual_of_dense_Gδ`. Topologically, the non-computable reals are
    "generic" in Baire's sense — every comeagre property of a real holds for
    *some* non-computable real, and in fact for "most" of them.

    This is the Baire-category counterpart of
    `card_nonComputableReals_eq_continuum`: the non-computable reals are not
    only of full cardinality `𝔠` but also of full Baire category — a sharper
    "almost all reals are non-computable" statement than the cardinality result
    alone. -/
theorem nonComputableReals_residual : nonComputableReals ∈ residual ℝ :=
  residual_of_dense_Gδ nonComputableReals_isGδ nonComputableReals_dense

/-- **S8 — the computable reals are meagre in `ℝ`.**

    Immediate from `nonComputableReals_residual` together with the
    definitional unfolding `IsMeagre s ↔ sᶜ ∈ residual X` and
    `({r | IsComputable r})ᶜ = nonComputableReals`.

    This is strictly stronger than `computable_reals_countable` for spaces like
    `ℝ` that have no isolated points: meagre is a topological-category
    statement, countable is a cardinality statement, and the gap matters for
    downstream Baire-category arguments (e.g. "a generic real is not
    computable"). -/
theorem computable_reals_meagre : IsMeagre {r : ℝ | IsComputable r} := by
  have h_compl : ({r : ℝ | IsComputable r} : Set ℝ)ᶜ = nonComputableReals := by
    ext r; rfl
  unfold IsMeagre
  rw [h_compl]
  exact nonComputableReals_residual

/-- **S8 corollary — the computable reals have empty interior in `ℝ`.**

    From `nonComputableReals_dense` (S8-prep): the complement of the computable
    reals is dense, hence the interior of the computable reals is empty.

    This is the precise form of "the computable reals contain no open ball":
    every nonempty open subset of `ℝ` meets the non-computable reals. -/
theorem interior_computable_reals_eq_empty :
    interior {r : ℝ | IsComputable r} = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  have h_compl : ({r : ℝ | IsComputable r} : Set ℝ)ᶜ = nonComputableReals := by
    ext r; rfl
  rw [h_compl]
  exact nonComputableReals_dense

/-- **S8 corollary — the non-computable reals have empty interior in `ℝ`.**

    From `computable_reals_dense` (S7): the complement of the non-computable
    reals is dense, hence the interior of the non-computable reals is empty.

    Symmetric counterpart of `interior_computable_reals_eq_empty`: every
    nonempty open subset of `ℝ` meets the computable reals as well. The two
    together say the partition `{computable} ⊔ {non-computable}` has both sides
    with empty interior — neither half contains any open interval. -/
theorem interior_nonComputableReals_eq_empty :
    interior nonComputableReals = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  have h_compl : (nonComputableReals : Set ℝ)ᶜ = {r : ℝ | IsComputable r} := by
    ext r
    simp [nonComputableReals]
  rw [h_compl]
  exact computable_reals_dense

end AlgebraicNumbersCountableOQ02OQ04
