import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountable

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
- **S3** (this PR): full proof of `computable_reals_countable` via `decodeReal` +
  `Nat.Partrec.Code.exists_code` pipeline. **Build pending** — verification
  relies on the named Mathlib API (`Computable.encode`, `Computable.comp`,
  `Partrec.nat_iff`, `Nat.Partrec.Code.exists_code`, `Set.countable_range`,
  `Set.Countable.mono`, `tendsto_nhds_unique`, `Encodable.encode_injective`,
  `Part.some_injective`). With S3 landed, `card_computable_reals_le_aleph0`
  and `card_computable_reals_eq_aleph0` (from S2) become unconditional.

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
  simpa [Cardinal.mk_rat] using hcard

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

end AlgebraicNumbersCountableOQ02OQ04
