/-
  Erdős Problem #1 (Distinct Subset Sums): the second-moment lower bound.

  A finite set `A ⊆ ℕ` has *distinct subset sums* (DSS) if its `2^{|A|}` subsets
  all have different sums.  Erdős' \$500 conjecture asks whether `max(A) ≥ c·2^n`
  for an absolute constant `c`.  The gallery already formalises:

    * the **counting bound** `max(A) ≥ 2^n / n`  (`erdos-1-oq-01`), and
    * the **Dubroff–Fox–Xu entropy bound** `max(A) ≥ √(2/π)·2^n/√n`
      (`erdos-1-oq-02`), whose probability-free core is the
      *second-moment identity* `∑_{T⊆A}(2·Σ_T − S)² = 2^n·Σ_{i∈A} i²` already
      proved in `Proofs.Erdos1OQ02`.

  That file (`Erdos1OQ02.lean`, lines 168–171) explicitly flags a road **not**
  taken: the *pure* second-moment route, which lower-bounds the spread of the
  `2^n` distinct subset sums by `(M³−M)/12` (`M = 2^n`).  The missing ingredient
  is a general extremal fact about distinct integers — not in Mathlib — which we
  supply here:

  ### The extremal minimum-variance lemma (general, reusable)

  `distinct_int_variance_lower`: for **any** finite set `Y ⊆ ℤ` (its elements are
  automatically distinct), with `M = |Y|`,

      M²·(M² − 1)  ≤  12·( M·∑_{y∈Y} y²  −  (∑_{y∈Y} y)² ).

  Equivalently `Var(Y) ≥ (M²−1)/12`: among `M` distinct integers, the consecutive
  block `0,1,…,M−1` minimises the variance.  The proof is elementary:

    * `pairwise_sq_eq`  — the identity `∑_{i,j} (f i − f j)² = 2(M·∑f² − (∑f)²)`;
    * enumerate `Y` in increasing order via `Finset.orderEmbOfFin`, a strictly
      monotone `e : Fin M ↪o ℤ`; for `i ≤ j` integers force a gap
      `e j − e i ≥ j − i` (`strictMono_displacement`), so termwise
      `(i − j)² ≤ (e i − e j)²` (`termwise`);
    * summing, `∑_{i,j∈range M}(i−j)² ≤ ∑_{a,b∈Y}(a−b)²`, and the left side has the
      exact value `M²(M²−1)/6` (`sum_range_id_int`, `sum_range_sq_int`).

  ### Application to Erdős #1

  Taking `Y` to be the `2^n` distinct *doubled deviations* `{2·Σ_T − S : T ⊆ A}`
  (distinct because `A` is DSS), `∑_{y∈Y} y² = 2^n·Σ_{i∈A} i²`
  (`second_moment_identity`), and since `(∑ y)² ≥ 0` the extremal lemma yields,
  after dividing by `4^n > 0`,

      `dss_sumsq_lower` :   4^n − 1  ≤  12·∑_{i∈A} i² .

  Bounding `∑ i² ≤ n·N²` gives the max-element form

      `dss_max_lower`  :   4^n  ≤  12·n·N² + 1 ,   i.e.  max(A) ≳ 2^n/√(12n).

  This is a *self-contained, structurally independent* derivation of a `√n`
  improvement over the counting bound `2^n/n`.  Its constant `1/√12 ≈ 0.289` is
  weaker than DFX's `√(2/π) ≈ 0.798` (as the `Erdos1OQ02` note predicts), but the
  route is completely elementary — no probability, no entropy — and the extremal
  lemma is a general tool of independent interest.

  Status: fully elementary, 0 sorries, 0 axioms beyond Mathlib's foundational
  `propext`/`Classical.choice`/`Quot.sound`.
-/
import Proofs.Erdos1OQ02
import Mathlib

open Finset

namespace Erdos1Wip01OQ02

/-! ## Part I: Closed forms for the consecutive-block reference sums -/

/-- Gauss' sum over `range M`, in `ℤ`: `2·∑_{i<M} i = M(M−1)`. -/
lemma sum_range_id_int (M : ℕ) : 2 * ∑ i ∈ range M, (i : ℤ) = (M : ℤ) * ((M : ℤ) - 1) := by
  induction M with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

/-- Square-pyramidal sum over `range M`, in `ℤ`: `6·∑_{i<M} i² = (M−1)·M·(2M−1)`. -/
lemma sum_range_sq_int (M : ℕ) :
    6 * ∑ i ∈ range M, (i : ℤ) ^ 2 = ((M : ℤ) - 1) * M * (2 * M - 1) := by
  induction M with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

/-! ## Part II: The pairwise-difference identity -/

/-- **Pairwise-square identity.**  For a function `f` on a finite set `s`,
    `∑_{i,j∈s} (f i − f j)² = 2·( |s|·∑ f²  −  (∑ f)² )`.  (Twice the variance,
    rescaled by `|s|`.) -/
lemma pairwise_sq_eq {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2
      = 2 * ((s.card : ℤ) * (∑ i ∈ s, (f i) ^ 2) - (∑ i ∈ s, f i) ^ 2) := by
  have inner : ∀ a ∈ s, ∑ j ∈ s, (f a - f j) ^ 2
      = (s.card : ℤ) * (f a) ^ 2 - 2 * (f a) * (∑ j ∈ s, f j) + (∑ j ∈ s, (f j) ^ 2) := by
    intro a _; simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
  have hcross : ∑ a ∈ s, 2 * (f a) * (∑ j ∈ s, f j) = 2 * (∑ i ∈ s, f i) ^ 2 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  rw [Finset.sum_congr rfl inner, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcross]; ring

/-! ## Part III: Monotone enumeration and the termwise gap bound -/

/-- Reindex a sum over `Y ⊆ ℤ` through its increasing enumeration
    `Finset.orderEmbOfFin`. -/
lemma reindex (Y : Finset ℤ) {M : ℕ} (h : Y.card = M) (F : ℤ → ℤ) :
    ∑ i : Fin M, F (Y.orderEmbOfFin h i) = ∑ a ∈ Y, F a := by
  have himg : (Finset.univ : Finset (Fin M)).image (Y.orderEmbOfFin h) = Y := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha; simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
      obtain ⟨i, rfl⟩ := ha; exact Y.orderEmbOfFin_mem h i
    · rw [Finset.card_image_of_injective _ (Y.orderEmbOfFin h).injective, Finset.card_univ,
        Fintype.card_fin, h]
  calc ∑ i : Fin M, F (Y.orderEmbOfFin h i)
      = ∑ a ∈ (Finset.univ : Finset (Fin M)).image (Y.orderEmbOfFin h), F a :=
        (Finset.sum_image (fun x _ y _ hxy => (Y.orderEmbOfFin h).injective hxy)).symm
    _ = ∑ a ∈ Y, F a := by rw [himg]

/-- A strictly monotone `ℤ`-valued map on `Fin M` moves by at least the index gap:
    if `j = i + k` then `e j − e i ≥ k`.  (Distinct integers are spaced `≥ 1` apart.) -/
lemma strictMono_displacement {M : ℕ} (e : Fin M → ℤ) (he : StrictMono e) :
    ∀ k : ℕ, ∀ i j : Fin M, (j : ℕ) = (i : ℕ) + k → (k : ℤ) ≤ e j - e i := by
  intro k
  induction k with
  | zero => intro i j hj; have : i = j := Fin.ext (by omega); simp [this]
  | succ n ih =>
    intro i j hj
    have hlt : (i : ℕ) + n < M := by omega
    let j' : Fin M := ⟨(i : ℕ) + n, by omega⟩
    have h1 : (n : ℤ) ≤ e j' - e i := ih i j' rfl
    have hj'j : j' < j := by rw [Fin.lt_def]; simp only [j']; omega
    have h2 : e j' < e j := he hj'j
    push_cast; omega

/-- **Termwise gap domination.**  For a strictly monotone `e : Fin M → ℤ`,
    `(i − j)² ≤ (e i − e j)²`: spreading distinct integers can only widen gaps. -/
lemma termwise {M : ℕ} (e : Fin M → ℤ) (he : StrictMono e) (i j : Fin M) :
    ((i : ℤ) - (j : ℤ)) ^ 2 ≤ (e i - e j) ^ 2 := by
  rcases le_total (i : ℕ) (j : ℕ) with hij | hij
  · have hd := strictMono_displacement e he ((j : ℕ) - (i : ℕ)) i j (by omega)
    rw [Nat.cast_sub hij] at hd
    have h0 : (0 : ℤ) ≤ (j : ℤ) - (i : ℤ) := by
      have : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
      linarith
    nlinarith [hd, h0]
  · have hd := strictMono_displacement e he ((i : ℕ) - (j : ℕ)) j i (by omega)
    rw [Nat.cast_sub hij] at hd
    have h0 : (0 : ℤ) ≤ (i : ℤ) - (j : ℤ) := by
      have : (j : ℤ) ≤ (i : ℤ) := by exact_mod_cast hij
      linarith
    nlinarith [hd, h0]

/-! ## Part IV: The extremal minimum-variance lemma -/

/-- **Minimum variance of `M` distinct integers (0 axioms).**  For any finite set
    `Y ⊆ ℤ` with `M = |Y|`,

      `M²·(M² − 1) ≤ 12·( M·∑_{y∈Y} y² − (∑_{y∈Y} y)² )`,

    i.e. the variance of `M` distinct integers is at least `(M²−1)/12`, with equality
    for a consecutive block.  Not currently in Mathlib. -/
theorem distinct_int_variance_lower (Y : Finset ℤ) :
    (Y.card : ℤ) ^ 2 * ((Y.card : ℤ) ^ 2 - 1)
      ≤ 12 * ((Y.card : ℤ) * (∑ a ∈ Y, a ^ 2) - (∑ a ∈ Y, a) ^ 2) := by
  obtain ⟨M, hM⟩ : ∃ M, Y.card = M := ⟨Y.card, rfl⟩
  have he : StrictMono (⇑(Y.orderEmbOfFin hM)) := (Y.orderEmbOfFin hM).strictMono
  have hPW : ∑ a ∈ Y, ∑ b ∈ Y, (a - b) ^ 2
      = 2 * ((Y.card : ℤ) * (∑ a ∈ Y, a ^ 2) - (∑ a ∈ Y, a) ^ 2) := by
    have := pairwise_sq_eq Y (fun x => x); simpa using this
  have hV : 6 * (∑ i ∈ range M, ∑ j ∈ range M, ((i : ℤ) - (j : ℤ)) ^ 2)
      = (M : ℤ) ^ 2 * ((M : ℤ) ^ 2 - 1) := by
    have hpr := pairwise_sq_eq (range M) (fun n => (n : ℤ))
    rw [Finset.card_range] at hpr
    rw [hpr]; nlinarith [sum_range_id_int M, sum_range_sq_int M]
  have hVle : (∑ i ∈ range M, ∑ j ∈ range M, ((i : ℤ) - (j : ℤ)) ^ 2)
      ≤ ∑ a ∈ Y, ∑ b ∈ Y, (a - b) ^ 2 := by
    have hRe : ∑ a ∈ Y, ∑ b ∈ Y, (a - b) ^ 2
        = ∑ i : Fin M, ∑ j : Fin M, ((Y.orderEmbOfFin hM) i - (Y.orderEmbOfFin hM) j) ^ 2 := by
      rw [← reindex Y hM (fun a => ∑ b ∈ Y, (a - b) ^ 2)]
      apply Finset.sum_congr rfl; intro i _
      rw [← reindex Y hM (fun b => ((Y.orderEmbOfFin hM) i - b) ^ 2)]
    have hLe : ∑ i ∈ range M, ∑ j ∈ range M, ((i : ℤ) - (j : ℤ)) ^ 2
        = ∑ i : Fin M, ∑ j : Fin M, ((i : ℤ) - (j : ℤ)) ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range M, ((i : ℤ) - (j : ℤ)) ^ 2)]
      apply Finset.sum_congr rfl; intro i _
      rw [← Fin.sum_univ_eq_sum_range (fun j => ((i : ℤ) - (j : ℤ)) ^ 2)]
    rw [hRe, hLe]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact termwise (⇑(Y.orderEmbOfFin hM)) he i j
  rw [hM]
  rw [hM] at hPW
  rw [hPW] at hVle
  linarith [hV, hVle]

/-! ## Part V: The second-moment lower bound for Erdős #1 -/

/-- **Second-moment sum-of-squares bound (0 axioms).**  Any distinct-subset-sums set
    `A` of size `n` has `∑_{i∈A} i² ≥ (4^n − 1)/12`.  Proof: the `2^n` doubled
    deviations are distinct integers with `∑ y² = 2^n·∑ i²`; the minimum-variance
    lemma forces their spread, and dividing by `4^n` gives the bound. -/
theorem dss_sumsq_lower (A : Finset ℕ) (hDSS : hasDistinctSubsetSums A) :
    (4 : ℤ) ^ A.card - 1 ≤ 12 * ∑ i ∈ A, (i : ℤ) ^ 2 := by
  set dev : Finset ℕ → ℤ := fun T => 2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ A, (i : ℤ) with hdev
  set Y : Finset ℤ := A.powerset.image dev with hY
  have hinj : Set.InjOn dev (A.powerset : Set (Finset ℕ)) :=
    Erdos1OQ02.doubledDrop_injOn_of_distinct hDSS
  have hcard : Y.card = 2 ^ A.card := by
    rw [hY, Finset.card_image_of_injOn hinj, Finset.card_powerset]
  have hsq : ∑ y ∈ Y, y ^ 2 = 2 ^ A.card * ∑ i ∈ A, (i : ℤ) ^ 2 := by
    rw [hY, Finset.sum_image (fun x hx y hy h => hinj (by simpa using hx) (by simpa using hy) h)]
    exact Erdos1OQ02.second_moment_identity A
  have hext := distinct_int_variance_lower Y
  rw [hcard, hsq] at hext
  push_cast at hext
  have hsumsq : (0 : ℤ) ≤ (∑ a ∈ Y, a) ^ 2 := sq_nonneg _
  have hpos : (0 : ℤ) < 2 ^ A.card := by positivity
  have h4 : ((2 : ℤ) ^ A.card) ^ 2 = 4 ^ A.card := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  nlinarith [hext, hsumsq, hpos, h4, sq_nonneg ((2 : ℤ) ^ A.card)]

/-- **Max-element form (0 axioms).**  If every element of a distinct-subset-sums set
    `A` of size `n` is `≤ N`, then `4^n ≤ 12·n·N² + 1`, i.e. `N = max(A) ≳ 2^n/√(12n)`
    — a `√n` improvement over the counting bound `2^n/n`. -/
theorem dss_max_lower (A : Finset ℕ) (N : ℕ) (hDSS : hasDistinctSubsetSums A)
    (hN : ∀ a ∈ A, a ≤ N) :
    (4 : ℤ) ^ A.card ≤ 12 * A.card * N ^ 2 + 1 := by
  have hb := dss_sumsq_lower A hDSS
  have hbound : ∑ i ∈ A, (i : ℤ) ^ 2 ≤ A.card * N ^ 2 := by
    calc ∑ i ∈ A, (i : ℤ) ^ 2 ≤ ∑ _i ∈ A, ((N : ℤ)) ^ 2 := by
          apply Finset.sum_le_sum; intro i hi
          have : (i : ℤ) ≤ N := by exact_mod_cast hN i hi
          have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
          nlinarith [this, hi0]
      _ = A.card * (N : ℤ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  push_cast at hb ⊢
  nlinarith [hb, hbound]

/-- **The second-moment route beats counting.**  For `n ≥ 1` the second-moment bound
    `∑ i² ≥ (4^n−1)/12` is genuinely a `√n`-type statement: combined with
    `∑ i² ≤ n·max(A)²` it gives `12·n·max(A)² ≥ 4^n − 1`, whereas the counting bound
    only gives `n·max(A) ≥ 2^n − 1`.  Here we record the clean comparison that the
    bound is non-vacuous (positive right-hand growth) for every nonempty `A`. -/
theorem dss_sumsq_lower_pos (A : Finset ℕ) (hDSS : hasDistinctSubsetSums A)
    (hne : A.Nonempty) :
    1 ≤ ∑ i ∈ A, (i : ℤ) ^ 2 := by
  have hb := dss_sumsq_lower A hDSS
  have hcard : 1 ≤ A.card := hne.card_pos
  have h4 : (4 : ℤ) ^ A.card ≥ 4 ^ 1 := by
    apply pow_le_pow_right₀ (by norm_num) hcard
  nlinarith [hb, h4]

end Erdos1Wip01OQ02
