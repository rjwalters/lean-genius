/-
  Szemerédi Regularity Lemma — OQ-04: the two-level AFKS conclusion, packaged.

  Every prior OQ-04 file discharges an *ingredient* of the strong
  Alon–Fischer–Krivelevich–Szegedy regularity lemma:

  * the finiteness/termination engine (`SzemerediRegularityOQ04`),
  * the per-step energy increment and its `n`-independent equipartition count
    `N ≤ k²/ε⁴` (`…Assembly`, `…Bridge`, `…Product*`),
  * the tolerance dimension — regularity monotone in ε, the exceptional count
    antitone in ε (`…Tolerance`), and the AFKS *fine-level* predicate
    `IsAFKSFineRegular` with its up/down bridges (`…ToleranceBridge`).

  What was still missing (state.md "What remains open", **item 2**) is the
  *conclusion statement itself*: the full **two-level** object (i)–(iii) of the
  AFKS lemma as a single packaged `Prop`, threading the coarse partition, the
  refinement, and the dependent fine tolerance together.  This file supplies it
  and connects it to the tolerance-bridge tower.

  ## The pinned target (problem.md, formal statement (i)–(iii))

  A coarse partition `V₁..V_k` and a refinement `W₁..W_ℓ` with
  * **(i)** `W` refines `V` — every fine cell lies inside a coarse cell;
  * **(ii)** the coarse partition is `ε`-regular;
  * **(iii)** all but `ε·C(ℓ,2)` pairs `(W_a,W_b)` are `E(k)`-regular
    (the fine tolerance `E ≤ ε`, chosen after seeing `k`).

  ## What this file proves

  * `IsTwoLevelAFKSRegular G ε E coarse fine` — the packaged Prop bundling
    (i)–(iii) plus `E ≤ ε`.  (iii) is exactly `IsAFKSFineRegular` from
    `…ToleranceBridge`; (i) is the refinement relation `∀ W ∈ fine, ∃ Vc ∈
    coarse, W ⊆ Vc`.
  * `twoLevelAFKS_coarse_isRegular` / `twoLevelAFKS_fine_isRegular` — **both
    levels are classically `ε`-regular.**  The coarse one by projection (ii); the
    fine one *for free* via `isRegularPartition_of_afksFineRegular` (its strong
    `E`-guarantee dominates the coarse `ε`-test).  This is the formal statement of
    why the strong lemma refines — not merely restates — the classical one.
  * `twoLevelAFKS_of_isRegularPartition_fine` — **inhabitation / consistency.**
    Any genuinely `E`-regular partition (`E ≤ ε`) is a (degenerate, coarse=fine)
    two-level AFKS object, so the packaged predicate is satisfiable and correctly
    *weaker* than demanding a properly finer second level.
  * `twoLevelAFKS_mono_fine` / `twoLevelAFKS_mono_coarse` — the two-level object
    is monotone in both tolerances (inherited from the fine-level bridges), so a
    solution at strong `(ε, E)` transports to every weaker `(ε', E')`.

  Everything here is elementary order/set arithmetic over `Szemeredi.Core` and the
  `…ToleranceBridge` API — **no** energy machinery.  It is a *statement-level*
  contribution: it pins OQ-04's conclusion object in Lean and shows it sits
  correctly in the regularity hierarchy.  It does **not** construct the partition
  or bound `k` (item 3, the outer-loop assembly), which remains the open crux.
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularityOQ04Tolerance
import Proofs.SzemerediRegularityOQ04ToleranceBridge

namespace Szemeredi.RegularityOQ04TwoLevel

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Tolerance
  Szemeredi.RegularityOQ04ToleranceBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The two-level AFKS conclusion, packaged.**  A pair of partitions
    `(coarse, fine)` is a *two-level AFKS-regular* configuration at coarse
    tolerance `ε` and fine tolerance `E` when it realizes the full strong-lemma
    conclusion (i)–(iii):

    * **(i) refinement** — every fine cell `W` lies inside some coarse cell `Vc`
      (`fine` refines `coarse`);
    * **(ii) coarse regularity** — `coarse` is a classical `ε`-regular partition;
    * **(iii) fine almost-all-pairs regularity** — `fine` is AFKS-fine-regular at
      coarse budget `ε`, fine tolerance `E`: all but `ε·ℓ(ℓ−1)` ordered pairs are
      `E`-regular; plus the AFKS dependent-tolerance constraint `E ≤ ε`.

    This is the object whose *existence* (with a bound on `coarse.card`) the strong
    regularity lemma asserts; the outer-loop construction that produces it is item
    3 and is not part of this predicate. -/
def IsTwoLevelAFKSRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε E : ℚ) (coarse fine : Finset (Finset V)) : Prop :=
  IsRegularPartition G ε coarse ∧                         -- (ii)
  (∀ W ∈ fine, ∃ Vc ∈ coarse, W ⊆ Vc) ∧                   -- (i) fine refines coarse
  IsAFKSFineRegular G ε E fine ∧                           -- (iii)
  E ≤ ε                                                    -- dependent tolerance E(k) ≤ ε

/-- **(ii) projection.**  The coarse level of a two-level AFKS object is a
    classical `ε`-regular partition — by definition, but recorded as a named
    accessor for downstream consumers. -/
theorem twoLevelAFKS_coarse_isRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E : ℚ} {coarse fine : Finset (Finset V)}
    (h : IsTwoLevelAFKSRegular G ε E coarse fine) :
    IsRegularPartition G ε coarse :=
  h.1

/-- **The fine level is classically `ε`-regular, for free.**  The AFKS
    almost-all-pairs guarantee (iii) is stated at the *strong* fine tolerance
    `E ≤ ε`; since fewer pairs fail the coarse `ε`-test than the fine `E`-test
    (`isRegularPartition_of_afksFineRegular`), the fine partition already satisfies
    the classical `ε`-regularity budget.  This is the precise sense in which the
    strong lemma's fine level *refines* — rather than merely restates — the
    classical conclusion. -/
theorem twoLevelAFKS_fine_isRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E : ℚ} {coarse fine : Finset (Finset V)}
    (h : IsTwoLevelAFKSRegular G ε E coarse fine) :
    IsRegularPartition G ε fine :=
  isRegularPartition_of_afksFineRegular G h.2.2.1 h.2.2.2

/-- **The refinement relation (i)**, recorded as a named accessor: every fine cell
    lies inside a coarse cell. -/
theorem twoLevelAFKS_refines (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E : ℚ} {coarse fine : Finset (Finset V)}
    (h : IsTwoLevelAFKSRegular G ε E coarse fine) :
    ∀ W ∈ fine, ∃ Vc ∈ coarse, W ⊆ Vc :=
  h.2.1

/-- **Inhabitation / consistency.**  Any genuinely `E`-regular partition `P`
    (`E ≤ ε`) *is* a two-level AFKS object with `coarse = fine = P`:

    * (ii) `P` is `ε`-regular because it is `E`-regular and `E ≤ ε`
      (`isRegularPartition_of_isRegularPartition_fine`);
    * (i) `P` trivially refines itself (`W ⊆ W`);
    * (iii) `P` is AFKS-fine-regular at `(ε, E)` because its `E`-budget dominates
      into the coarse budget (`afksFineRegular_of_isRegularPartition`).

    This shows the packaged predicate is *satisfiable* — it is not vacuously false
    — and that it is correctly **weaker** than requiring a genuinely finer second
    level: the degenerate coarse = fine witness already qualifies.  (The
    mathematical content of OQ-04 is producing such a `P` with a bound on its size;
    that is item 3, not this lemma.) -/
theorem twoLevelAFKS_of_isRegularPartition_fine (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E : ℚ} {P : Finset (Finset V)}
    (hP : IsRegularPartition G E P) (hEε : E ≤ ε) :
    IsTwoLevelAFKSRegular G ε E P P := by
  refine ⟨?_, ?_, ?_, hEε⟩
  · exact isRegularPartition_of_isRegularPartition_fine G hP hEε
  · exact fun W _ => ⟨W, ‹_›, Finset.Subset.refl W⟩
  · exact afksFineRegular_of_isRegularPartition G hP hEε

/-- **Monotone in the fine tolerance.**  Relaxing the fine tolerance `E ≤ E'`
    (still `E' ≤ ε`) preserves the two-level AFKS conclusion: the coarse level and
    the refinement are untouched, and the fine-level guarantee only weakens its
    per-pair demand while its exceptional set shrinks (`afksFineRegular_mono_fine`). -/
theorem twoLevelAFKS_mono_fine (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E E' : ℚ} {coarse fine : Finset (Finset V)}
    (h : IsTwoLevelAFKSRegular G ε E coarse fine) (hEE' : E ≤ E') (hE'ε : E' ≤ ε) :
    IsTwoLevelAFKSRegular G ε E' coarse fine :=
  ⟨h.1, h.2.1, afksFineRegular_mono_fine G h.2.2.1 hEE', hE'ε⟩

/-- **Monotone in the coarse tolerance.**  Enlarging the coarse tolerance `ε ≤ ε'`
    (keeping `E ≤ ε ≤ ε'`) preserves the two-level AFKS conclusion: (ii) coarse
    `ε`-regularity lifts to `ε'` (`isRegularPartition_mono`), the refinement is
    unchanged, and (iii) the fine budget only grows (`afksFineRegular_mono_coarse`). -/
theorem twoLevelAFKS_mono_coarse (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε' E : ℚ} {coarse fine : Finset (Finset V)}
    (h : IsTwoLevelAFKSRegular G ε E coarse fine) (hεε' : ε ≤ ε') :
    IsTwoLevelAFKSRegular G ε' E coarse fine :=
  ⟨isRegularPartition_mono G h.1 hεε',
    h.2.1,
    afksFineRegular_mono_coarse G h.2.2.1 hεε',
    le_trans h.2.2.2 hεε'⟩

end Szemeredi.RegularityOQ04TwoLevel
