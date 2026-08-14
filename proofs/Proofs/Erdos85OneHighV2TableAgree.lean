import Proofs.Erdos85OneHighV2Exclusion

/-!
# Relevant-coordinate transport for the exact v2 generator

Audit of every `table` read in `oneHighFamilyV2Clauses profile table`:

* `oneHighFamilyV2UpperTableClauses` — reads `table c j` exactly for
  `(c, j) ∈ oneHighFamilyTablePairs` (upper non-mate pairs).
* `oneHighFamilyV2LexClauses` — no table reads.
* `oneHighFamilyV2F1Clauses` (lower pass) — reads `table j c` for
  `(c, j) ∈ oneHighFamilyV2LowerTablePairs`; the swapped coordinate
  `(j, c)` is again an upper non-mate pair.
* `oneHighFamilyV2PairedCommonClauses`, `oneHighFamilyV2F2Clauses`,
  `oneHighFamilyV2F3aClauses` — no table reads.
* `oneHighFamilyV2F3bBlockStep` — reads
  `oneHighFamilyTableGet table c (j ^^^ 1)` and
  `oneHighFamilyTableGet table j (c ^^^ 1)` for
  `(c, j) ∈ oneHighFamilyTablePairs`; `oneHighFamilyTableGet`
  normalises through `min`/`max` back into the upper non-mate pairs.

Hence the generator depends on a table only through its 24 upper
non-mate coordinates, and any two tables agreeing there produce the
same generator state, the same `Std.Sat.CNF`, and transportable
`OneHighFamilyV2CheckedUnsat` evidence.  This is the agreement notion
the orbit-cover socket needs: artifact tables set only these 24
coordinates, while graph tables may be nonzero elsewhere.
-/

namespace Erdos85

/-- Two miss tables agree on every coordinate the exact v2 generator
reads. -/
def OneHighTableRelevantAgree (t u : OneHighMissTable) : Prop :=
  ∀ pair ∈ oneHighFamilyTablePairs, t pair.1 pair.2 = u pair.1 pair.2

theorem OneHighTableRelevantAgree.symm {t u : OneHighMissTable}
    (h : OneHighTableRelevantAgree t u) : OneHighTableRelevantAgree u t :=
  fun pair hmem => (h pair hmem).symm

/-- Congruence for the shared fold driver: pointwise-equal steps on the
list's members give equal runs. -/
theorem oneHighFamilyRunList_congr {α : Type} (xs : List α)
    (f g : α → OneHighFamilyGenState → OneHighFamilyGenState)
    (h : ∀ x ∈ xs, ∀ st, f x st = g x st) :
    ∀ st, oneHighFamilyRunList xs f st = oneHighFamilyRunList xs g st := by
  unfold oneHighFamilyRunList
  induction xs with
  | nil => intro st; rfl
  | cons a l ih =>
      intro st
      simp only [List.foldl_cons]
      rw [h a (List.mem_cons_self ..) st]
      exact ih (fun x hx st => h x (List.mem_cons_of_mem a hx) st) _

/-- The lower-pass read coordinates are upper non-mate pairs. -/
theorem oneHighFamilyV2LowerTablePairs_swap_mem :
    ∀ pair ∈ oneHighFamilyV2LowerTablePairs,
      (pair.2, pair.1) ∈ oneHighFamilyTablePairs := by decide

/-- The first F3b read coordinate is an upper non-mate pair. -/
theorem oneHighFamilyTablePairs_f3bLeft_mem :
    ∀ pair ∈ oneHighFamilyTablePairs,
      (min pair.1 (pair.2 ^^^ 1), max pair.1 (pair.2 ^^^ 1)) ∈
        oneHighFamilyTablePairs := by decide

/-- The second F3b read coordinate is an upper non-mate pair. -/
theorem oneHighFamilyTablePairs_f3bRight_mem :
    ∀ pair ∈ oneHighFamilyTablePairs,
      (min pair.2 (pair.1 ^^^ 1), max pair.2 (pair.1 ^^^ 1)) ∈
        oneHighFamilyTablePairs := by decide

theorem oneHighFamilyV2UpperTableClauses_congr (a : Nat)
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u) :
    oneHighFamilyV2UpperTableClauses a t =
      oneHighFamilyV2UpperTableClauses a u := by
  unfold oneHighFamilyV2UpperTableClauses
  refine oneHighFamilyRunList_congr _ _ _ (fun pair hmem st => ?_) _
  rcases pair with ⟨c, j⟩
  have hcj : t c j = u c j := h (c, j) hmem
  simp only [oneHighFamilyTablePairStep, hcj]

theorem oneHighFamilyV2LexClauses_congr (a : Nat)
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u) :
    oneHighFamilyV2LexClauses a t = oneHighFamilyV2LexClauses a u := by
  unfold oneHighFamilyV2LexClauses
  rw [oneHighFamilyV2UpperTableClauses_congr a h]

theorem oneHighFamilyV2F1Clauses_congr (a : Nat)
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u) :
    oneHighFamilyV2F1Clauses a t = oneHighFamilyV2F1Clauses a u := by
  unfold oneHighFamilyV2F1Clauses
  rw [oneHighFamilyV2LexClauses_congr a h]
  refine oneHighFamilyRunList_congr _ _ _ (fun pair hmem st => ?_) _
  rcases pair with ⟨c, j⟩
  have hjc : t j c = u j c :=
    h (j, c) (oneHighFamilyV2LowerTablePairs_swap_mem (c, j) hmem)
  simp only [oneHighFamilyV2LowerTablePairStep, hjc]

theorem oneHighFamilyV2PairedCommonClauses_congr (a : Nat)
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u) :
    oneHighFamilyV2PairedCommonClauses a t =
      oneHighFamilyV2PairedCommonClauses a u := by
  unfold oneHighFamilyV2PairedCommonClauses
  rw [oneHighFamilyV2F1Clauses_congr a h]

theorem oneHighFamilyV2F2Clauses_congr (a : Nat)
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u) :
    oneHighFamilyV2F2Clauses a t = oneHighFamilyV2F2Clauses a u := by
  unfold oneHighFamilyV2F2Clauses
  rw [oneHighFamilyV2PairedCommonClauses_congr a h]

theorem oneHighFamilyV2F3aClauses_congr (a : Nat)
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u) :
    oneHighFamilyV2F3aClauses a t = oneHighFamilyV2F3aClauses a u := by
  unfold oneHighFamilyV2F3aClauses
  rw [oneHighFamilyV2F2Clauses_congr a h]

/-- Agreement on the read coordinates yields the same exact v2 generator
state. -/
theorem oneHighFamilyV2Clauses_congr (profile : Nat)
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u) :
    oneHighFamilyV2Clauses profile t = oneHighFamilyV2Clauses profile u := by
  unfold oneHighFamilyV2Clauses
  rw [oneHighFamilyV2F3aClauses_congr profile h]
  refine oneHighFamilyRunList_congr _ _ _ (fun pair hmem st => ?_) _
  rcases pair with ⟨c, j⟩
  have hl : t (min c (j ^^^ 1)) (max c (j ^^^ 1)) =
      u (min c (j ^^^ 1)) (max c (j ^^^ 1)) :=
    h _ (oneHighFamilyTablePairs_f3bLeft_mem (c, j) hmem)
  have hr : t (min j (c ^^^ 1)) (max j (c ^^^ 1)) =
      u (min j (c ^^^ 1)) (max j (c ^^^ 1)) :=
    h _ (oneHighFamilyTablePairs_f3bRight_mem (c, j) hmem)
  simp only [oneHighFamilyV2F3bBlockStep, oneHighFamilyV2F3bFinish,
    oneHighFamilyTableGet, hl, hr]

/-- Agreement on the read coordinates yields the same `Std.Sat.CNF`. -/
theorem oneHighFamilyV2SatCnf_congr (profile : Nat)
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u) :
    oneHighFamilyV2SatCnf profile t = oneHighFamilyV2SatCnf profile u := by
  unfold oneHighFamilyV2SatCnf
  rw [oneHighFamilyV2Clauses_congr profile h]

/-- Checked-UNSAT evidence transports across relevant agreement.  This is
the repair piece for the orbit-cover socket: certificates checked against
artifact tables apply to any graph table agreeing on the 24 read
coordinates. -/
theorem OneHighFamilyV2CheckedUnsat.transport {profile : Nat}
    {t u : OneHighMissTable} (h : OneHighTableRelevantAgree t u)
    (hc : OneHighFamilyV2CheckedUnsat profile t) :
    OneHighFamilyV2CheckedUnsat profile u where
  nonzero := by
    rw [← oneHighFamilyV2Clauses_congr profile h]
    exact hc.nonzero
  unsat := by
    rw [← oneHighFamilyV2SatCnf_congr profile h]
    exact hc.unsat

/-- Canonical normaliser: zero outside the read coordinates. -/
def oneHighTableRestrict (t : OneHighMissTable) : OneHighMissTable :=
  fun c j => if (c, j) ∈ oneHighFamilyTablePairs then t c j else 0

theorem oneHighTableRestrict_relevantAgree (t : OneHighMissTable) :
    OneHighTableRelevantAgree t (oneHighTableRestrict t) := by
  intro pair hmem
  rcases pair with ⟨c, j⟩
  unfold oneHighTableRestrict
  rw [if_pos hmem]

end Erdos85
