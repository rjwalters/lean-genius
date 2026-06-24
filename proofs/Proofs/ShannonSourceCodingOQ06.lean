/-
  Universal Source Coding: the Incompressibility / Counting Bound

  Open question oq-06 of the Shannon Source Coding entry asks about *universal*
  compression (Lempel-Ziv / Kolmogorov complexity): reaching the entropy rate
  without knowing the source distribution. The full Lempel-Ziv analysis is far
  beyond a single Lean session, but its converse — the reason *no* universal
  scheme can beat the entropy rate — rests on a clean, finite, distribution-free
  fact: a counting (pigeonhole) bound. This file formalizes that bound with no
  axioms and no sorries.

  Setup. A *lossless binary code* on a finite message set `α` is an injective
  map `f : α → List Bool`: distinct messages get distinct binary codewords, so
  the original message is always recoverable. This is exactly "unique
  decodability" at the level of single symbols, and it requires nothing about
  the source distribution — the heart of *universal* coding.

  Key results:

  1. `sum_two_pow_range`         : ∑_{k<L} 2^k = 2^L − 1
                                   (there are 2^L − 1 binary strings of length < L).
  2. `compressible_count_le`     : for an injective code, the number of messages
                                   whose codeword is shorter than `L` bits is at
                                   most `2^L − 1`.  (Incompressibility.)
  3. `compressible_count_lt`     : ... strictly less than `2^L`.
  4. `exists_long_codeword`      : if there are at least `2^L` messages, *some*
                                   message needs a codeword of length ≥ `L`.
                                   No lossless code compresses everything; the
                                   worst-case length is ≥ log₂(#messages).
  5. `compressible_filter_card_le`: the same bound stated for the explicit
                                   `Finset` of "compressible" messages.

  Together these say: *whatever* code you use (universal or not), at most a
  `2^{-c}` fraction of messages can be compressed by `c` bits below the
  blocklength — the rigorous floor underneath universal source coding and
  Kolmogorov-complexity incompressibility.

  Claude Shannon (1948); Kolmogorov / Lempel-Ziv (incompressibility).

  Axioms: 0
  Sorries: 0
-/
import Mathlib

namespace InformationTheory.UniversalSourceCoding

open Finset

/-- A lossless binary code on a message set `α` is an injective assignment of a
binary string (`List Bool`) to each message: distinct messages receive distinct
codewords, hence the message can always be recovered.  No assumption is made on
the source distribution — this is the universal/distribution-free setting. -/
def IsLossless {α : Type*} (f : α → List Bool) : Prop := Function.Injective f

/-- There are exactly `2^L − 1` binary strings of length strictly less than `L`,
because `∑_{k<L} 2^k = 2^L − 1`. -/
theorem sum_two_pow_range (L : ℕ) :
    ∑ k ∈ Finset.range L, 2 ^ k = 2 ^ L - 1 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    omega

/-- **Incompressibility (counting bound).**  For any lossless binary code
`f : α → List Bool` on a finite message set, the number of messages whose
codeword has length `< L` is at most `2^L − 1`.

The proof is a pigeonhole: each short codeword is a binary string of length
`< L`, and there are only `2^L − 1` such strings.  Concretely we inject the
"compressible" messages into `Σ k : Fin L, (binary strings of length k)`, whose
cardinality is `∑_{k<L} 2^k = 2^L − 1`. -/
theorem compressible_count_le {α : Type*} [Fintype α]
    {f : α → List Bool} (hf : IsLossless f) (L : ℕ) :
    Fintype.card {x : α // (f x).length < L} ≤ 2 ^ L - 1 := by
  -- Send a short message to (its length as an index, its codeword as a vector).
  let Φ : {x : α // (f x).length < L} → Σ k : Fin L, List.Vector Bool (k : ℕ) :=
    fun x => ⟨⟨(f x.1).length, x.2⟩, ⟨f x.1, rfl⟩⟩
  have hΦ : Function.Injective Φ := by
    intro a b hab
    -- Reading off the underlying list recovers the codeword, so f a = f b.
    have hfab : f a.1 = f b.1 := congrArg (fun s => (s.2).toList) hab
    exact Subtype.ext (hf hfab)
  calc Fintype.card {x : α // (f x).length < L}
      ≤ Fintype.card (Σ k : Fin L, List.Vector Bool (k : ℕ)) :=
        Fintype.card_le_of_injective Φ hΦ
    _ = ∑ k : Fin L, 2 ^ (k : ℕ) := by
        simp [Fintype.card_sigma, card_vector, Fintype.card_bool]
    _ = ∑ k ∈ Finset.range L, 2 ^ k := Fin.sum_univ_eq_sum_range (fun m => 2 ^ m) L
    _ = 2 ^ L - 1 := sum_two_pow_range L

/-- Strict form: fewer than `2^L` messages can be compressed below `L` bits. -/
theorem compressible_count_lt {α : Type*} [Fintype α]
    {f : α → List Bool} (hf : IsLossless f) (L : ℕ) :
    Fintype.card {x : α // (f x).length < L} < 2 ^ L := by
  have h := compressible_count_le hf L
  have hpos : 0 < 2 ^ L := pow_pos (by norm_num) L
  omega

/-- **No lossless code compresses everything.**  If there are at least `2^L`
messages, then some message must be assigned a codeword of length at least `L`.
Equivalently, the worst-case codeword length of any lossless binary code on `N`
messages is at least `log₂ N`. -/
theorem exists_long_codeword {α : Type*} [Fintype α]
    {f : α → List Bool} (hf : IsLossless f) {L : ℕ}
    (h : 2 ^ L ≤ Fintype.card α) :
    ∃ x, L ≤ (f x).length := by
  by_contra hc
  push_neg at hc
  -- Every message is compressible, so the subtype is all of `α`.
  have hcard : Fintype.card {x : α // (f x).length < L} = Fintype.card α :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv hc)
  have hlt := compressible_count_lt hf L
  omega

/-- The counting bound restated for the explicit `Finset` of messages whose
codeword is shorter than `L` bits. -/
theorem compressible_filter_card_le {α : Type*} [Fintype α] [DecidableEq α]
    {f : α → List Bool} (hf : IsLossless f) (L : ℕ) :
    (Finset.univ.filter (fun x => (f x).length < L)).card ≤ 2 ^ L - 1 := by
  have h := compressible_count_le hf L
  rwa [Fintype.card_subtype] at h

end InformationTheory.UniversalSourceCoding
