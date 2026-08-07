# PySAT seqcounter emission spec (for byte-exact Lean clause-list matching)

Source: pysat @ github.com/pysathq/pysat, `cardenc/seqcounter.hh`
(`seqcounter_encode_atmostN`) and `cardenc/card.hh` (`_encode_atmost`,
`_encode_atleast`, equals = atleast then atmost). PySAT's implementation is
**Knuth's irredundant variant** of the sequential counter (per the in-source
comment "as suggested by Alex Healy"), NOT the original Sinz CP'05 layout.

## equals(lits, k) emission order

1. **ATLEAST block first**: `_encode_atleast(lits, k)` is implemented by
   negating every literal in place and calling atmost with bound `n − k`:
   `atmostN([-l for l in lits], n − k)`.
2. **ATMOST block second**: `atmostN(lits, k)`.

Special cases short-circuit before the general encoder:
- atmost with `rhs ≥ n`: emit nothing;
- atmost with `rhs = n−1`: single clause `(¬l₁ ∨ … ∨ ¬lₙ)` (common_encode_atmostNm1);
- atmost with `rhs = 0`: unit clauses `(¬lᵢ)` each;
- atleast with `rhs ≤ 0`: nothing; `rhs = 1`: single clause `(l₁ ∨ … ∨ lₙ)`;
  `rhs = n`: unit clauses `(lᵢ)` each.

## atmostN(vars, t) general case (t = tval, n = |vars|), 0-indexed

Aux variables `s(k, j)` for `k ∈ [0, t−1]`, `j ∈ [0, n−t−1]`, allocated by
`mk_yvar` **memoized on first use** in the exact loop order below (so the
DIMACS numbering is the first-use order, continuing from the current top):

```
for j in 0 .. n−t−1:
    # eq 19, k = 0:
    emit ( −vars[j] ∨ s(0,j) )                       # s(0,j) allocated here on first use
    for k in 0 .. t−2:
        # eq 18:
        if j < n−t−1:
            emit ( −s(k,j) ∨ s(k,j+1) )              # allocates s(k,j+1) if new
        # eq 19:
        emit ( −vars[j+k+1] ∨ −s(k,j) ∨ s(k+1,j) )   # allocates s(k+1,j) if new
    # k = t−1, eq 18:
    if j < n−t−1:
        emit ( −s(t−1,j) ∨ s(t−1,j+1) )
    # k = t−1, eq 19 (final):
    emit ( −vars[j+t] ∨ −s(t−1,j) )
```

Aux count per block: exactly `t · (n − t)` variables.

## Concrete check (equals([1..5], 2), aux starting at 6)

Atleast block = atmostN([−1..−5], 3): aux 6..11; clauses
`[1,6],[-6,7],[2,-6,8],[-8,9],[3,-8,10],[-10,11],[4,-10],[2,7],[3,-7,9],
[4,-9,11],[5,-11]`.
Atmost block = atmostN([1..5], 2): aux 12..17; clauses
`[-1,12],[-12,13],[-2,-12,14],[-14,15],[-3,-14],[-2,13],[-13,16],
[-3,-13,15],[-15,17],[-4,-15],[-3,16],[-4,-16,17],[-5,-17]`.

## Verified allocation order at n = 48 (the lab's per-vertex size)

Replicating the loop above reproduces pysat's allocation exactly. First-use
order interleaves columns j and j+1 (eq 18 touches s(k,j+1) before eq 19
allocates s(k+1,j)): for the first column the order is
(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),… Verified counts:
- equals(48, 7): atleast block = atmostN(¬lits, 41) → 41·7 = 287 aux;
  atmost block = atmostN(lits, 7) → 7·41 = 287 aux; total 574 aux, 1148 clauses.
- equals(48, 8): 40·8 + 8·40 = 640 aux, 1280 clauses.

## Usage in the 49-lab instances

Each vertex x gets `CardEnc.equals(lits = edge vars of x in lex order of the
other endpoint, bound = 8 (high) or 7 (low))`, emitted in vertex order
x = 0..48, after the 1176 lex-pre-allocated edge variables and any unit-fixed
clauses. Partition-law clauses follow the cardinality blocks.
