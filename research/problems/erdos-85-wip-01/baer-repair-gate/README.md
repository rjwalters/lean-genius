# Odd-degree design and repair restrictions

[ODD_DDG_GATE.md](ODD_DDG_GATE.md) proves that no simple odd-regular graph
of degree at least3 admits equal groups with zero common neighbors within
a group and one common neighbor across groups. Equivalently, its graph of
zero-common-neighbor pairs cannot be a disjoint union of cliques. This is
a uniform prose theorem, independently accepted in squad review1547.

[GRAM_GATE.md](GRAM_GATE.md), accepted in review1545, is a special case:
no loopless repair can preserve the square of the Baer-deletion matrix
with its exterior absolute loops restored. Its direct quotient proof is
preserved separately. It is subsumed by the broader theorem and should
not be counted as a second independent obstruction.

[NOTE.md](NOTE.md), accepted in review1543, proves a different restriction:
a repair retaining a perfect matching of the deficient absolute vertices
requires quadratically many old-edge deletions. It permits changes to the
Gram matrix. Neither result excludes arbitrary larger repairs or proves
Erdős85.

`check.py` verifies the deterministic q25 seed and matching-deletion bound.
`gram_check.py` verifies the restored-loop matrix and quotient, invoking
the seed checker first. Both use only Python's standard library and write
their verification JSON files alongside the scripts. The manifest records
the reviewed proof/checker/result bytes. No Lean theorem is included.
