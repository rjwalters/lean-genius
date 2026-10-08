#!/usr/bin/env python3
"""Generate the native_decide part modules and the cell module for one H5 cell.

usage: gen_parts.py CELL K M   (run from the repository root)

CELL in 0,1,2; K = number of core vertices in the phase-1 prefix; M = parts.
Writes proofs/Proofs/Erdos85H5T{CELL}PartNN.lean and Erdos85H5T{CELL}.lean.
"""
import sys, pathlib
c, k, m = map(int, sys.argv[1:4])
d = pathlib.Path('proofs/Proofs')
w = max(2, len(str(m - 1)))
names = []
for r in range(m):
    nn = str(r).zfill(w)
    mod = f'Erdos85H5T{c}Part{nn}'
    thm = f'cellPart_{c}_{k}_{m}_{nn}'
    names.append((mod, thm))
    (d / f'{mod}.lean').write_text(f'''import Proofs.Erdos85H5Bridge

/-! Part {r} of the {m}-way split five-high search, cell `t = {c}` (`native_decide`). -/

namespace Erdos85
namespace H5

theorem {thm} : cellPart {c} {k} {m} {r} = true := by
  native_decide

end H5
end Erdos85
''')
imports = '\n'.join(f'import Proofs.{mod}' for mod, _ in names)
cases = '\n'.join(f'  | {r}, _ => {thm}' for r, (_, thm) in enumerate(names))
(d / f'Erdos85H5T{c}.lean').write_text(f'''{imports}

/-!
# Exclusion of the canonical five-high representative `t = {c}`

Composition of the {m} `native_decide` parts of the split search with the
kernel-checked engine soundness and bridge.  Besides the three standard
axioms, the conclusion depends on exactly the {m} axioms that
`native_decide` emits for the part theorems `cellPart_{c}_{k}_{m}_NN` (trust
in compiled evaluation of `cellPart {c} {k} {m} NN`).
-/

namespace Erdos85
namespace H5

theorem cellPart_{c}_{k}_{m}_all : ∀ r, r < {m} → cellPart {c} {k} {m} r = true
{cases}
  | n + {m}, h => absurd h (by omega)

/-- The canonical five-high representative with `{c}` triple supports is
excluded. -/
theorem fiveHighCanonicalRepresentativeExcluded_{c} :
    FiveHighCanonicalRepresentativeExcluded {c} :=
  fiveHighCanonicalRepresentativeExcluded_of_parts {c} {k} {m} (by norm_num)
    cellPart_{c}_{k}_{m}_all

end H5
end Erdos85

#print axioms Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_{c}
''')
print(f'wrote {m} parts and Erdos85H5T{c}.lean')
