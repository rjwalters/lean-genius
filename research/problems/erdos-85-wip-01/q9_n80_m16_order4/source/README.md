# Coupled order-four character filter for N80/m16

codex-sol-2, 2026-09-11. Necessary character-matrix computation, not a graph/CNF/SAT search. Acceptance depends on the separately frozen quotient2152, mixed-triangle2154 and parity2155 stages.

The input consists of the180 parity matrices H for quotient types0,1,3,4 retained after the triangle exclusions. For each, let C be the Hermitian adjacency Fourier matrix at z=i. A cross block of degree q contributes a sum of q fourth roots whose parity sum equals the corresponding H entry. This gives its finite Gaussian-integer domain.

An internal degree0 gives Cii=0. Degree1 is the antipodal shift8 and gives Cii=1. For degree2, an odd internal shift gives Hii=-2 and Cii=0. An even shift must be2 or6 up to sign: shift4 makes an internal C4, while shift8 would have degree1. Thus Hii=2 forces Cii=-2, never+2. This last restriction is specific to order16.

For i!=j, the adjacency-square block has0/1 coefficients on16 offsets. Write their counts in the four residue classes modulo4 as n0,n1,n2,n3, each between0 and4. They satisfy

`n0+n1+n2+n3=(Q²)ij`,

`n0+n2-n1-n3=(H²)ij`,

and consequently `(C²)ij=(n0-n2)+i(n1-n3)`.

Within an orbit, the square has diagonal9 and a set of opposite offset pairs selected from representatives1,...,7. Offset8 is absent: common neighbours of antipodal vertices would come in free-involution pairs, violating codegree at most1. For a selected set S, require

`9+2|S|=(Q²)ii` and `9+2 sum((-1)^s:s in S)=(H²)ii`;

then `(C²)ii=9+2 sum(Re(i^s):s in S)`.

The producer constructs complete row domains satisfying these norms and joins rows by Hermitian symmetry and the cross-square constraints. Original limits were100000 operations per parity-input case and60seconds aggregate. All180 cases completed in1.466seconds, maximum2529 operations per case, with0UNKNOWN and0unvisited. Types0,3,4 retain no C matrix. Type1 retains1024 C matrices across16 of its48 parity inputs. Full ordered case receipts and survivors are saved.

The independent verifier enumerates all65536 actual subsets of the16 offsets to derive cross-square possibilities, and all128 subsets of the seven opposite pairs for diagonal possibilities. It derives edge domains from actual distinct offset subsets, represents Gaussian integers as integer pairs, and joins rows in smallest-domain order rather than natural order. It reconstructs the exact1024 survivors and all180 endpoint counts in1.223seconds, maximum2913 operations per case. No producer functions are imported.

Subject to independent review of this stage and its premises, types0,3,4 cannot lift to graphs. Together with the triangle exclusions, only quotient type1 remains (60 labelled degree matrices), with1024 necessary order-four character matrices. These matrices are not graph witnesses, and their nonempty list does not prove existence. There is no full N80/m16 or global Erdős85 conclusion and no Lean theorem. Original capped domains were not retried or enlarged.
