# Uniform interval-defect exclusion

[UNIFORM.md](UNIFORM.md) is the final theorem: the interval circulant defect
cannot arise from a q-regular loopless C4-free graph on q² vertices for any
binary q>=4. The proof uses cyclotomic integers modulo two and rational
spectral trace. It does not cover arbitrary defects or solve Erdős85.

Squad review1540 independently accepted the uniform proof and regression
checker. Review1539 accepted the earlier exact norm certificates at q16/64.
The companion [squareclass note](../l6-circulant-squareclass/NOTE.md), reviewed
in1537, proves a separate necessary condition for connected circulant defects.

`NOTE.md` is the finite/conditional predecessor, preserved with its reviewed
bytes. Its formerly missing uniform nonsquareness input is supplied by
`UNIFORM.md`. Likewise, the companion squareclass note's interval family
passes only its two named screens; it is excluded by this uniform theorem.

Run `python3 check_mod2.py` for the finite regression checks of the uniform
argument. Run `python3 check.py` for the independent exact modular-resultant
certificates at q16/64. Both require only Python; the latter additionally
requires SymPy. They write their corresponding verification JSON beside the
script. The manifests preserve hashes of the reviewed proof/checker/result
files. No Lean formalization is included.
