#!/usr/bin/env python3
"""
L6-representability probe for the Erdos-85 campaign (q = 16 circulant defect D16).

M = 15 I + J - D16  (n = 256).  Question: is M Z_2-represented by I_256, i.e. is there a
2-adic integer matrix X with X^T X = M?   Equivalently: does the lattice L_M = (Z_2^256, M)
have a unimodular overlattice U (index 2^m) that is ODD and has the Conway-Sloane 2-adic
symbol of I_256, namely  1^{+256}_0  (rank 256, det in (Z_2^x)^2, oddity 0 mod 8)?

Also: rational Hasse-Minkowski comparison of M with I_256 at every place.

Everything is exact (Python big ints, arithmetic mod 2^prec with explicit precision
bookkeeping for the 2-adic part, and exact integer leading principal minors for the
rational part).  Only the standard library is required.
"""
import json, hashlib, random, sys, time
from math import gcd

random.seed(20260908)
N_VERT = 256
Q = 16

# --------------------------------------------------------------------------------------
# 1.  The matrix
# --------------------------------------------------------------------------------------
def circulant_defect_S(q):
    order = q * q
    positive_pairs = [1, *range(2, q - 2, 2)]
    gens = {order // 2}
    for s in positive_pairs:
        gens.update((s, order - s))
    assert len(gens) == q - 1
    return sorted(gens)

def build_M(q):
    n = q * q
    S = circulant_defect_S(q)
    M = [[1] * n for _ in range(n)]          # J
    for i in range(n):
        M[i][i] += q - 1                     # (q-1) I
        for s in S:
            M[i][(i + s) % n] -= 1           # - D
    return M, S

# --------------------------------------------------------------------------------------
# Bareiss: exact determinant and all leading principal minors
# --------------------------------------------------------------------------------------
def bareiss_minors(A):
    """Return list of leading principal minors Delta_1..Delta_n (exact ints) of a square
    integer matrix, assuming no zero pivot occurs (raise otherwise)."""
    n = len(A)
    a = [row[:] for row in A]
    minors = []
    prev = 1
    for k in range(n):
        p = a[k][k]
        if p == 0:
            raise ZeroDivisionError(f"zero pivot at {k}")
        for i in range(k + 1, n):
            aik = a[i][k]
            rowi = a[i]
            rowk = a[k]
            for j in range(k + 1, n):
                rowi[j] = (rowi[j] * p - aik * rowk[j]) // prev
        minors.append(p)
        prev = p
    return minors

def v2(x):
    if x == 0:
        return None
    return (x & -x).bit_length() - 1

def isqrt_exact(x):
    from math import isqrt
    r = isqrt(x)
    return r if r * r == x else None

# --------------------------------------------------------------------------------------
# 2.  2-adic Jordan decomposition (mod 2^prec with precision bookkeeping)
# --------------------------------------------------------------------------------------
def val2_mod(x, prec):
    """2-adic valuation of a residue mod 2^prec (None if 0 mod 2^prec)."""
    x %= (1 << prec)
    if x == 0:
        return None
    return (x & -x).bit_length() - 1

def inv_odd(u, prec):
    return pow(u, -1, 1 << prec)

def jordan_2adic(G, prec, track_P=True):
    """Symmetric congruence reduction of symmetric G (entries mod 2^prec) over Z_2.
    Returns (J, P, blocks, precP) with J = P^T G P mod 2^{prec} block diagonal,
    blocks = list of (scale v, [indices]) with len 1 (1x1: 2^v * unit) or 2 (2x2 even
    block 2^v [[2a,b],[b,2c]], b unit).  P is Z_2-unimodular, known mod 2^precP."""
    n = len(G)
    mod = 1 << prec
    A = [[x % mod for x in row] for row in G]
    P = [[int(i == j) for j in range(n)] for i in range(n)] if track_P else None
    precP = prec
    remaining = list(range(n))
    blocks = []
    order = []          # final index order
    while remaining:
        # minimal valuation among remaining submatrix
        best_v = None; best = None; diag = False
        for i in remaining:
            vi = val2_mod(A[i][i], prec)
            if vi is not None and (best_v is None or vi < best_v):
                best_v, best, diag = vi, (i, i), True
        for idx_i, i in enumerate(remaining):
            Ai = A[i]
            for j in remaining[idx_i + 1:]:
                vij = val2_mod(Ai[j], prec)
                if vij is not None and (best_v is None or vij < best_v):
                    best_v, best, diag = vij, (i, j), False
        if best_v is None:
            raise RuntimeError("submatrix is 0 mod 2^prec: precision exhausted")
        v = best_v
        if diag:
            i = best[0]
            piv = A[i][i]
            u = piv >> v
            uinv = inv_odd(u, prec)
            remaining.remove(i)
            # eliminate: for j in remaining: row_j -= (A[j][i]/piv) row_i, col likewise
            for j in remaining:
                aji = A[j][i]
                if aji % mod == 0:
                    continue
                # coefficient c = aji / piv = (aji >> v) * uinv  (known mod 2^{prec-v})
                c_num = aji  # keep 2^v inside for the Gram update
                Aj = A[j]; Ai = A[i]
                for k in remaining:
                    # correction = aji * A[i][k] / piv = (aji * (A[i][k] >> v)) * uinv   (no precision loss)
                    Aj[k] = (Aj[k] - ((c_num * (Ai[k] >> v)) % mod) * uinv) % mod
                if track_P:
                    c = ((aji >> v) * uinv) % mod
                    Pi_col = [P[r][i] for r in range(n)]
                    for r in range(n):
                        P[r][j] = (P[r][j] - c * Pi_col[r]) % mod
            for j in remaining:
                A[j][i] = 0; A[i][j] = 0
            if track_P:
                precP = min(precP, prec - v)
            blocks.append((v, [i]))
            order.append(i)
        else:
            i, k = best
            a, b, c = A[i][i], A[i][k], A[k][k]
            # det of the block = ac - b^2 = 2^{2v} * w, w unit (a, c divisible by 2^{v+1})
            det_blk = (a * c - b * b)
            w = (det_blk >> (2 * v)) % mod
            assert w % 2 == 1, "2x2 pivot block not of expected shape"
            winv = inv_odd(w, prec)
            remaining.remove(i); remaining.remove(k)
            # adj(B) = [[c, -b], [-b, a]]
            for j in remaining:
                aji, ajk = A[j][i], A[j][k]
                if aji % mod == 0 and ajk % mod == 0:
                    continue
                # coefficients of row_j in terms of rows i,k:  [aji ajk] adj(B) / (2^{2v} w)
                ci_num = (aji * c - ajk * b)          # divisible by 2^{2v}
                ck_num = (-aji * b + ajk * a)
                Aj = A[j]; Ai = A[i]; Ak = A[k]
                for l in remaining:
                    corr = (ci_num * Ai[l] + ck_num * Ak[l])   # divisible by 2^{3v}
                    corr = (corr >> (2 * v)) * winv
                    Aj[l] = (Aj[l] - corr) % mod
                if track_P:
                    ci = ((ci_num >> (2 * v)) * winv) % mod
                    ck = ((ck_num >> (2 * v)) * winv) % mod
                    for r in range(n):
                        P[r][j] = (P[r][j] - ci * P[r][i] - ck * P[r][k]) % mod
            for j in remaining:
                A[j][i] = A[j][k] = 0
                A[i][j] = A[k][j] = 0
            if track_P:
                precP = min(precP, prec - 2 * v)
            blocks.append((v, [i, k]))
            order.extend([i, k])
    return A, P, blocks, precP

def matmul_mod(X, Y, mod):
    n = len(X); m = len(Y[0]); k = len(Y)
    Yt = [[Y[r][c] for r in range(k)] for c in range(m)]
    out = []
    for i in range(n):
        Xi = X[i]
        out.append([sum(Xi[r] * Ytc[r] for r in range(k)) % mod for Ytc in Yt])
    return out

def transpose(X):
    return [list(r) for r in zip(*X)]

# --------------------------------------------------------------------------------------
# Conway-Sloane 2-adic symbol of a Jordan decomposition
# --------------------------------------------------------------------------------------
def diagonalise_odd_unimodular(U, prec, tries=200):
    """U: symmetric unimodular over Z_2 (mod 2^prec), ODD type. Return list of diagonal
    units (mod 8 suffices but we keep mod 2^prec) of a diagonalisation, found by random
    unimodular basis changes + greedy odd-diagonal pivoting."""
    n = len(U)
    mod = 1 << prec
    for t in range(tries):
        # random Z_2-unimodular change of basis (unit lower triangular * permutation-ish)
        R = [[int(i == j) for j in range(n)] for i in range(n)]
        if t > 0:
            for i in range(n):
                for j in range(n):
                    if i != j and random.random() < 0.5:
                        R[i][j] = random.randrange(0, 4)
            # make sure R is invertible mod 2: use unit upper triangular + unit lower triangular product
            L = [[int(i == j) if i <= j else random.randrange(0, 4) for j in range(n)] for i in range(n)]
            Up = [[int(i == j) if i >= j else random.randrange(0, 4) for j in range(n)] for i in range(n)]
            R = matmul_mod(L, Up, mod)
        G = matmul_mod(matmul_mod(transpose(R), U, mod), R, mod)
        # greedy odd diagonal pivots
        A = [row[:] for row in G]
        remaining = list(range(n))
        diag = []
        ok = True
        while remaining:
            piv = None
            for i in remaining:
                if A[i][i] % 2 == 1:
                    piv = i; break
            if piv is None:
                ok = False; break
            i = piv
            u = A[i][i]; uinv = inv_odd(u, prec)
            remaining.remove(i)
            for j in remaining:
                aji = A[j][i]
                if aji % mod == 0: continue
                c = (aji * uinv) % mod
                Aj = A[j]; Ai = A[i]
                for k in remaining:
                    Aj[k] = (Aj[k] - c * Ai[k]) % mod
                for r in range(n):
                    R[r][j] = (R[r][j] - c * R[r][i]) % mod
            for j in remaining:
                A[j][i] = 0; A[i][j] = 0
            diag.append(u)
        if ok:
            # verify: R^T U R is diagonal with the recorded diagonal
            chk = matmul_mod(matmul_mod(transpose(R), U, mod), R, mod)
            perm = [i for i in range(n)]
            # diag was appended in pivot order; check off-diagonals vanish and diagonal set matches
            assert all(chk[i][j] == 0 for i in range(n) for j in range(n) if i != j), "diagonalisation check failed"
            assert sorted(chk[i][i] % 8 for i in range(n)) == sorted(d % 8 for d in diag)
            return diag
    raise RuntimeError("could not diagonalise odd unimodular lattice")

def cs_symbol(J, blocks, prec):
    """Compute the Conway-Sloane 2-adic symbol from the block-diagonal Jordan form J.
    Returns list of dicts per scale: {scale, rank, type, det_mod8, sign, oddity} plus the
    per-scale unimodular Gram used."""
    mod = 1 << prec
    by_scale = {}
    for v, idx in blocks:
        by_scale.setdefault(v, []).extend(idx)
    out = []
    for v in sorted(by_scale):
        idx = by_scale[v]
        r = len(idx)
        # unimodular Gram of the constituent: J[idx,idx] / 2^v  (known mod 2^{prec-v})
        p2 = prec - v
        U = [[(J[i][j] >> v) % (1 << p2) for j in idx] for i in idx]
        odd = any(U[i][i] % 2 == 1 for i in range(r))
        # determinant of U mod 8 via exact integer determinant of small-ish matrix? use Bareiss over Z on residues mod 2^p2 then reduce mod 8 -- fine if r moderate; else use block structure
        # blocks are 1x1 or 2x2 so det is a product:
        det = 1
        for vv, bi in blocks:
            if vv != v: continue
            if len(bi) == 1:
                det = (det * ((J[bi[0]][bi[0]] >> v) % 8)) % 8
            else:
                i, k = bi
                a, b, c = (J[i][i] >> v), (J[i][k] >> v), (J[k][k] >> v)
                d = (a * c - b * b) % 8
                assert d in (3, 7), f"even 2x2 block det {d} mod 8 unexpected"
                det = (det * d) % 8
        sign = '+' if det in (1, 7) else '-'
        entry = {"scale": v, "rank": r, "type": "I" if odd else "II", "det_mod8": det, "sign": sign}
        if odd:
            diag = diagonalise_odd_unimodular(U, p2)
            t = sum(d % 8 for d in diag) % 8
            entry["oddity"] = t   # trace of an explicit (verified) diagonalisation mod 8 -- authoritative
            entry["diag_mod8_multiset"] = {str(k): sum(1 for d in diag if d % 8 == k) for k in (1, 3, 5, 7)}
            dm = 1
            for d in diag: dm = (dm * (d % 8)) % 8
            entry["det_from_diagonalisation_mod8"] = dm
            assert dm == det, ("det mismatch", dm, det)
            entry["symbol"] = f"{2**v}^{sign}{r}_{t}"
        else:
            entry["symbol"] = f"{2**v}^{sign}{r}_II"
        out.append(entry)
    return out

# --------------------------------------------------------------------------------------
# 3.  Overlattice construction (greedy) in Jordan coordinates
# --------------------------------------------------------------------------------------
def overlattice_greedy(M, prec, prefer_odd=True, verbose=True):
    """Start from Gram M (mod 2^prec).  Repeat: Jordan-reduce, adjoin an isotropic dual
    vector, until unimodular or stuck.  Returns dict with chain log, final Gram, index,
    unimodular?, odd?, and (if unimodular odd) diagonal units multiset."""
    n = len(M)
    G = [row[:] for row in M]
    steps = 0
    log = []
    m_index = 0
    while True:
        J, P, blocks, precP = jordan_2adic(G, prec, track_P=False)
        scales = {}
        for v, idx in blocks:
            scales.setdefault(v, []).append(idx)
        maxv = max(scales)
        if maxv == 0:
            G = J
            break
        # choose move
        move = None
        # (a) 1x1 block of scale >= 2 : adjoin e/2
        for v in sorted(scales, reverse=True):
            if v >= 2:
                for idx in scales[v]:
                    if len(idx) == 1:
                        move = ('half', idx[0], v); break
                    else:
                        move = ('half', idx[0], v); break   # (c) even block scale >= 2: adjoin e1/2
                if move: break
        if move is None:
            # scale 1 only: pair two 1x1 blocks (b), else even block (c)
            ones = [idx[0] for idx in scales[1] if len(idx) == 1]
            twos = [idx for idx in scales[1] if len(idx) == 2]
            if prefer_odd and len(ones) >= 2:
                move = ('pairhalf', ones[0], ones[1], 1)
            elif twos:
                move = ('half', twos[0][0], 1)
            elif len(ones) >= 2:
                move = ('pairhalf', ones[0], ones[1], 1)
            else:
                # stuck: residual is a single <2u> at scale 1 (anisotropic)
                log.append({"step": steps, "stuck_residual": [(v, idx) for v, idx in blocks if v > 0]})
                G = J
                return {"steps": steps, "index_log2": m_index, "unimodular": False, "log": log,
                        "final_blocks": [(v, len(idx)) for v, idx in blocks if v > 0], "G": G, "prec": prec}
        # apply the move to J (block diagonal), i.e. rescale rows/cols
        if move[0] == 'half':
            i = move[1]
            # new basis: e_i / 2 ; Gram: row/col i divided by 2, (i,i) by 4.  (off-diagonal in row i
            # is zero except inside the 2x2 block)
            Jn = J
            for k in range(n):
                if k != i:
                    assert Jn[i][k] % 2 == 0 and Jn[k][i] % 2 == 0
                    Jn[i][k] = Jn[i][k] >> 1
                    Jn[k][i] = Jn[k][i] >> 1
            assert Jn[i][i] % 4 == 0
            Jn[i][i] >>= 2
            prec -= 2
            mod = 1 << prec
            G = [[x % mod for x in row] for row in Jn]
            log.append({"step": steps, "move": f"adjoin e/2 at scale {move[2]}", "prec": prec})
        else:
            i, k = move[1], move[2]
            # new basis: x = (e_i + e_k)/2, e_k ; Gram: [[ (Jii + Jkk)/4, Jkk/2 ], [Jkk/2, Jkk]],
            # and b(x, e_l) = (J_il + J_kl)/2 = 0 for other l (block diagonal)
            Jn = J
            Jii, Jkk, Jik = Jn[i][i], Jn[k][k], Jn[i][k]
            assert Jik % (1 << prec) == 0
            assert (Jii + Jkk) % 4 == 0 and Jkk % 2 == 0
            for l in range(n):
                if l not in (i, k):
                    assert Jn[i][l] % 2 == 0 and Jn[k][l] % 2 == 0
                    Jn[i][l] = (Jn[i][l] + Jn[k][l]) >> 1
                    Jn[l][i] = Jn[i][l]
            Jn[i][i] = (Jii + Jkk) >> 2
            Jn[i][k] = Jn[k][i] = Jkk >> 1
            prec -= 2
            mod = 1 << prec
            G = [[x % mod for x in row] for row in Jn]
            log.append({"step": steps, "move": "adjoin (e+e')/2 (two scale-1 rank-1 blocks)", "prec": prec})
        steps += 1
        m_index += 1
        if verbose and steps % 10 == 0:
            print(f"  overlattice step {steps}, index 2^{m_index}, prec {prec}", flush=True)
    odd = any(G[i][i] % 2 == 1 for i in range(n))
    return {"steps": steps, "index_log2": m_index, "unimodular": True, "odd": odd, "log": log, "G": G, "prec": prec}

# --------------------------------------------------------------------------------------
# 5.  Rational Hasse invariants
# --------------------------------------------------------------------------------------
def vp_unit(x, p):
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v, x

def hilbert_odd(a_v, a_u, b_v, b_u, p):
    """(a,b)_p for odd p with a = p^a_v a_u, b = p^b_v b_u (a_u,b_u units): returns +-1."""
    eps = ((p - 1) // 2) % 2
    s = 1
    if (a_v * b_v * eps) % 2 == 1:
        s = -s
    if b_v % 2 == 1 and pow(a_u % p, (p - 1) // 2, p) == p - 1:
        s = -s
    if a_v % 2 == 1 and pow(b_u % p, (p - 1) // 2, p) == p - 1:
        s = -s
    return s

def hilbert_2(a_v, a_u, b_v, b_u):
    eps = lambda u: ((u - 1) // 2) % 2
    om = lambda u: ((u * u - 1) // 8) % 2
    e = (eps(a_u) * eps(b_u) + a_v * om(b_u) + b_v * om(a_u)) % 2
    return -1 if e else 1

def hasse_invariant(diag_square_classes, p):
    """diag entries d_i (ints, nonzero); Hasse invariant c_p = prod_{i<j} (d_i,d_j)_p."""
    data = []
    for d in diag_square_classes:
        sgn = 1 if d > 0 else -1
        v, u = vp_unit(abs(d), p)
        data.append((v, u * sgn))
    c = 1
    n = len(data)
    if p == 2:
        # reduce units mod 8 for speed
        data = [(v % 2, ((u % 8) if u % 8 else 0)) for v, u in data]
        for i in range(n):
            for j in range(i + 1, n):
                c *= hilbert_2(data[i][0], data[i][1], data[j][0], data[j][1])
    else:
        # precompute Legendre symbols
        leg = [pow(u % p, (p - 1) // 2, p) == p - 1 for v, u in data]
        eps = ((p - 1) // 2) % 2
        for i in range(n):
            vi, li = data[i][0] % 2, leg[i]
            for j in range(i + 1, n):
                vj, lj = data[j][0] % 2, leg[j]
                s = 1
                if vi and vj and eps: s = -s
                if vj and li: s = -s
                if vi and lj: s = -s
                c *= s
    return c

def hasse_real(diag):
    neg = sum(1 for d in diag if d < 0)
    return -1 if (neg * (neg - 1) // 2) % 2 else 1

# --------------------------------------------------------------------------------------
def main():
    t0 = time.time()
    M, S = build_M(Q)
    n = len(M)
    print("connection set S =", S)
    for i in range(n):
        assert M[i][i] == Q and all(M[i][(i + s_) % n] == 0 for s_ in S)
        assert sum(1 for j in range(n) if M[i][j] == 0) == Q - 1 and sum(M[i]) == n
    print("M checked: diag 16, zero exactly on the 15 D-edges, row sum 256", flush=True)
    results = {"q": Q, "n": n, "S": S, "M_definition": "M = (q-1)I + J - D16 = 15I + J - D16"}

    # ---- Step 1: determinant
    print("Bareiss ...", flush=True)
    minors = bareiss_minors(M)
    detM = minors[-1]
    print(f"det M has {len(str(detM))} digits; v2 = {v2(detM)}; time {time.time()-t0:.1f}s", flush=True)
    assert all(d > 0 for d in minors), "M not positive definite?!"
    results["positive_definite_via_minors"] = True
    results["detM"] = str(detM)
    results["v2_detM"] = v2(detM)
    q_ = detM // 1024
    assert detM % 1024 == 0
    s = isqrt_exact(q_)
    results["detM_over_1024_is_square"] = s is not None
    results["sqrt_detM_over_1024"] = str(s) if s is not None else None
    odd_part = detM >> v2(detM)
    results["detM_odd_part"] = str(odd_part)
    results["detM_odd_part_mod8"] = odd_part % 8
    # factor odd part with capped effort
    try:
        import sympy
        f = sympy.factorint(odd_part, limit=10**6)
        results["detM_odd_part_factorint_limit1e6"] = {str(k): v for k, v in f.items()}
        results["detM_odd_part_factorint_note"] = "sympy.factorint(limit=1e6); large cofactors may be composite"
    except Exception as e:
        results["detM_odd_part_factorint_note"] = f"factorint failed: {e}"

    # cross-check det via circulant eigenvalues (cyclotomic norms) with sympy resultants
    try:
        import sympy
        x = sympy.Symbol('x')
        f = 15 + sum(x**j for j in range(n)) - sum(x**s_ for s_ in S)
        fpoly = sympy.Poly(f, x)
        detcheck = 1
        for d in sympy.divisors(n):
            Phi = sympy.Poly(sympy.cyclotomic_poly(d, x), x)
            detcheck *= int(sympy.resultant(Phi, fpoly % Phi if Phi.degree() > 0 else fpoly, x))
        results["det_circulant_cyclotomic_crosscheck"] = (abs(detcheck) == abs(detM))
        print("cyclotomic cross-check:", abs(detcheck) == abs(detM), flush=True)
    except Exception as e:
        results["det_circulant_cyclotomic_crosscheck"] = f"skipped: {e}"

    # ---- Step 2: 2-adic Jordan decomposition of M
    v2d = v2(detM)
    prec0 = 2 * v2d + 64
    print(f"Jordan decomposition mod 2^{prec0} ...", flush=True)
    J, P, blocks, precP = jordan_2adic(M, prec0, track_P=True)
    # sanity: P^T M P == J mod 2^precP
    mod = 1 << precP
    PtMP = matmul_mod(matmul_mod(transpose(P), M, mod), P, mod)
    assert all(PtMP[i][j] % mod == J[i][j] % mod for i in range(n) for j in range(n)), "P^T M P != J"
    sym = cs_symbol(J, blocks, prec0)
    results["jordan_M"] = sym
    results["jordan_M_symbol"] = " ".join(e["symbol"] for e in sym)
    tot = sum(e["scale"] * e["rank"] for e in sym)
    assert tot == v2d, (tot, v2d)
    print("2-adic symbol of M:", results["jordan_M_symbol"], flush=True)
    print(f"  time {time.time()-t0:.1f}s", flush=True)

    # ---- Step 3/4: overlattice
    print("Overlattice construction ...", flush=True)
    ov = overlattice_greedy(M, prec0)
    res_ov = {k: v for k, v in ov.items() if k != "G"}
    results["overlattice"] = res_ov
    print(f"  steps {ov['steps']}, index 2^{ov['index_log2']}, unimodular {ov['unimodular']}", flush=True)
    if ov["unimodular"]:
        assert ov["index_log2"] * 2 == v2d
        G = ov["G"]; pr = ov["prec"]
        Ju, _, bl, _ = jordan_2adic(G, pr, track_P=False)
        symU = cs_symbol(Ju, bl, pr)
        results["overlattice"]["symbol"] = " ".join(e["symbol"] for e in symU)
        results["overlattice"]["jordan"] = symU
        print("  overlattice symbol:", results["overlattice"]["symbol"], flush=True)
        if not ov["odd"]:
            # try to obtain an odd one: adjoin nothing -- instead retry with prefer_odd variations
            print("  even overlattice found; searching for an odd one via different Lagrangian choice", flush=True)
            ov2 = overlattice_greedy(M, prec0, prefer_odd=False)
            results["overlattice_alt"] = {k: v for k, v in ov2.items() if k != "G"}
    else:
        print("  STUCK; residual blocks:", ov["final_blocks"], flush=True)

    # ---- Step 5: rational Hasse invariants.  diag of Q-diagonalisation: d_k = Delta_k / Delta_{k-1}
    # square class of d_k = Delta_k * Delta_{k-1}.
    diag_sq = [minors[0]] + [minors[k] * minors[k - 1] for k in range(1, n)]
    primes = set([2])
    fdict = results.get("detM_odd_part_factorint_limit1e6", {})
    for k in fdict:
        primes.add(int(k))
    hasse = {}
    for p in sorted(primes):
        c = hasse_invariant(diag_sq, p)
        hasse[str(p)] = c
        print(f"  Hasse invariant c_{p}(M) = {c}   (I_n: +1)", flush=True)
    results["hasse_invariants_M"] = hasse
    results["hasse_real"] = hasse_real(diag_sq)
    results["hasse_primes_tested_note"] = ("Places tested: infinity, 2, and every odd prime factor returned by sympy.factorint(limit=1e6) "
                                          "of the odd part of det M (primality of the large cofactor recorded in crosschecks). "
                                          "At odd p not dividing det M the form is p-unimodular, hence c_p(M) = +1 = c_p(I_n).")
    # det square class over Q: det M = 1024 * s^2 -> square in Q iff s integer
    results["detM_is_rational_square"] = s is not None
    # product formula check
    prod_ = results["hasse_real"]
    for p in hasse: prod_ *= hasse[p]
    results["hasse_product_over_tested_places"] = prod_

    results["time_s"] = round(time.time() - t0, 1)
    with open(OUT_JSON, "w") as fh:
        json.dump(results, fh, indent=1)
    print("done, time", results["time_s"])

OUT_JSON = sys.argv[1] if len(sys.argv) > 1 else "results.json"
if __name__ == "__main__" and "--crosscheck" not in sys.argv:
    main()

# ======================================================================================
# Independent cross-checks (appended): odd-p Jordan decomposition, c_2 from the 2-adic
# Jordan symbol, invariance under random congruence, primality of the big cofactor.
# ======================================================================================
def jordan_padic_odd(G, p, prec):
    """Diagonalise symmetric G over Z_p (p odd) mod p^prec. Returns list of (v, unit)."""
    n = len(G); mod = p ** prec
    A = [[x % mod for x in row] for row in G]
    remaining = list(range(n)); out = []
    def vp(x):
        x %= mod
        if x == 0: return None
        v = 0
        while x % p == 0: x //= p; v += 1
        return v
    while remaining:
        best_v = None; best = None; diag = False
        for i in remaining:
            vi = vp(A[i][i])
            if vi is not None and (best_v is None or vi < best_v): best_v, best, diag = vi, i, True
        if best_v is None or not diag or True:
            # for odd p, if an off-diagonal entry has smaller valuation than all diagonal ones,
            # replace e_i by e_i + e_j to bring it to the diagonal.
            for ii, i in enumerate(remaining):
                for j in remaining[ii+1:]:
                    vij = vp(A[i][j])
                    if vij is not None and (best_v is None or vij < best_v):
                        # e_i <- e_i + e_j : new A[i][i] = A[i][i] + 2 A[i][j] + A[j][j]
                        for k in range(n):
                            A[i][k] = (A[i][k] + A[j][k]) % mod
                        for k in range(n):
                            A[k][i] = (A[k][i] + A[k][j]) % mod
                        best_v = vp(A[i][i]); best = i
                        assert best_v == vij
        i = best; v = best_v
        piv = A[i][i]; u = piv // (p ** v); uinv = pow(u, -1, mod)
        remaining.remove(i)
        for j in remaining:
            aji = A[j][i]
            if aji % mod == 0: continue
            Aj = A[j]; Ai = A[i]
            for k in remaining:
                Aj[k] = (Aj[k] - ((aji * (Ai[k] // (p ** v))) % mod) * uinv) % mod
        for j in remaining:
            A[j][i] = 0; A[i][j] = 0
        out.append((v, u % mod))
    return out

def hasse_from_padic_diag(diag_vu, p):
    """diag entries p^v u. c_p = prod_{i<j} (p^{v_i} u_i, p^{v_j} u_j)_p."""
    c = 1; n = len(diag_vu)
    if p == 2:
        for i in range(n):
            for j in range(i + 1, n):
                c *= hilbert_2(diag_vu[i][0] % 2, diag_vu[i][1] % 8, diag_vu[j][0] % 2, diag_vu[j][1] % 8)
    else:
        for i in range(n):
            for j in range(i + 1, n):
                c *= hilbert_odd(diag_vu[i][0], diag_vu[i][1], diag_vu[j][0], diag_vu[j][1], p)
    return c

def crosschecks(M, results):
    n = len(M)
    out = {}
    # (i) c_2 from the 2-adic Jordan symbol of M: even unimodular rank 254 sign '-' = H^126 + A2,
    #     H ~ <1,-1>, A2 ~ <2,6>; plus <2^8 u>, <2^16 u'> with the recorded units.
    jm = results["jordan_M"]
    diag = []
    for e in jm:
        if e["type"] == "II":
            k = e["rank"] // 2
            if e["sign"] == '+':
                diag += [(0, 1), (0, 7)] * k
            else:
                diag += [(0, 1), (0, 7)] * (k - 1) + [(1, 1), (1, 3)]
        else:
            for u, cnt in e["diag_mod8_multiset"].items():
                diag += [(e["scale"], int(u))] * cnt
    out["c2_from_jordan_symbol_of_M"] = hasse_from_padic_diag(diag, 2)
    # (ii) odd p Jordan decompositions
    odd_primes = [int(k) for k in results["detM_odd_part_factorint_limit1e6"]]
    c_odd = {}
    for p in odd_primes:
        if p.bit_length() > 64:   # skip the huge cofactor for the p-adic route (mod p^prec too big) -- still cheap actually
            pass
        d = jordan_padic_odd(M, p, 6)
        c_odd[str(p)] = hasse_from_padic_diag(d, p)
        vals = sorted(v for v, u in d)
        c_odd[str(p) + "_valuations"] = {str(v): vals.count(v) for v in set(vals)}
    out["c_p_from_padic_jordan"] = c_odd
    # (iii) invariance under a random unimodular integral congruence (minors route)
    R = [[int(i == j) for j in range(n)] for i in range(n)]
    for _ in range(3 * n):
        i, j = random.sample(range(n), 2)
        c = random.choice([-1, 1])
        for r in range(n):
            R[r][j] += c * R[r][i]
    Rt = transpose(R)
    MR = [[sum(M[i][k] * R[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    M2 = [[sum(Rt[i][k] * MR[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    minors2 = bareiss_minors(M2)
    assert minors2[-1] == int(results["detM"])
    diag_sq2 = [minors2[0]] + [minors2[k] * minors2[k - 1] for k in range(1, n)]
    out["hasse_after_random_congruence"] = {str(p): hasse_invariant(diag_sq2, p) for p in [2] + odd_primes}
    out["hasse_at_primes_not_dividing_det"] = {str(p): hasse_invariant(diag_sq2, p) for p in [3, 5, 11, 13, 19, 23]}
    # (iv) primality of the odd part's factors
    import sympy
    out["factor_primality"] = {str(p): bool(sympy.isprime(p)) for p in odd_primes}
    return out

if __name__ == "__main__" and "--crosscheck" in sys.argv:
    r = json.load(open(OUT_JSON))
    M, S = build_M(Q)
    cc = crosschecks(M, r)
    r["crosschecks"] = cc
    r["script_sha256"] = hashlib.sha256(open(__file__, "rb").read()).hexdigest()
    json.dump(r, open(OUT_JSON, "w"), indent=1)
    print(json.dumps(cc, indent=1))
