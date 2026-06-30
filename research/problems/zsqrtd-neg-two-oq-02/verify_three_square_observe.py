import math

N = 20000

def is_4a8b7(n):
    while n % 4 == 0 and n > 0:
        n //= 4
    return n % 8 == 7

# sum of three squares membership via direct search bounded by sqrt
def is_three_squares(n):
    r = int(math.isqrt(n))
    for a in range(r+1):
        m = n - a*a
        rb = int(math.isqrt(m))
        for b in range(a, rb+1):
            c2 = m - b*b
            c = int(math.isqrt(c2))
            if c*c == c2 and c >= b:
                return True
    return False

# representable as x^2 + 2 y^2 (the Z[sqrt(-2)] norm form)
def is_x2_2y2(n):
    y = 0
    while 2*y*y <= n:
        rem = n - 2*y*y
        r = int(math.isqrt(rem))
        if r*r == rem:
            return True
        y += 1
    return False

# 1) verify the three-square iff: 3sq  <=>  not 4^a(8b+7)
bad = 0
for n in range(0, N+1):
    lhs = is_three_squares(n)
    rhs = not is_4a8b7(n)
    if lhs != rhs:
        bad += 1
        if bad <= 5:
            print("MISMATCH", n, "3sq", lhs, "not4a8b7", rhs)
print(f"[iff] three-square <=> not 4^a(8b+7) over 0..{N}: mismatches = {bad}")

# 2) quantify the Z[sqrt(-2)] reach: among n that ARE sums of three squares,
#    how many are representable by x^2+2y^2 (the parent norm form)?
three = [n for n in range(1, N+1) if is_three_squares(n)]
reach = [n for n in three if is_x2_2y2(n)]
print(f"[reach] sums of three squares in 1..{N}: {len(three)}")
print(f"[reach] of those, representable as x^2+2y^2: {len(reach)} ({100*len(reach)/len(three):.1f}%)")

# 3) smallest three-square numbers NOT reachable by x^2+2y^2 (the genuine gap witnesses)
gap = [n for n in three if not is_x2_2y2(n)][:15]
print(f"[gap] smallest 3-square numbers NOT of form x^2+2y^2: {gap}")

# 4) sanity: x^2+2y^2 numbers are always 3-squares (subset check)
viol = [n for n in range(1, N+1) if is_x2_2y2(n) and not is_three_squares(n)]
print(f"[subset] x^2+2y^2 numbers that are NOT sums of three squares: {len(viol)} (expect 0)")
