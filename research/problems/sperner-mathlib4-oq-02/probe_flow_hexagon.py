import itertools

negL = [2,3,0,1]
sgn  = [0,0,1,1]  # Fin4 -> {0,1}

def Vlab(a,b,c):
    return [a,b,c,negL[a],negL[b],negL[c]]  # Fin6 -> Fin4

def dir_open(x,y):  # pos->neg directed door on oriented edge x->y (x,y are sgn bits)
    return 1 if (x==0 and y==1) else 0

# Cells: triangles 0..5.  T_i = (d, v_i, v_{i+1}) CCW.
# Doors: ('S',j) spoke {d,v_j} j=0..5 ; ('E',i) boundary edge {v_i,v_{i+1}} i=0..5.
DOORS = [('S',j) for j in range(6)] + [('E',i) for i in range(6)]

def sgn_v(a,b,c,i):
    return sgn[Vlab(a,b,c)[i%6]]

def tail(a,b,c,d, i, door):
    sd = sgn[d]
    if door[0]=='E':
        k=door[1]
        if k!=i: return False
        return dir_open(sgn_v(a,b,c,i), sgn_v(a,b,c,i+1))==1   # tail = T_i when E_i open
    else: # spoke j
        j=door[1]
        svj=sgn_v(a,b,c,j)
        arrow_d_to_vj = (sd==0 and svj==1)   # d->v_j
        arrow_vj_to_d = (svj==0 and sd==1)   # v_j->d
        # arrow d->v_j : tail = T_j ; arrow v_j->d : tail = T_{j-1}
        if arrow_d_to_vj and i==j: return True
        if arrow_vj_to_d and i==(j-1)%6: return True
        return False

def head(a,b,c,d, i, door):
    sd=sgn[d]
    if door[0]=='E':
        return False   # outside end missing
    else:
        j=door[1]
        svj=sgn_v(a,b,c,j)
        arrow_d_to_vj = (sd==0 and svj==1)
        arrow_vj_to_d = (svj==0 and sd==1)
        # arrow d->v_j : head = T_{j-1} ; arrow v_j->d : head = T_j
        if arrow_d_to_vj and i==(j-1)%6: return True
        if arrow_vj_to_d and i==j: return True
        return False

def outCount(a,b,c,d,i): return sum(tail(a,b,c,d,i,dr) for dr in DOORS)
def inCount(a,b,c,d,i):  return sum(head(a,b,c,d,i,dr) for dr in DOORS)
def tailCount(a,b,c,d,dr): return sum(tail(a,b,c,d,i,dr) for i in range(6))
def headCount(a,b,c,d,dr): return sum(head(a,b,c,d,i,dr) for i in range(6))

bad_hdeg=bad_hwf=bad_himb=no_source=0
himb_vals=set()
for a,b,c,d in itertools.product(range(4),repeat=4):
    # hdeg
    ok=True
    for i in range(6):
        if outCount(a,b,c,d,i)>1 or inCount(a,b,c,d,i)>1: ok=False
    if not ok: bad_hdeg+=1
    # hwf': each door interior(1,1)/bout(1,0)/bin(0,1)/absent(0,0)
    for dr in DOORS:
        tc=tailCount(a,b,c,d,dr); hc=headCount(a,b,c,d,dr)
        if (tc,hc) not in [(1,1),(1,0),(0,1),(0,0)]: bad_hwf+=1
    # himb: #bout > #bin
    bout=sum(1 for dr in DOORS if (tailCount(a,b,c,d,dr),headCount(a,b,c,d,dr))==(1,0))
    binn=sum(1 for dr in DOORS if (tailCount(a,b,c,d,dr),headCount(a,b,c,d,dr))==(0,1))
    himb_vals.add((bout,binn))
    if not (binn<bout): bad_himb+=1
    # source exists?
    srcs=[i for i in range(6) if outCount(a,b,c,d,i)==1 and inCount(a,b,c,d,i)==0]
    if len(srcs)==0: no_source+=1

print("total labellings:", 4**4)
print("bad_hdeg:", bad_hdeg)
print("bad_hwf :", bad_hwf)
print("bad_himb:", bad_himb)
print("no_source:", no_source)
print("(bout,bin) values seen:", sorted(himb_vals))
