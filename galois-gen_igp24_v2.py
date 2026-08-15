"""IGP24 generator v2 — pair AND triple composita, wider source library.
24 = 2*12 = 3*8 = 4*6 = 2*2*6 = 2*3*4 = 2*2*2*3.
Triples carry nested block systems -> different imprimitive groups than pairs."""
import sympy as sp, json, sys, itertools
from sympy import Poly, symbols, resultant, expand, factor_list, discriminant
from sympy.polys.galoistools import gf_factor_sqf, gf_from_int_poly, gf_sqf_p
from sympy.polys.domains import ZZ
x,y=symbols('x y')
def nb(n): return x**n - sum(x**i for i in range(n))

SRC={
 2:[x**2-x-1,x**2-2,x**2-3,x**2+1,x**2-x+1,x**2-5,x**2-6,x**2-7,x**2+x+2,x**2-x-3,
    x**2-10,x**2-11,x**2+2,x**2-13,x**2-x-5,x**2+x+3],
 3:[nb(3),x**3-x-1,x**3-2,x**3-3,x**3+x-1,x**3-x**2-1,x**3-x**2+x+1,x**3-4,x**3-x**2-2,
    x**3+x**2-1,x**3-5,x**3+2*x-1],
 4:[nb(4),x**4-2,x**4-x-1,x**4+1,x**4-x**3-1,x**4+x+1,x**4-3,x**4-x**2-1,x**4+x**2+1,
    x**4-x**3+x**2-x+1,x**4-5,x**4+x**3+x**2+x+1],
 6:[nb(6),x**6-2,x**6+x**5+x**4+x**3+x**2+x+1,x**6-x-1,x**6+3,x**6-x**5-1,x**6-x**3-1,
    x**6+x**3+1,x**6-3,x**6+x**4+x**2+1,x**6-x**4-1],
 8:[nb(8),x**8-2,x**8+1,x**8-x-1,x**8+x**4+1,x**8-x**7-1,x**8-3,x**8+x**5-1],
 12:[nb(12),x**12-2,x**12+1,x**12-x-1,x**12+x**6+1,x**12-3,x**12-x**11-1],
}
def irr(e):
    fl=factor_list(e); return len(fl[1])==1 and fl[1][0][1]==1
def comp(pa,pb,c=1):
    A=Poly(pa.subs(x,y),y); B=Poly(expand(pb.subs(x,x-c*y)),y)
    return Poly(expand(resultant(A.as_expr(),B.as_expr(),y)),x)
def fp(co,nprimes=25):
    d=abs(int(discriminant(sum(v*x**i for i,v in enumerate(co)),x)))
    dens=list(reversed(co)); out=[]
    for i in range(1,nprimes+1):
        q=sp.prime(i)
        if d%q==0: out.append(None); continue
        f=gf_from_int_poly(dens,q)
        if not gf_sqf_p(f,q,ZZ): out.append(None); continue
        _,fac=gf_factor_sqf(f,q,ZZ)
        out.append(tuple(sorted(len(g)-1 for g in fac)))
    return tuple(out), d

out={}; tried=0
def consider(P,note):
    global tried; tried+=1
    if P.degree()!=24: return
    lc=P.coeff_monomial(x**24)
    if lc==-1: P=Poly(-P.as_expr(),x); lc=1
    if lc!=1: return
    co=[int(P.coeff_monomial(x**i)) for i in range(25)]
    if co[0]==0: return
    if max(abs(v) for v in co)>10**14: return          # keep discriminants sane
    if not irr(P.as_expr()): return
    f,d=fp(co)
    if f not in out or d<out[f][0]: out[f]=(d,co,note)

# --- pairs ---
for (a,b) in [(2,12),(3,8),(4,6)]:
    for pa in SRC[a]:
        for pb in SRC[b]:
            try: consider(comp(pa,pb,1), f"{a}x{b}: {sp.sstr(pa)} | {sp.sstr(pb)}")
            except Exception: pass
json.dump([{"disc":str(v[0]),"coeffs":v[1],"note":v[2]} for v in out.values()],open("igp24_candidates_v2.json","w"))
print(f"after pairs: {len(out)} fields ({tried} tried)", file=sys.stderr)

# --- triples: 2*2*6, 2*3*4 ---
for (a,b,c_) in [(2,2,6),(2,3,4)]:
    for pa in SRC[a][:7]:
        for pb in SRC[b][:7]:
            if a==b and sp.sstr(pa)>=sp.sstr(pb): continue
            try:
                M=comp(pa,pb,1)
                if M.degree()!=a*b or not irr(M.as_expr()): continue
                for pc in SRC[c_][:6]:
                    try: consider(comp(M.as_expr(),pc,1), f"{a}x{b}x{c_}: {sp.sstr(pa)} | {sp.sstr(pb)} | {sp.sstr(pc)}")
                    except Exception: pass
            except Exception: pass
json.dump([{"disc":str(v[0]),"coeffs":v[1],"note":v[2]} for v in out.values()],open("igp24_candidates_v2.json","w"))
print(f"after triples: {len(out)} fields ({tried} tried)", file=sys.stderr)
json.dump([{"disc":str(v[0]),"coeffs":v[1],"note":v[2]} for v in out.values()],
          open("igp24_candidates_v2.json","w"))
