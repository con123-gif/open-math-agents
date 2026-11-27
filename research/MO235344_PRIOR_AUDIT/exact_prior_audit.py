"""Independent exact audit of byrohan's public MO235344 witness (no Lean claim)."""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import json, hashlib

def det(a):
    n=len(a)
    if n==0:return 1
    a=[list(map(Fraction,r)) for r in a];ans=Fraction(1)
    for c in range(n):
        p=next((r for r in range(c,n) if a[r][c]),None)
        if p is None:return 0
        if p!=c:a[p],a[c]=a[c],a[p];ans=-ans
        q=a[c][c];ans*=q
        for r in range(c+1,n):
            t=a[r][c]/q
            for j in range(c,n):a[r][j]-=t*a[c][j]
    return int(ans) if ans.denominator==1 else ans

def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(a))) for j in range(len(a))] for i in range(len(a))]
def minor(a,s):return det([[a[i][j] for j in s] for i in s])
def all_minors(a):return [minor(a,[i for i in range(len(a)) if mask>>i&1]) for mask in range(1<<len(a))]
def irred(a):
    n=len(a)
    return all(any(a[i][j]!=0 for i in range(n) if mask>>i&1 for j in range(n) if not(mask>>j&1)) for mask in range(1,(1<<n)-1))
def triangle(a,i,j,k):return a[i][j]*a[j][k]*a[k][i]
def transpose(a):return list(map(list,zip(*a)))
A=[[1,2,0,2,2,2],[0,0,1,0,0,0],[2,1,0,2,2,2],[2,2,0,3,4,4],[2,2,0,2,3,4],[2,2,0,2,2,3]]
B=[[1,0,2,-2,2,-2],[2,0,1,-2,2,-2],[0,1,0,0,0,0],[-2,0,-2,3,-4,4],[2,0,2,-2,3,-4],[-2,0,-2,2,-2,3]]
I=[[int(i==j) for j in range(6)] for i in range(6)]
ma,mb=all_minors(A),all_minors(B)
assert mul(A,B)==I==mul(B,A)
assert ma==mb and irred(A)
# AD=DB at(0,1):2d1=0. A^T D=DB at(0,3),(3,4),(4,0):
# 2d3=-2d0, 2d4=-4d3, 2d0=2d4, hence d0=0.
assert (A[0][1],B[0][1])==(2,0)
assert (A[3][0],B[0][3],A[4][3],B[3][4],A[0][4],B[4][0])==(2,-2,2,-4,2,2)
X=[[53,96,-32,80,40,20],[-32,45,92,-16,-8,-4],[96,-28,45,48,24,12],[20,12,-4,117,112,56],[40,24,-8,20,117,112],[80,48,-16,40,20,117]]
Y=[[53,-32,96,-80,40,-20],[96,45,-28,-48,24,-12],[-32,92,45,16,-8,4],[-20,4,-12,117,-112,56],[40,-8,24,-20,117,-112],[-80,16,-48,40,-20,117]]
mx,my=all_minors(X),all_minors(Y)
assert mul(X,Y)==[[107**2*I[i][j] for j in range(6)] for i in range(6)]
assert mx==my and all(z>0 for z in mx)
assert all(z!=0 for row in X for z in row)
t1=(triangle(X,0,1,2),triangle(Y,0,1,2))
t2=(triangle(transpose(X),0,3,4),triangle(Y,0,3,4))
assert t1[0]!=t1[1] and t2[0]!=t2[1]
# Independent current Matrix lane 5x5 witness, normalized by3.
U=[[1,2,-2,-2,0],[-4,1,2,2,0],[2,-2,-1,-4,0],[0,0,0,0,3],[-2,2,-2,1,0]]
V=[[1,-2,-2,0,-2],[4,1,-2,0,-2],[2,2,-1,0,-4],[-2,-2,-2,0,1],[0,0,0,3,0]]
I5=[[int(i==j) for j in range(5)] for i in range(5)]
assert mul(U,V)==[[9*I5[i][j] for j in range(5)] for i in range(5)]
assert all_minors(U)==all_minors(V) and irred(U)
assert U[0][3]!=0 and V[0][3]==0
trans_ob=(triangle(transpose(U),0,2,1),triangle(V,0,2,1))
assert trans_ob[0]!=trans_ob[1]
r={'foreign_author':'byrohan','foreign_public_commit':'4a3de5ffadcc285760ceebc1dd12b9b5b50f025d','foreign_commit_utc':'2026-11-27T07:06:42Z','earlier_statement_pr':3755,'sparse_six_dimensional':{'detA':det(A),'detB':det(B),'two_sided_integer_inverse':True,'all64_principal_minors_equal':True,'all62_nonempty_proper_cuts_have_outgoing_nonzero_entry':True,'ordinary_diagonal_obstruction':'2*d1=0','transpose_diagonal_obstruction':'d3=-d0;d4=-2*d3;d0=d4 => d0=0','principal_minors_by_bitmask':ma},'additional_dense_six_dimensional':{'denominator':107,'XY_equals_107_squared_I':True,'all_entries_nonzero':True,'all64_corresponding_principal_minors_equal_and_positive':True,'ordinary_triangle_products':t1,'transpose_triangle_products':t2},'matrix_lane_five_dimensional':{'denominator':3,'UV_equals_9I':True,'all32_corresponding_principal_minors_equal':True,'irreducible_support':True,'ordinary_diagonal_obstruction':'U03=-2,V03=0 forces d3=0','transpose_triangle_products':trans_ob},'scope_conclusion':'The earlier six-dimensional witness already disproves the exact universal original conjecture. The current five-dimensional witness improves dimension, not the solved source scope; no second source count.','verification_limit':'This script independently verifies finite exact rational/integer identities constituting complete explicit counterexamples. It does not claim independent Lean compilation or official full-proof acceptance for the foreign file.'}
p=Path(__file__).with_name('EXACT_PRIOR_AUDIT_RESULT.json');p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
