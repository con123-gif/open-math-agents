import json
from pathlib import Path
P=Path(__file__).parent

def D(n):
 s=0
 while n:s+=n%4;n//=4
 return s

def witness(q):
 bits=[i for i in range(q.bit_length()) if(q>>i)&1]
 s=sum((-1)**i for i in bits)
 wanted=1 if s<1 else 0
 count=abs(s-1)//3
 selected=[i for i in bits if i%2==wanted][:count]
 assert len(selected)==count
 out=[i for i in bits if i not in selected]
 for i in selected:assert i>0;out +=[i-1,i-1]
 assert sum(2**i for i in out)==q and sum((-1)**i for i in out)==1
 return sorted(out)

orbit=[27];valuations=[]
while orbit[-1]!=1:
 q=3*orbit[-1]+1;v=(q&-q).bit_length()-1
 valuations.append(v);orbit.append(q>>v)
assert len(orbit)==42 and orbit[-1]==1
rows=[]
for s,y in enumerate(orbit):
 q=3*y+1;W,V=D(q),D(2*q);R=max((2*W+1)//3,(2*V-1)//3)
 w=witness(q)
 assert len(w)==R and R<=9 and R%2==1
 row={'s':s,'y':y,'q':q,'W':W,'V':V,'R':R,'upper_exponents':w}
 if s:
  v=valuations[s-1];row['min_exponent']=v
  if v==1:
   cert=max(2*D(q-1)-3,2*D(2*(q-1))+3)
   assert cert>=3*R
   row['E1_minus3_numerator']=cert
   if R==9:assert D(2*(q-2))>7;row['E1_minus7_weight']=D(2*(q-2))
 rows.append(row)
assert [r for r in rows if r['y']==233][0]['R']==7
assert [r for r in rows if r['y']==911][0]['R']==9
receipt={'finite_data_only':True,'no_infinite_theorem_claim_from_script':True,'orbit':orbit,'valuation_steps':valuations,'rows':rows,'E1_case_count':sum(r.get('min_exponent')==1 for r in rows),'source_three_clauses_retained':True}
(P/'a372561_lift_certificate.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Verified42 finite base rows,',receipt['E1_case_count'],'E1 certificates, upper power witnesses and parity sums; no infinite theorem asserted by this script.')
