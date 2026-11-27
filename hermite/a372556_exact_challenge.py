import json,time
from pathlib import Path
P=Path(__file__).parent
N=100000
J=[0,1]
while J[-1]<=N:J.append(J[-1]+2*J[-2])
J.extend([J[-1]+2*J[-2],3*J[-1]+2*J[-2]])
coins=J[2:];dp=[0]*(N+1); score=[0]*(N+1);last=[0]*(N+1)
for n in range(1,N+1):
 options=[(dp[n-J[j]]+1,-score[n-J[j]]-5**j,j) for j in range(2,len(J)) if J[j]<=n]
 dp[n],neg,last[n]=min(options);score[n]=-neg
 counts=[0]*len(J);m=n
 while m: j=last[m];counts[j]+=1;m-=J[j]
 k=max(j for j in range(2,len(J)) if J[j]<=n)
 assert max(j for j in range(2,len(J)) if counts[j])>=k-1,(n,counts)
 for j in range(2,k+1):
  if j%2: assert counts[j]<=1,(n,j,counts)
  else:
   assert counts[j]<=4,(n,j,counts)
   if counts[j]==4:assert sum(counts[2:j])==0,(n,j,counts)
  if j<k:assert not(counts[j]>=2 and counts[j+1]),(n,j,counts)
  v=sum(counts[i]*J[i] for i in range(2,j+1))
  assert v<(J[j+2] if j%2==0 else J[j+1]),(n,j,counts)
# Source data gives the largest eligible index, not necessarily our score-max index.
x=json.load(open(P/'a372556_source.json')); vals=list(map(int,x['data'].split(',')))
for n,a in enumerate(vals):
 if n==0:assert a==0;continue
 aa=max(j for j in range(2,len(J)) if J[j]<=n and dp[n-J[j]]==dp[n]-1)
 assert a==aa,(n,a,aa)
receipt={'tested_n_min':0,'tested_n_max':N,'all_exact_cardinalities':True,'all_exchange_normal_forms':True,'all_prefix_bounds':True,'all_largest_two_coin_conclusions':True,'all_source_terms':len(vals),'finite_test_only':True,'lean_kernel_verification':False}
(P/'a372556_exact_challenge_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
