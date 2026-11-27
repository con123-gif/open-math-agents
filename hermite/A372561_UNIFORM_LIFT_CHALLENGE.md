# A372561: independent challenge of the general lift-cost theorem

27 November 2026. Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6; exact serving variant not exposed. This is an informal independent mathematical review, not a Lean pass, official submission, acceptance or historical-priority claim. No lease was claimed. The source/array/prior and finite E=1 audit is assigned to the number-theory lane; this note independently checks the unbounded lift theorem in reversal_work/fresh/A372561_COMPLETE_HAND_PROOF_DRAFT.md.

Let J_i=(2^i-(-1)^i)/3 for i>=2, and let c(N) be the least number of those coins summing to N. Let y be a positive odd integer, q=3y+1, and

    L_E(y)=4^E y+(4^E-1)/3=(q4^E-1)/3.

Write D for the base4 digit sum, W=D(q), V=D(2q), and

    T=max((2W+1)/3,(2V-1)/3).

The reviewed claim is c(L_E(y))=T whenever T<=9 and E>=2.

## Upper representation and integrality

Let a and b count the binary1-bits of q in even and odd positions respectively. Then W=a+2b,V=2a+b, and s=a-b is congruent1 modulo3 because q is congruent1 modulo3. Thus both displayed quotients defining T are integers, and

    T=a+b+|s-1|/3.

If s<1, split (1-s)/3 original odd-position bits, each into two bits one position lower. Each split raises the alternating parity sum by3 and raises the number of summands by1. There are enough such bits:1-s<=3b follows from a+2b>=1. If s>1, split (s-1)/3 original even-position bits instead. This lowers the parity sum by3; the availability inequality s-1<=3a holds. Since q is even, no original even-position bit is at position0, so these splits are legal. Newly created repeated powers are permitted; no distinctness is required.

The resulting T powers sum to q and have alternating parity sum1. Shifting all exponents by2E therefore produces T Jacobsthal coins with sum(q4^E-1)/3. Every shifted exponent is at least2 for E>=1. This proves the upper bound without relying on a finite search. The parity sum1 also proves T is odd.

## Lower invariant and exhaustive cases

For any r-coin representation, let e,o count even and odd indices and put S=e-o. The exact identity is

    3N+S=sum 2^i.

Base4 carries never increase digit sum. A power2^i has digit weight1 for even i and2 for odd i; after doubling these weights interchange. Consequently, with U=3N+S,

    2D(U)<=3r-S,     2D(2U)<=3r+S.

For N=L_E(y), E>=1 gives N congruent1 modulo4. All coin indices are at least2, so the power sum is divisible by4 and S is congruent1 modulo4. Also all these Jacobsthal coins are odd and N is odd, so r is odd. If r<T<=9, then r<=7 and |S|<=r leaves exactly the possible values S=-7,-3,1,5. There is no omitted negative case.

For S=1, U=q4^E, and the two inequalities are precisely3r>=2W+1 and3r>=2V-1. Thus r>=T, a contradiction.

For S=5, U=q4^E+4. Because q is even, D(U)=W+1 and D(2U)=V+2 already for E=1. Thus3r>=2W+7 and3r>=2V-1, again contradicting r<T.

## Borrow identities, including the exponent boundaries

For every positive integer a and m>=0,

    D(a4^m-1)=D(a-1)+3m,
    D(2(a4^m-1))=D(2(a-1))+3m.

The first is ordinary borrowing. For the second, m=0 is immediate; for m>=1 use2(a4^m-1)=(2a-1)4^m+(4^m-2), together with D(4^m-2)=3m-1 and D(2a-1)=D(2a-2)+1. The last increment creates no carry because2a-2 is even. This proves the formula also at m=0 rather than using an invalid negative remainder there.

For S=-3, U=4(q4^(E-1)-1), so these identities give

    D(U)=D(q-1)+3(E-1),
    D(2U)=D(2(q-1))+3(E-1).

Subadditivity gives D(q-1)>=W-1. Writing q=2t gives D(2(q-1))=D(t-1)+2>=D(t)+1=V+1. Therefore E>=2 gives3r>=2W+1 and3r>=2V+11, which are sufficient to force r>=T.

For S=-7, r must be7 and T must be9, with e=0,o=7. Hence D(2U)<=7. Now U=q4^E-8 and, for E>=2,

    2U=16(2q4^(E-2)-1),
    D(2U)=D(2(q-1))+3E-5>=V+2.

The formula remains valid at E=2 by the m=0 case of the first borrow identity. T=9 means W=13 or V=14. Moreover W=D(4q)=D(2q+2q)<=2V, so either alternative implies V>=7. Thus D(2U)>=9, contradicting D(2U)<=7.

The upper and exhaustive lower arguments prove the stated general lift-cost equality. All divisions, signs, borrow lengths and minimum-index boundaries check. The finite orbit and finite E=1 tests are not used to infer this infinite theorem, and their separate review remains necessary for the full A372561 source claim.
