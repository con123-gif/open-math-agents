from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
parts=['a372561_digits_helpers.lean','a372561_digits_lift_helpers.lean','a372561_mincoins_helpers.lean','a372561_valuation_helpers.lean','a372561_factor_helpers.lean','a372561_iterate_helpers.lean','a372561_jac_weights.lean','a372561_cost_helpers.lean','a372561_finite_cores.lean','a372561_array_assembly.lean']
def strip(s):return '\n'.join(l for l in s.splitlines()if not l.lstrip().startswith(('import ','#')))+'\n'
body='\n'.join(strip((p/n).read_text()) for n in parts)
header='''import OMAStatements.S_oeis_a372561

/-!
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
Conjectures: Antti Karttunen, OEIS A372561, May2024.
Classical Jacobsthal identities, ordinary digit-sum carry inequalities,
and the known finite reduced-Collatz trajectory of27 are acknowledged.
The new target is the complete three-clause minimum-summand assertion,
with uniform lift exponents and the full infinite array retained.
No new general method or worldwide-priority claim is made.
-/

'''
(p/'a372561_complete_body.lean').write_text(body)
(p/'oeis-a372561_proof.lean').write_text(header+body)
(p/'ProbeA372561Full.lean').write_text((p/'a372561_statement.lean').read_text()+'\n'+body+'\n#print axioms OMA.solution\n')
# Isolated extended-digit and source-transform probes aid legitimate repairs.
dig='import Mathlib\n'+strip((p/parts[0]).read_text())+'\n'+strip((p/parts[1]).read_text())+'\n#print axioms A372561Certificate.D_plus_four\n#print axioms A372561Certificate.D_minus_four\n#print axioms A372561Certificate.D_double_minus_eight\n'
(p/'ProbeA372561DigitsLift.lean').write_text(dig)
s=(p/'a372561_statement.lean').read_text();pre=s[:s.index('theorem main')]+'end OMA.S_oeis_a372561\n'
val=pre+'\n'+'\n'.join(strip((p/n).read_text())for n in [parts[3],parts[4],parts[5]])+'\n#print axioms A372561Certificate.factor_data\n#print axioms A372561Certificate.grid_lift\n'
(p/'ProbeA372561Valuation.lean').write_text(val)
files=['a372561_statement.lean','oeis-a372561_proof.lean','ProbeA372561Full.lean']
(p/'a372561_current_hashes.json').write_text(json.dumps({n:hashlib.sha256((p/n).read_bytes()).hexdigest()for n in files},indent=2)+'\n')
print('complete probe lines',len((p/'ProbeA372561Full.lean').read_text().splitlines()))
