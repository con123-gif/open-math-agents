from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
parts=['a372556_core.lean','a372556_normal.lean','a372556_assembly.lean']
body='\n'.join((p/name).read_text() for name in parts)
header='''import OMAStatements.S_oeis_a372556

/-!
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
Conjecture: Antti Karttunen, OEIS A372556, May 10, 2024.
Jacobsthal identities and the local three-coin exchange are classical;
see A. F. Horadam, Jacobsthal Representation Numbers, Fibonacci Quarterly
34.1 (1996), 40-54. Carlitz, Scoville and Hoggatt (1972) study canonical
distinct-summand representations, which need not minimize cardinality.
The present proof uses a score-maximal minimum-cardinality representation
and an additional four-coin exchange to obtain the full largest-two-coin
conclusion. No claim of a new general method or global priority is made.
-/

'''
(p/'a372556_complete_proof_body.lean').write_text(body)
(p/'oeis-a372556_proof.lean').write_text(header+body)
(p/'ProbeA372556Full.lean').write_text((p/'a372556_statement.lean').read_text()+'\n'+body+'\n#print axioms OMA.solution\n')
names=['a372556_statement.lean','oeis-a372556_proof.lean','ProbeA372556Full.lean']
hashes={name:hashlib.sha256((p/name).read_bytes()).hexdigest() for name in names}
(p/'a372556_file_hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(json.dumps(hashes,indent=2))
