"""Assemble the complete source-faithful certificate; does not claim a kernel pass."""
from pathlib import Path
import hashlib
import json

p = Path(__file__).resolve().parent
parts = [
    "a381423_proof_body.lean",
    "a381423_new_helpers.lean",
    "a381423_selector_extension.lean",
    "a381423_blocks_extension.lean",
    "a381423_assembly.lean",
]
body = "\n".join((p / f).read_text() for f in parts)
statement = (p / "a381423_statement.lean").read_text()
proof = "import OMAStatements.S_oeis_a381423\n\n" + body
probe = statement + "\n" + body + "\n#print axioms OMA.solution\n"
(p / "a381423_complete_proof_body.lean").write_text(body)
(p / "oeis-a381423_proof.lean").write_text(proof)
(p / "ProbeA381423Full.lean").write_text(probe)
(p / "a383246_lint/proofs/oeis-a381423.lean").write_text(proof)
receipt = {
    "statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
    "canonical_proof_sha256": hashlib.sha256(proof.encode()).hexdigest(),
    "full_probe_sha256": hashlib.sha256(probe.encode()).hexdigest(),
    "statement_exact_probe_prefix": probe.startswith(statement),
    "entire_proof_body_identical_in_probe_and_canonical": body in probe and body in proof,
    "kernel_status": "Must be determined from the actual matching Actions run",
}
(p / "a381423_frozen_hashes.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt))
