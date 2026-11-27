"""Assemble auditable ordinary Lean helpers; no proof-generating metaprogramming."""
from pathlib import Path

base = Path(__file__).resolve().parent
root = base.parents[1]
det_helper = root / "fresh_algebra_work/MO513259DetEvenPerturbation.lean"
if not det_helper.exists():
    det_helper = base / "MO513259DetEvenPerturbation.lean"
inputs = [
    base / "MO513259Permanent.lean",
    base / "MO513259Parity.lean",
    base / "MO513259Alternating.lean",
    det_helper,
    base / "MO513259DetIntegration.lean",
    base / "MO513259Pivot.lean",
    base / "MO513259CRT.lean",
]
parts = ["import Mathlib\n"]
for path in inputs:
    source = path.read_text()
    assert source.startswith("import Mathlib\n")
    lines = [line for line in source.splitlines()[1:]
             if not line.startswith("#print axioms ")]
    parts.append("\n".join(lines) + "\n")
parts.append("#print axioms OMA.MO513259.det_add_even_symm_pair\n")
parts.append("#print axioms OMA.MO513259.permanent_double_shear\n")
parts.append("#print axioms OMA.MO513259.duplicate_row_even_eight\n")
parts.append("#print axioms OMA.MO513259.base_two_scalar\n")
parts.append("#print axioms OMA.MO513259.map_inverse_diagonal_zero_mod_two\n")
parts.append("#print axioms OMA.MO513259.exists_unit_offdiagonal\n")
parts.append("#print axioms OMA.MO513259.offdiagonal_pivot_det_unit\n")
parts.append("#print axioms OMA.MO513259.mod_twenty_four_of_three_component_facts\n")
output = base / "ProbeMO513259DetInfrastructure.lean"
output.write_text("\n".join(parts))
assert output.read_text().count("import Mathlib") == 1
print(output)
