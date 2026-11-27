"""Concatenate ordinary Lean helper sources for the current orbit/minor check."""
from pathlib import Path

base = Path(__file__).resolve().parent
sources = [
    "MO513259Permanent.lean",
    "MO513259Parity.lean",
    "MO513259RowReplacement.lean",
    "MO513259RowExpansion.lean",
    "MO513259PairSums.lean",
    "MO513259CopyRowOrbit.lean",
    "MO513259ForcedMinor.lean",
    "MO513259CRT.lean",
    "MO513259Polar.lean",
]
parts = ["import Mathlib\n"]
for name in sources:
    lines = (base / name).read_text().splitlines()
    assert lines[0] == "import Mathlib"
    parts.append("\n".join(line for line in lines[1:]
                           if not line.startswith("#print axioms ")) + "\n")
for name in ["det_forceTwoRows", "map_copyRowHalf", "copyRowHalf_mod_two_inverse",
             "upperPairSum_polar", "copyRowHalf_eight_reduction"]:
    parts.append("#print axioms OMA.MO513259." + name + "\n")
output = base / "ProbeMO513259ForcedMinor.lean"
output.write_text("\n".join(parts))
print(output)
