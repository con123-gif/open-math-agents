"""Reproduce the bounded test of an UNPROVED corrected congruence."""
import json
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "runtime_research"))
from MO513259_screen import invmod, permanent


def detmod(a, modulus=8):
    a = [row[:] for row in a]
    determinant = 1
    n = len(a)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j] % 2), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            determinant = -determinant
        value = a[j][j] % modulus
        determinant = determinant * value % modulus
        inverse = pow(value, -1, modulus)
        for i in range(j + 1, n):
            factor = a[i][j] * inverse % modulus
            for k in range(j, n):
                a[i][k] = (a[i][k] - factor * a[j][k]) % modulus
    return determinant % modulus


rng = random.Random(513259004)
output = []
for n in [2, 4, 6, 8, 10]:
    count = 0
    bad = None
    for t in range(2000):
        a = [[0] * n for _ in range(n)]
        for i in range(n):
            a[i][i] = 2 * rng.randrange(4)
            for j in range(i):
                a[i][j] = a[j][i] = rng.randrange(8)
        b = invmod(a, 8)
        if b is None:
            continue
        count += 1
        zeroed = [row[:] for row in a]
        for i in range(n):
            zeroed[i][i] = 0
        proposed = detmod(zeroed) * pow(detmod(a), -1, 8) % 8
        actual = permanent(b, 8)
        if actual != proposed:
            bad = {"A": a, "B": b, "q": actual, "formula": proposed}
            break
    output.append({"n": n, "eligible": count, "trials": t + 1, "bad": bad})
    print(n, count, "bad", bool(bad), flush=True)
Path(__file__).with_suffix(".json").write_text(json.dumps(output, indent=2) + "\n")
