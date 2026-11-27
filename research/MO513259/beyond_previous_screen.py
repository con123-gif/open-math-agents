"""Reproduce the exact bounded random screen, not a universal proof."""
import json
from pathlib import Path
import random
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "runtime_research"))
from MO513259_screen import invmod, permanent, verify_inverse

rng = random.Random(513259)
result = {
    "method": "Exact modular random simple graphs beyond the previous exhaustive n<=6 screen",
    "seed": 513259,
    "finite_only": True,
    "checked": [],
}
for n, trials in [(8, 2000), (10, 1000), (12, 400)]:
    c8 = c24 = 0
    started = time.time()
    for z in range(trials):
        a = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(i):
                a[i][j] = a[j][i] = rng.randrange(2)
        b8 = invmod(a, 8)
        if b8 is None:
            continue
        c8 += 1
        q8 = permanent(b8, 8)
        if q8 != 1:
            assert verify_inverse(a, b8, 8) and verify_inverse(b8, a, 8)
            result["counterexample"] = {
                "conjecture": 1, "n": n, "A": a, "B": b8, "q8": q8}
            break
        b3 = invmod(a, 3)
        if b3 is None:
            continue
        c24 += 1
        b24 = [[(b8[i][j] + 8 * ((b3[i][j] - b8[i][j]) * 2 % 3)) % 24
                for j in range(n)] for i in range(n)]
        p = permanent(a, 24)
        q = permanent(b24, 24)
        if (2 * p + q - 3) % 24:
            assert verify_inverse(a, b24, 24) and verify_inverse(b24, a, 24)
            result["counterexample"] = {
                "conjecture": 2, "n": n, "A": a, "B": b24, "p": p, "q": q}
            break
    row = {
        "n": n, "trials": z + 1, "invertible8": c8, "invertible24": c24,
        "seconds": round(time.time() - started, 3),
    }
    result["checked"].append(row)
    print(json.dumps(row), flush=True)
    if "counterexample" in result:
        print(json.dumps(result["counterexample"]), flush=True)
        break
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
