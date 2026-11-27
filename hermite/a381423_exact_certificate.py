"""Exact finite error checks for A381423; not an infinite proof."""
from math import factorial, isqrt
from pathlib import Path
import json

p = Path(__file__).resolve().parent
LIMIT = 500


def cutoff(n):
    return (1 + isqrt(8 * n + 17)) // 2


def predicted(n):
    q = cutoff(n)
    assert q >= n % 4
    return q - (q - n % 4) % 4


def signed_mode(n):
    nf = factorial(n)
    coeffs = []
    for j in range(n + 1):
        if (n - j) % 2:
            coeffs.append(0)
            continue
        m = (n - j) // 2
        num = (-1) ** m * nf * 2 ** j
        den = factorial(m) * factorial(j)
        assert num % den == 0
        coeffs.append(num // den)
    peak = max(coeffs)
    indices = [j for j, c in enumerate(coeffs) if c == peak]
    assert len(indices) == 1, (n, indices)
    return indices[0]


def block_data(q):
    start = q * (q - 1) // 2 - 2
    delta = (q - start) % 4
    assert q >= 4 and q - 2 >= delta
    return start + delta, (q - 2 - delta) // 4


actual = [signed_mode(n) for n in range(LIMIT + 2)]
assert actual == [predicted(n) for n in range(LIMIT + 2)]
raw = json.loads((p / "a381423_source.json").read_text())
source = raw[0] if isinstance(raw, list) else raw.get("results", [raw])[0]
published = [int(x) for x in source["data"].split(",")]
assert actual[: len(published)] == published
differences = [actual[n + 1] - actual[n] for n in range(LIMIT + 1)]
assert set(differences) <= {1, -3}
drops = [n for n, d in enumerate(differences) if d == -3]
assert drops[0] == 4
assert all(b - a in {4, 5} for a, b in zip(drops, drops[1:]))
expected_drops = set()
five_ends = set()
for q in range(4, cutoff(LIMIT) + 2):
    end, count = block_data(q)
    expected_drops.update(end + 4 * r for r in range(count + 1) if end + 4 * r <= LIMIT)
    if end <= LIMIT:
        five_ends.add(end)
    next_end, _ = block_data(q + 1)
    later_end, later_count = block_data(q + 8)
    assert next_end == end + 4 * count + 5
    assert later_end == end + 8 * q + 28
    assert later_count == count + 2
assert expected_drops == set(drops)
actual_five_ends = {4} | {b for a, b in zip(drops, drops[1:]) if b - a == 5}
assert actual_five_ends == five_ends
for n, mode in enumerate(actual):
    assert isqrt(2 * n) <= mode + 3
    assert mode <= isqrt(2 * n) + 2

receipt = {
    "scope": "Finite exact validation only; infinite proof is the mathematical argument and pending complete Lean certificate",
    "coefficient_orders_checked": [0, LIMIT + 1],
    "transitions_checked": [0, LIMIT],
    "source_revision": source["revision"],
    "published_terms_matched": len(published),
    "unique_signed_maxima": True,
    "exact_closed_formula": True,
    "every_negative_jump_formula": True,
    "complete_four_or_five_blocks": True,
    "five_block_endpoints": True,
    "quadratic_period_eight_spacing": True,
    "linear_four_block_count_shift": True,
    "explicit_sqrt_bounds": True,
}
(p / "a381423_exact_certificate_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt))
