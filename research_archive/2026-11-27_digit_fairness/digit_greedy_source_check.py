"""Reproduce published prefixes from literal greedy decimal rules.

This is a source-translation check only. It does not prove infinite coverage.
The full infinite arguments are in the companion Lean proof bodies.
"""

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def source_terms(sequence):
    payload = json.loads((HERE / (sequence.lower() + ".json")).read_text())
    if isinstance(payload, list):
        record = payload[0]
    elif "results" in payload:
        record = payload["results"][0]
    else:
        record = payload
    return [int(x) for x in record["data"].split(",")]


def greedy_prefix(count, parity, forbidden, positive, seed):
    used = set()
    previous = seed
    result = []
    for _ in range(count):
        candidate = 1 if positive else 0
        while True:
            digits = [int(c) for c in str(candidate)]
            internal = all(
                left % 2 != parity
                or (right < left if parity == 0 else left < right)
                for left, right in zip(digits, digits[1:])
            )
            last = previous % 10
            boundary = last % 2 != parity or (
                digits[0] < last if parity == 0 else last < digits[0]
            )
            if (
                candidate not in used
                and forbidden not in digits
                and internal
                and boundary
            ):
                break
            candidate += 1
        result.append(candidate)
        used.add(candidate)
        previous = candidate
    return result


def predecessor_prefix(count, parity, increasing, positive, seed):
    """Literal rule on the right member of each adjacent digit pair."""
    used = set()
    previous = seed
    result = []
    for _ in range(count):
        candidate = 1 if positive else 0
        while True:
            digits = [int(c) for c in str(candidate)]
            stream = [previous % 10] + digits
            valid = all(
                right % 2 != parity
                or (left < right if increasing else right < left)
                for left, right in zip(stream, stream[1:])
            )
            if candidate not in used and valid:
                break
            candidate += 1
        result.append(candidate)
        used.add(candidate)
        previous = candidate
    return result


def main():
    receipt = {}
    for sequence, parity, forbidden, positive, seed in [
        ("A342043", 0, 0, True, 1),
        ("A342044", 1, 9, False, 0),
    ]:
        published = source_terms(sequence)
        reproduced = greedy_prefix(len(published), parity, forbidden, positive, seed)
        if reproduced != published:
            first = next(i for i, (x, y) in enumerate(zip(reproduced, published)) if x != y)
            raise AssertionError((sequence, first, reproduced[first], published[first]))
        receipt[sequence] = {
            "matched_published_terms": len(published),
            "first_terms": reproduced[:14],
            "scope": "Finite source-fidelity check; not an infinite coverage proof",
        }
    for sequence, parity, increasing, positive, seed in [
        ("A382462", 0, True, True, 1),
        ("A382621", 0, False, True, 9),
        ("A383059", 1, True, False, 0),
    ]:
        published = source_terms(sequence)
        reproduced = predecessor_prefix(len(published), parity, increasing, positive, seed)
        if reproduced != published:
            first = next(i for i, (x, y) in enumerate(zip(reproduced, published)) if x != y)
            raise AssertionError((sequence, first, reproduced[first], published[first]))
        receipt[sequence] = {
            "matched_published_terms": len(published),
            "first_terms": reproduced[:14],
            "scope": "Finite source-fidelity check; not an infinite coverage proof",
        }
    (HERE / "digit_greedy_source_check_receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n"
    )
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
