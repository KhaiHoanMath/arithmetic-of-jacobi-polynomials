"""Regenerate the eleven residual derivative certificates. Requires python-flint.

Use --check to compare the generated Lean files with the committed copies.
Use --output-dir to write the same files to a separate directory.
"""

import argparse
from math import factorial, gcd, isqrt
from pathlib import Path

from flint import nmod_poly

from check_factor_degrees import primitive_coefficients, read_witnesses


DIRECTORY = Path(__file__).resolve().parents[1] / "ArithmeticOfJacobiPolynomials/Verification/Rabin"
CASES = {0: (11, 23, 46), 1: (17, 22, 25, 32, 38, 43, 45, 47)}


def certificate(delta, m, p):
    """Compute a Frobenius table and the additive and multiplicative witnesses."""
    degree = 2*m
    n = degree + delta
    coeffs = primitive_coefficients(m, delta)
    scale = gcd(*(
        factorial(2*n + 2 - 2*k) //
        (factorial(k) * factorial(n + 1 - k) * factorial(n - 2*k))
        for k in range(m + 1)
    ))
    modulus = nmod_poly(coeffs, p) * pow(coeffs[-1], -1, p)
    x = nmod_poly([0, 1], p)
    one = x**0

    def pack(poly):
        # The highest coefficient is the first digit in the fixed-width Lean list.
        return sum(int(poly[i]) * p**(degree-1-i) for i in range(len(poly)))

    relation = pack(x**degree - modulus)
    exponents = [1]
    powers = [x]
    operations = []

    def product(i, j):
        operations.append((i, j))
        exponents.append(exponents[i] + exponents[j])
        powers.append(powers[i] * powers[j] % modulus)

    for bit in bin(p)[3:]:
        last = len(powers) - 1
        product(last, last)
        if bit == "1":
            product(len(powers)-1, 0)
    xp = powers[-1]
    assert exponents[-1] == p and xp == pow(x, p, modulus)

    # Applying Frobenius to a coefficient vector is linear over the prime field.
    table = [one]
    for _ in range(1, degree):
        table.append(table[-1] * xp % modulus)
    trace = [x]
    for _ in range(degree):
        trace.append(pow(trace[-1], p, modulus))
    assert trace[-1] == x

    inverses = []
    for q in range(2, degree + 1):
        if degree % q or any(q % k == 0 for k in range(2, isqrt(q) + 1)):
            continue
        g, inv, _ = (trace[degree//q] - x).xgcd(modulus)
        assert g == one
        inverses.append((q, pack(inv % modulus)))

    def entries(values):
        return "[\n    " + ",\n    ".join(map(str, values)) + "]"

    return {
        "m": m, "δ": delta, "p": p, "scale": scale,
        "coeffs": entries(coeffs), "relation": relation, "exponents": exponents,
        "operations": operations, "powers": entries(map(pack, powers)),
        "table": entries(map(pack, reversed(table))), "trace": entries(map(pack, trace)),
        "inverses": entries(inverses),
    }


def fast_certificate(delta, m, p):
    """Give polynomial quotients and carries for evaluation in base 2^48.

    All coefficient vectors below are in ascending order, as expected by FLINT.
    The integer bound in Lean proves uniqueness of the resulting base expansion.
    """
    d = 2*m
    coeffs = primitive_coefficients(m, delta)
    modulus = nmod_poly(coeffs, p) * pow(coeffs[-1], -1, p)
    x = nmod_poly([0, 1], p)
    xp = pow(x, p, modulus)
    def to_list(poly):
        return [int(poly[i]) for i in range(d)]
    f = to_list(x**d - modulus)
    table = [x**0]
    for _ in range(1, d):
        table.append(table[-1] * xp % modulus)
    table.reverse()

    def pack_reverse(values, width, base):
        assert len(values) <= width and all(0 <= a < base for a in values)
        return sum(a * base**(width - 1 - i) for i, a in enumerate(values))

    def convolution(a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, u in enumerate(a):
            if u:
                for j, v in enumerate(b):
                    out[i+j] += u*v
        return out

    positive, negative, quotients = [], [], []
    carry_base = 4*(d+1)*p + 1
    for out, v in zip(table, table[1:]):
        q, r = divmod(xp * v, modulus)
        assert r == out
        q = to_list(q)
        lhs = convolution(to_list(xp), to_list(v)) + [0]
        qf = convolution(q, f) + [0]
        rhs = to_list(out) + q
        diff = [a+b-c for a, b, c in zip(lhs, qf, rhs)]
        assert all(v % p == 0 for v in diff)
        quotients.append(pack_reverse(q, d, p))
        positive.append(pack_reverse([max(-v//p, 0) for v in diff], 2*d, carry_base))
        negative.append(pack_reverse([max(v//p, 0) for v in diff], 2*d, carry_base))

    rows = [to_list(t) for t in table]
    packed = [sum(a * (2**48)**i for i, a in enumerate(v)) for v in rows]
    sums = [sum(v) for v in rows]
    carries = []
    r = x
    for _ in range(d):
        nxt = pow(r, p, modulus)
        u = to_list(r)[::-1]
        c = to_list(nxt)
        diff = [sum(a * row[j] for a, row in zip(u, rows)) - c[j] for j in range(d)]
        assert all(v >= 0 and v % p == 0 for v in diff)
        carries.append(pack_reverse([v//p for v in diff], d, carry_base))
        r = nxt
    return {"quotients": quotients, "positive": positive, "negative": negative,
            "packed": packed, "sums": sums, "carries": carries}


def render(delta, m, p):
    name = f"case{delta}_{m}"
    record = "\n".join(f"  {k} := {v}" for k, v in certificate(delta, m, p).items())
    imports = ["RabinData", "RabinConditions"]
    extras = ""
    arguments = ""
    condition = "Conditions"
    if m >= 32:
        imports = ["FastRabinData", "RabinFastConditions"]
        fast = name + "Fast"
        fields = []
        for k, values in fast_certificate(delta, m, p).items():
            # Digits encode nonnegative integer coefficients in fixed-width rows.
            rows = ",\n    ".join(map(str, values))
            fields.append(f"  {k} := [\n    {rows}]")
        extras = (f"@[expose] def {fast} : FastRabinData where\n"
                  + "\n".join(fields) + "\n\n")
        condition = "FastConditions"
        arguments = (f"\n    ({fast}.qAt {name}) ({fast}.plusAt {name}) ({fast}.minusAt {name})"
                     f"\n    {fast}.packed {fast}.sums ({fast}.carryAt {name})")
    imports = "\n".join("public import ArithmeticOfJacobiPolynomials.Verification." + i for i in imports)
    return f"""module

{imports}

/-! # Frobenius certificate for the exceptional derivative index ({delta}, {m}) -/

-- Packed integers are recorded in full so the kernel can check their digits.
set_option linter.style.longLine false

public section
namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

@[expose] def {name} : RabinData where
{record}

{extras}set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel checks every coefficient, table product, trace entry, and inverse.
theorem {name}Checked : {condition} {name}.m {name}.δ {name}.p {name}.scale {name}.coeffs {name}.f {name}.xp
    {name}.tabs {name}.row {name}.inv {name}.chainAt {name}.expAt {name}.opAt {name}.operations.length{arguments} := by
  constructor <;> decide +kernel

end ArithmeticOfJacobiPolynomials.ModularArithmetic
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare without writing files")
    parser.add_argument("--output-dir", type=Path, default=DIRECTORY)
    args = parser.parse_args()
    primes = read_witnesses()
    for delta, indices in CASES.items():
        for m in indices:
            path = args.output_dir / f"Case{delta}_{m}.lean"
            data = render(delta, m, primes[delta, m][0]).encode()
            if args.check:
                if not path.exists() or path.read_bytes() != data:
                    raise SystemExit(f"Certificate differs: {path}")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
    print(f"{'Matched' if args.check else 'Wrote'} all eleven derivative certificates.")


if __name__ == "__main__":
    main()
