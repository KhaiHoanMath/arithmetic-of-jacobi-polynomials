"""Verify the 80 exceptional derivatives using Newton polygons and two rational-root tests.

The polynomial coefficients are in ascending order. All calculations use integers.
"""

from math import gcd, isqrt

from check_factor_degrees import primitive_coefficients, read_witnesses


def valuation(a, p):
    """The p-adic valuation of a nonzero integer."""
    assert a
    v = 0
    while a % p == 0:
        a //= p
        v += 1
    return v


def newton_degrees(coefficients, p):
    """Degrees permitted by Dumas's product rule at p."""
    assert coefficients[0] and coefficients[-1]
    vertices = []
    for i, c in enumerate(coefficients):
        if not c:
            continue
        v = valuation(c, p)
        while len(vertices) >= 2:
            j, u = vertices[-2]
            k, w = vertices[-1]
            if (w - u) * (i - k) < (v - w) * (k - j):
                break
            vertices.pop()
        vertices.append((i, v))

    degrees = 1  # Bit j corresponds to a possible factor of degree j.
    for (i, u), (j, v) in zip(vertices, vertices[1:]):
        count = gcd(j - i, abs(v - u))
        step = (j - i) // count
        for _ in range(count):
            degrees |= degrees << step
    return degrees


def translate_by_one(coefficients):
    """Horner substitution of X+1 for X."""
    result = []
    for c in reversed(coefficients):
        result = [a+b for a, b in zip(result + [0], [c] + result)]
    return result


def value_mod(coefficients, x, p):
    y = 0
    for c in reversed(coefficients):
        y = (y*x + c) % p
    return y


def main():
    indices = set(read_witnesses())
    assert len(indices) == 80
    primes = [p for p in range(2, 152) if all(p % d for d in range(2, isqrt(p)+1))]
    translated = set()
    remaining = {}
    for delta, m in sorted(indices):
        coefficients = primitive_coefficients(m, delta)
        degrees = (1 << (m+1)) - 2  # A smaller proper factor has degree 1,...,m.
        for p in primes:
            degrees &= newton_degrees(coefficients, p)
            if not degrees:
                break
        if degrees:
            degrees &= newton_degrees(translate_by_one(coefficients), 2)
            if not degrees:
                translated.add((delta, m))
        if degrees:
            remaining[delta, m] = {d for d in range(1, m+1) if (degrees >> d) & 1}

    assert translated == {(1, 32)}
    assert remaining == {(1, 25): {2}, (1, 43): {2}}
    for m, p in ((25, 13), (43, 193)):
        coefficients = primitive_coefficients(m, 1)
        # H(X)=G(X^2). A monic irreducible quadratic and its reflection
        # would give a quartic factor unless the quadratic is even.
        assert all(c == 0 for c in coefficients[1::2])
        g = coefficients[::2]
        assert all(p % d for d in range(2, isqrt(p)+1)) and g[-1] % p
        assert all(value_mod(g, x, p) != 0 for x in range(p))
    print('77 cases by unshifted Newton polygons, one more after X -> X+1, '
          'and two by rational-root tests modulo 13 and 193.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that all certificates are checked.')
    main()
