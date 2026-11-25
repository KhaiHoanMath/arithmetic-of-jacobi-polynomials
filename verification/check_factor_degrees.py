"""Check the 80 prime lists of Lemma C.2 by Frobenius and gcd, using only Python."""

from math import comb, gcd, isqrt
from pathlib import Path


def primitive_coefficients(m, delta):
    n = 2*m + delta
    coefficients = [0] * (2*m + 1)
    for k in range(m + 1):
        j = n + 1 - k
        coefficients[2*(m-k)] = (-1)**k * (j-k) * comb(2*j, j) * comb(j, k)
    content = gcd(*coefficients)
    return [c // content for c in coefficients]


# Polynomial coefficients are listed in ascending order. The empty list represents zero.
def trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def monic(f, p):
    if not f:
        return []
    inverse = pow(f[-1], -1, p)
    return [a*inverse % p for a in f]


def divide(f, g, p):
    """Euclidean division by a monic polynomial over F_p."""
    assert g and g[-1] == 1
    r = f.copy()
    q = [0] * max(0, len(f) - len(g) + 1)
    while len(r) >= len(g):
        shift = len(r) - len(g)
        c = r[-1]
        q[shift] = c
        for j, a in enumerate(g):
            r[shift+j] = (r[shift+j] - c*a) % p
        trim(r)
    return q, r


def polynomial_gcd(f, g, p):
    while g:
        g = monic(g, p)
        f, g = g, divide(f, g, p)[1]
    return monic(f, p)


def multiply_mod(f, g, modulus, p):
    if not f or not g:
        return []
    h = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            h[i+j] += a*b
    return divide(trim([v % p for v in h]), modulus, p)[1]


def power_mod(f, e, modulus, p):
    result = [1]
    while e:
        if e % 2:
            result = multiply_mod(result, f, modulus, p)
        e //= 2
        if e:
            f = multiply_mod(f, f, modulus, p)
    return result


def factor_degrees(coefficients, p):
    f = monic(trim([a % p for a in coefficients]), p)
    assert len(f) == len(coefficients)
    derivative = trim([i*f[i] % p for i in range(1, len(f))])
    assert polynomial_gcd(f, derivative, p) == [1]

    degrees = []
    d = 1
    frobenius = [0, 1]
    while 2*d <= len(f)-1:
        # All factors of degrees less than d have already been removed.
        # gcd(f, X^(p^d)-X) is exactly the product of the degree-d factors.
        frobenius = power_mod(frobenius, p, f, p)
        difference = frobenius + [0] * max(0, 2 - len(frobenius))
        difference[1] = (difference[1] - 1) % p
        block = polynomial_gcd(f, trim(difference), p)
        count, rem = divmod(len(block)-1, d)
        assert rem == 0
        if count:
            degrees.extend([d] * count)
            f, remainder = divide(f, block, p)
            assert not remainder
            frobenius = divide(frobenius, f, p)[1]
        d += 1
    # The remaining degree is less than 2d and each remaining factor has degree at least d.
    if len(f) > 1:
        degrees.append(len(f)-1)
    assert sum(degrees) == len(coefficients)-1
    return degrees


def check_irreducible(coefficients, p):
    """Rabin's test, in the form used by irreducible_of_frobenius_reduction."""
    f = monic(trim([a % p for a in coefficients]), p)
    degree = len(coefficients) - 1
    assert len(f) == degree + 1 and degree >= 2
    divisors = {q for q in range(2, degree + 1)
                if degree % q == 0 and all(q % k for k in range(2, isqrt(q) + 1))}
    tests = {degree // q for q in divisors}
    x = [0, 1]
    residue = x
    for i in range(1, degree + 1):
        residue = power_mod(residue, p, f, p)
        if i in tests:
            difference = residue + [0] * max(0, 2 - len(residue))
            difference[1] = (difference[1] - 1) % p
            assert polynomial_gcd(f, trim(difference), p) == [1]
    assert residue == x


def read_witnesses():
    witnesses = {}
    path = Path(__file__).with_name('appendix_c_primes.txt')
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        delta, m, witness, *primes = map(int, line.split())
        assert (delta, m) not in witnesses and primes == sorted(set(primes))
        witnesses[delta, m] = witness, primes
    return witnesses


def main():
    # These are exactly E_0 and E_1 in Appendix C.
    exceptions = (
        set(range(1, 26)) | {28, 30, 31, 32, 34, 37, 40, 42, 43, 45, 46, 47},
        set(range(1, 27)) | {29, 31, 32, 33, 34, 35, 37, 38, 41, 43, 44,
                              45, 47, 49, 50, 53, 73},
    )
    witnesses = read_witnesses()
    assert set(witnesses) == {(delta, m) for delta in (0, 1) for m in exceptions[delta]}
    used = []
    for (delta, m), (witness, primes) in witnesses.items():
        coefficients = primitive_coefficients(m, delta)
        assert 2 <= witness <= 2311 and all(witness % k for k in range(2, isqrt(witness) + 1))
        check_irreducible(coefficients, witness)
        candidates = set(range(1, m + 1))
        for p in primes:
            assert 2 <= p <= 317 and all(p % k for k in range(2, isqrt(p) + 1))
            sums = {0}
            for d in factor_degrees(coefficients, p):
                sums |= {s + d for s in sums}
            candidates.intersection_update(sums)
            used.append(p)
        assert not candidates, (delta, m, candidates)
    assert (len(witnesses), len(used), max(used)) == (80, 254, 317)
    largest_witness = max(witness for witness, _ in witnesses.values())
    print(f'Verified {len(used)} reductions (largest prime {max(used)}) and one irreducible '
          f'reduction for each of the {len(witnesses)} polynomials (largest prime {largest_witness}).')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that every identity is checked.')
    main()
