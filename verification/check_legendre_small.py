"""Independently check reduced Legendre irreducibility in the 198 degrees 2–199.

Use the paper's exact comparison at derivative order zero whenever it applies.
For each remaining polynomial, check an irreducible reduction by the Frobenius test.
"""

from math import comb, gcd, isqrt, prod

from check_factor_degrees import check_irreducible


# m: primes for P_(2m) and P_(2m+1)/X, respectively
WITNESSES = {
    1: (5, 13), 2: (11, 19), 3: (23, 67), 4: (29, 31),
    5: (37, 97), 6: (41, 61), 7: (109, 41), 8: (71, 67),
    9: (67, 101), 10: (43, 197), 11: (53, 103), 12: (271, 113),
    13: (83, 61), 14: (463, 311), 15: (149, 359), 16: (761, 197),
    17: (397, 167), 18: (107, 467), 19: (131, 137), 20: (349, 307),
    21: (167, 97), 23: (409, 863), 31: (653, 997), 32: (449, 179),
}


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def prime_power(p, limit):
    q = p
    while q*p <= limit:
        q *= p
    return q


def reduced_legendre(m, delta):
    # Rodrigues' formula for 2^n P_n(X)/X^delta, followed by primitive normalization.
    n = 2*m + delta
    coefficients = [0] * (2*m + 1)
    for k in range(m + 1):
        coefficients[2*(m-k)] = (-1)**k * comb(2*n-2*k, n-k) * comb(n-k, k)
    content = gcd(*coefficients)
    return [c // content for c in coefficients]


def main():
    certified = set()
    comparisons = 0
    for m in range(1, 100):
        for delta in (0, 1):
            n = 2*m + delta
            z = prod(prime_power(p, 2*n + 1) for p in range(2, m+1) if is_prime(p))
            if m >= 4 and 16**m > 64*m*z*z:
                comparisons += 1
                continue
            p = WITNESSES[m][delta]
            assert is_prime(p)
            check_irreducible(reduced_legendre(m, delta), p)
            certified.add((m, delta))

    assert certified == {(m, delta) for m in WITNESSES for delta in (0, 1)}
    assert comparisons == 150 and len(certified) == 48
    print('Verified 198 small Legendre cases: 150 exact inequalities and '
          '48 irreducible reductions (largest prime 997).')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that every identity is checked.')
    main()
