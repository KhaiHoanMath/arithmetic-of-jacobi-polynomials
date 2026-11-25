"""Recheck the finite Galois inputs used for both polynomial families, given irreducibility."""

from bisect import bisect_right
from fractions import Fraction
from math import comb, gcd, isqrt, lcm, prod
from pathlib import Path

from check_factor_degrees import factor_degrees

PARAMETERS = {1: (-1, -1), 5: (1, -1), 7: (-1, 1), 11: (1, 1)}
MAX_DEGREE = 10**6 - 1


def sieve(limit):
    prime = bytearray([1]) * (limit + 1)
    prime[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            prime[p*p::p] = bytes((limit-p*p)//p + 1)
    return prime


def coefficients(n, sign_lambda, sign_mu):
    # Divide P_n^(lambda/3,mu/2)(1-2t) by its nonzero constant term.
    # The consecutive coefficient ratio follows from the terminating 2F1 series.
    c = [Fraction(1)]
    for j in range(n):
        numerator = (j-n) * (6*(n+j+1) + 2*sign_lambda + 3*sign_mu)
        denominator = 2 * (3*(j+1) + sign_lambda) * (j+1)
        c.append(c[-1] * Fraction(numerator, denominator))
    common = lcm(*(a.denominator for a in c))
    integral = [int(a*common) for a in c]
    content = gcd(*integral)
    return [a // content for a in integral]


def check_small_cases(filename, expected, coefficients_for, prime):
    rows = {}
    for line in Path(__file__).with_name(filename).read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        e, n, p, q = map(int, line.split())
        assert (e, n) not in rows and min(p, q) >= 2 and prime[p] and prime[q]
        rows[e, n] = p, q
    assert set(rows) == expected
    for (e, n), (p, q) in rows.items():
        c = coefficients_for(e, n)
        # Frobenius at p fixes one root and cycles the rest. At q an odd power
        # of Frobenius is a transposition. factor_degrees also checks squarefreeness.
        assert sorted(factor_degrees(c, p)) == [1, n-1]
        assert [d for d in factor_degrees(c, q) if d % 2 == 0] == [2]


def legendre_coefficients(e, n):
    c = [comb(n, j) * prod(2*j + 2*k + e for k in range(1, n+1)) for j in range(n+1)]
    content = gcd(*c)
    return [a // content for a in c]


def main():
    prime = sieve(12*MAX_DEGREE + max(PARAMETERS))
    primes = [p for p in range(MAX_DEGREE+1) if prime[p]]
    exceptions = set()
    for n in range(1, MAX_DEGREE+1):
        start = bisect_right(primes, n//2)
        for e in PARAMETERS:
            modular_index = 12*n + e
            i = start
            while primes[i] < n-2:
                if prime[modular_index - 6*primes[i]]:
                    break
                i += 1
            else:
                exceptions.add((e, n))
    # Cullinan-Hajir, Theorem 1.6, applies to every pair that passed the sieve.
    # Degrees one and two have symmetric group immediately under irreducibility.
    linear_quadratic = {(e, n) for e in PARAMETERS for n in (1, 2)}
    assert linear_quadratic <= exceptions
    remaining = exceptions - linear_quadratic
    check_small_cases('kz_small_galois_primes.txt', remaining,
                      lambda e, n: coefficients(n, *PARAMETERS[e]), prime)
    assert (len(exceptions), len(remaining)) == (51, 43)
    print(f'Kaneko–Zagier: {4*MAX_DEGREE-len(exceptions):,} prime-pair cases, '
          f'{len(linear_quadratic)} linear or quadratic cases, and {len(remaining)} Frobenius cases.')

    legendre_small = {(e, n) for e in (-1, 1) for n in range(3, 26)}
    check_small_cases('legendre_small_galois_primes.txt', legendre_small, legendre_coefficients, prime)
    print('Legendre: 46 Frobenius cases in degrees 3–25; degrees 1 and 2 follow from irreducibility.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that every identity is checked.')
    main()
