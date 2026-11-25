"""Independent integer verification of the two inequalities in Appendix B.

Run with Python 3.10 or later. No data files, third-party packages or other
verification scripts are used. All reported decimal bounds are rounded outwards.
"""

from array import array
from bisect import bisect_right
from fractions import Fraction
from functools import cache
from itertools import accumulate
from math import isqrt

FIRST, CUTOFF, LAST = 1810, 8333, 250_000
LOG_BITS = 32
LOG_SCALE = 1 << LOG_BITS


@cache
def binary_log(p):
    """Adjacent integer bounds for LOG_SCALE * log_2(p), by repeated squaring."""
    exponent = p.bit_length() - 1
    if p == 1 << exponent:
        return exponent*LOG_SCALE, exponent*LOG_SCALE
    precision = max(96, exponent)
    while True:
        unit = 1 << precision
        # [low/unit, high/unit] encloses the normalized mantissa in [1,2).
        low = high = p << (precision-exponent)
        digits = exponent
        for _ in range(LOG_BITS):
            low = low*low // unit
            high = -(-high*high // unit)
            digits *= 2
            if low >= 2*unit:
                low //= 2
                high = (high+1) // 2
                digits += 1
            elif high >= 2*unit:
                # Insufficient precision to decide this bit. An exact tie
                # would force p to be a power of two, already treated above.
                break
        else:
            return digits, digits+1
        precision *= 2


def natural_log_two():
    # Integrate 2/(1-t^2) from 0 to 1/3, using the geometric series.
    terms = 16
    partial = sum(Fraction(2, (2*j + 1)*3**(2*j + 1)) for j in range(terms))
    tail = Fraction(2, (2*terms + 1)*3**(2*terms + 1)) * Fraction(9, 8)
    denominator = 10**12
    lower = partial * denominator
    upper = (partial + tail) * denominator
    return lower.numerator // lower.denominator, -(-upper.numerator // upper.denominator), denominator


def least_prime_factors(limit):
    # A zero entry for k >= 2 means k is prime.
    least = array('I', [0]) * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if least[p] == 0:
            for multiple in range(p*p, limit + 1, p):
                if least[multiple] == 0:
                    least[multiple] = p
    return least


def add_prime_factors(primes, k, least):
    while k > 1:
        p = least[k] or k
        if p >= 5:
            primes.add(p)
        while k % p == 0:
            k //= p


def first_level_weight(n, p, a, b):
    """Coefficient of log p in T_0(n), from the indicators in Lemma 4.2."""
    carry, c = divmod(a+b, p)
    residue = n % p
    ea = residue + a >= p
    eb = residue + b >= p
    ec = residue + c >= p
    m = int(ea and eb and carry + ec == 1)
    if p > n:
        return m
    # eta + b* = 1 when c = p-1, and 1-carry otherwise.
    return ea + eb - ec + 1 - (carry if c != p-1 else 0) - m


def first_level_increment(n, lam, mu, least):
    # At n, the residue n mod p can wrap, or cross p-a, p-b or p-c.
    # The factor n also includes p = n, where the summation rule changes.
    # As 3a = lambda, 2b = mu, and 6c = 2lambda+3mu modulo p, it suffices
    # to factor the following four integers. The initial T_0(0) is zero.
    primes = set()
    for k in (n, 3*n+lam, 2*n+mu, 6*n+2*lam+3*mu):
        add_prime_factors(primes, k, least)
    change = 0
    for p in primes:
        if p > 2*n+1:
            # Both weights vanish: even the indicator n+b >= p is false.
            continue
        # Since p^2 = 1 modulo 3, this gives 0 <= a < p and 3a = lam modulo p.
        a = (lam + (-lam*p % 3)*p) // 3
        b = (p + mu) // 2
        jump = first_level_weight(n, p, a, b) - first_level_weight(n-1, p, a, b)
        if jump:
            # This updates the sum of weights times fixed upper log bounds.
            # A negative jump removes exactly the same upper bound it added.
            change += jump * binary_log(p)[1]
    return change


def prime_power_bounds(least):
    # Independent ordered list of all p^h, h >= 2, that can occur in Q.
    maximum = 12*LAST + 5
    powers = []
    for p in range(5, isqrt(maximum) + 1):
        if least[p] == 0:
            power = p*p
            while power <= maximum:
                powers.append((power, binary_log(p)[1]))
                power *= p
    powers.sort()
    return [k for k, _ in powers], list(accumulate((u for _, u in powers), initial=0))


def endpoint_progressions(p, coeff, shift):
    # p^h divides coeff*j+shift in a single nonzero class modulo p^h.
    conditions = []
    power = p
    while power <= coeff*LAST + shift:
        first = (-shift * pow(coeff, -1, power)) % power
        conditions.append((power, first))
        power *= p
    return conditions


def endpoint(n, progressions):
    return n + sum(1 + (n-j)//modulus for modulus, j in progressions)


def factorial_valuation(n, p):
    val = 0
    while n:
        n //= p
        val += n
    return val


def verify_pair(lam, mu, least, powers, prefix):
    lo2, hi2, units = natural_log_two()
    root3, top3 = binary_log(3)
    top7 = binary_log(7)[1]
    twos = endpoint_progressions(2, 3, lam)
    threes = endpoint_progressions(3, 2, mu)
    first_level = 0
    results = []
    for n in range(1, LAST + 1):
        first_level += first_level_increment(n, lam, mu, least)
        if n < FIRST:
            continue
        if n == FIRST or n == CUTOFF:
            results.append({'begin': n, 'end': n, 'delta': None, 'gap': None})

        d2 = endpoint(n, twos)
        d3 = endpoint(n, threes)
        v2 = factorial_valuation(n, 2)
        v3 = factorial_valuation(n, 3)
        arg = 2*n + (mu+1)//2
        # Legendre's formula yields s_p(a) = a - (p-1)*v_p(a!).
        c2 = 216*n + 48*v2 - 24*(n-v2) - 27*d2 - 192
        c3 = 48*v3 - 22*n - 21*d3 - 8*(arg-2*factorial_valuation(arg, 3))
        higher = prefix[bisect_right(powers, 12*n+5)]
        lower = (c2*LOG_SCALE + min(c3*root3, c3*top3) - 21*n*top7
                 - 48*(first_level + 3*higher))
        upper = max(d2*LOG_SCALE - d3*root3, d3*top3 - d2*LOG_SCALE)
        # lower bounds 48*LOG_SCALE*Delta/log(2), upper bounds LOG_SCALE*gap/log(2).
        if 1000*lower*lo2 <= 48*LOG_SCALE*n*units or 10*upper*hi2 > 9*LOG_SCALE*n*units:
            raise ArithmeticError(f'Failed at lambda={lam}, mu={mu}, n={n}')

        row = results[-1]
        row['end'] = n
        if row['delta'] is None or lower*row['delta'][1] < row['delta'][0]*n:
            row['delta'] = (lower, n)
        if row['gap'] is None or upper*row['gap'][1] > row['gap'][0]*n:
            row['gap'] = (upper, n)

    for row in results:
        lower, n_min = row['delta']
        upper, n_max = row['gap']
        delta = 10**6 * lower*lo2 // (48*LOG_SCALE*n_min*units)
        gap = -(-10**6 * upper*hi2 // (LOG_SCALE*n_max*units))
        print(f"lambda={lam:+}, mu={mu:+}, n={row['begin']}..{row['end']}: "
              f"Delta/n >= {delta}/1000000; endpoint gap/n <= {gap}/1000000", flush=True)


def main():
    least = least_prime_factors(6*LAST + 5)
    powers, prefix = prime_power_bounds(least)
    for lam in (-1, 1):
        for mu in (-1, 1):
            verify_pair(lam, mu, least, powers, prefix)
    print(f'Both inequalities hold for {4*(CUTOFF-FIRST):,} parameter-degree pairs '
          f'below {CUTOFF:,} and all {4*(LAST-CUTOFF+1):,} pairs in Proposition B.2.')


if __name__ == '__main__':
    main()
