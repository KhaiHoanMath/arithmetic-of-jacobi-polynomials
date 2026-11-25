"""Check polynomial normalizations, Appendix A's small examples, and Appendix C's margins."""

from fractions import Fraction
from math import comb, gcd, isqrt, lcm, prod
from pathlib import Path

from check_factor_degrees import primitive_coefficients
from check_galois_ranges import PARAMETERS, coefficients, legendre_coefficients


def primitive(poly):
    denominator = lcm(*(x.denominator for x in poly))
    integral = [int(x * denominator) for x in poly]
    content = gcd(*integral)
    return [x // content for x in integral]


def legendre_checks():
    # F_n = 2^n P_n. The three-term recurrence is independent of the closed
    # factorial formula used to construct the Appendix C prime certificates.
    polys = [[1], [0, 2]]
    for n in range(1, 400):
        numerator = [0] + [2*(2*n + 1)*c for c in polys[n]]
        for j, c in enumerate(polys[n-1]):
            numerator[j] -= 4*n*c
        assert all(c % (n+1) == 0 for c in numerator)
        polys.append([c // (n+1) for c in numerator])

    for m in range(1, 200):
        for delta in (0, 1):
            n = 2*m + delta
            derivative = [j*c for j, c in enumerate(polys[n+1])][1:]
            assert all(c == 0 for c in derivative[:delta])
            assert primitive(derivative[delta:]) == primitive_coefficients(m, delta)
            if m <= 25:
                model = polys[n][delta:]
                assert all(c == 0 for c in polys[n][:delta]) and all(c == 0 for c in model[1::2])
                # J_m^epsilon(-X^2) = (-2)^m m! P_n(X)/X^delta.
                square = [(-1)**(m+j)*c for j, c in enumerate(model[::2])]
                assert primitive(square) == legendre_coefficients(2*delta-1, m)
    print('398 derivative models and 50 Legendre quotient models match the three-term recurrence.')


def generalized_binomials(a, n):
    values = [Fraction(1)]
    for j in range(1, n+1):
        values.append(values[-1]*(a-j+1)/j)
    return values


def jacobi_at_one_minus_2t(n, lam, mu):
    # Substitute x=1-2t into the manuscript's defining Jacobi sum (1.1).
    a = generalized_binomials(n + Fraction(lam, 3), n)
    b = generalized_binomials(n + Fraction(mu, 2), n)
    return [(-1)**j * sum(a[n-k]*b[k]*comb(n-k, j-k) for k in range(j+1))
            for j in range(n+1)]


def kaneko_zagier_checks():
    rows = Path(__file__).with_name('kz_small_galois_primes.txt').read_text().splitlines()
    indices = set()
    for line in rows:
        if not line.strip() or line.startswith('#'):
            continue
        e, n, _, _ = map(int, line.split())
        assert (e, n) not in indices
        indices.add((e, n))
        lam, mu = PARAMETERS[e]
        assert e == 6 + 2*lam + 3*mu
        assert primitive(jacobi_at_one_minus_2t(n, lam, mu)) == coefficients(n, lam, mu)
    assert len(indices) == 43
    print('All 43 exceptional Kaneko-Zagier Galois models match the defining Jacobi sum.')


def v3(a):
    assert a > 0
    exponent = 0
    while a % 3 == 0:
        a //= 3
        exponent += 1
    return exponent


def monic_at_2x_minus_one(n, lam, mu):
    f = jacobi_at_one_minus_2t(n, lam, mu)
    # Translate t=1-X and divide by the leading coefficient.
    translated = [(-1)**j * sum(comb(k, j)*f[k] for k in range(j, n+1))
                  for j in range(n+1)]
    return [c / translated[-1] for c in translated]


def lower_newton_polygon(poly):
    hull = []
    for j, c in enumerate(poly):
        if not c:
            continue
        y = v3(abs(c.numerator)) - v3(c.denominator)
        while len(hull) >= 2:
            (i, u), (k, v) = hull[-2:]
            if (v-u)*(j-k) < (y-v)*(k-i):
                break
            hull.pop()
        hull.append((j, y))
    return hull


def appendix_a_checks():
    q = Fraction
    assert monic_at_2x_minus_one(3, 1, 1) == [-q(81, 1189), q(27, 41), -q(63, 41), 1]
    vertices = {5: [(0, 8), (1, 6), (4, 1), (5, 0)], 15: [(0, 23), (13, 3), (15, 0)]}
    for n, expected in vertices.items():
        for lam in (-1, 1):
            hull = lower_newton_polygon(monic_at_2x_minus_one(n, lam, 1))
            assert hull == expected
            assert all(gcd(k-i, abs(v-u)) == 1 for (i, u), (k, v) in zip(hull, hull[1:]))
    print('Appendix A cubic and both exceptional Newton polygons verified for the stated signs.')


def primes_through(limit):
    return [p for p in range(2, limit+1) if all(p % k for k in range(2, isqrt(p)+1))]


def legendre_small_degrees():
    primes = primes_through(203)
    residual = [n for n in range(2, 200) if not any(p-4 <= n <= p+3 for p in primes if p != 2)]
    assert residual == [117, 118, 119, 120, 121, 122, 143, 144, 185, 186]
    for n in residual:
        m = n // 2
        # Each prime contributes its highest power at most 2n+1.
        powers = []
        for p in primes:
            if p > m:
                break
            power = p
            while power*p <= 2*n+1:
                power *= p
            powers.append(power)
        assert 16**m > 64*m*prod(powers)**2
    print('The ten remaining degrees in the order-zero Legendre comparison pass its integer test.')


def logarithm_checks():
    q = Fraction

    def lower(z):
        return 2*sum(z**(2*j+1)/(2*j+1) for j in range(5))

    def upper(z):
        return lower(z) + 2*z**11/(11*(1-z*z))

    a = 13*lower(q(1, 3)) + 9*lower(q(1, 17)) - 34*upper(q(1, 33)) - 8
    b = 3*lower(q(1, 3)) + 8*lower(q(1, 5)) + 57*lower(q(3, 35)) + 92*lower(q(1, 47)) - 19
    assert a > q(97, 10000) and b > q(42, 1250)
    assert 3**5 * 2**16 > 5**10
    print('Appendix C rational logarithmic bounds and final integer comparison verified.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that every identity is checked.')
    legendre_checks()
    kaneko_zagier_checks()
    appendix_a_checks()
    legendre_small_degrees()
    logarithm_checks()
