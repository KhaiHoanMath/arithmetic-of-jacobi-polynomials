"""Check the numerical constants in Section 5.2 and Appendix B.1 by rational arithmetic."""

from fractions import Fraction as F
from math import gcd

from check_appendix_b_independent import binary_log, LOG_SCALE, natural_log_two


def log_bounds(x):
    """Rational bounds for the natural logarithm of a rational x >= 1."""
    x = F(x)
    assert x >= 1
    a, b = binary_log(x.numerator)
    c, d = binary_log(x.denominator)
    low, high, unit = natural_log_two()
    return F(max(0, a-d)*low, LOG_SCALE*unit), F((b-c)*high, LOG_SCALE*unit)


def section_five():
    n = 10**6
    low, high = F(69, 5), F(691, 50)
    assert low < log_bounds(n)[0] <= log_bounds(n)[1] < high
    assert log_bounds(9)[1] < F(11, 5) and log_bounds(2)[1] < F(7, 10)
    assert F(158, 5)**4 < n

    def phi(k):
        return sum(gcd(i, k) == 1 for i in range(1, k+1))

    for D in (2, 6):
        c = F(D, 2*phi(D))
        # Subtracting the two BMOR endpoint errors costs at most 0.0675*D*n/L^2.
        assert F(27, 1000)*F(5, 2) == F(675, 10000)
        assert F(675, 10000)*D/c <= F(27, 100) and 10*D/c <= 40
        for b in (2, 3):
            assert F(D, 2*phi(D*b)) >= F(1, 2)
            assert F(675, 10000)*D <= F(405, 1000)
            assert phi(D*b) in (2*phi(D), 3*phi(D)) and D*b <= 18

    main = low/(low+F(11, 5)) - F(27, 100)/low - 40*high/n
    lifts = low/(2*(low+F(11, 5))) - F(405, 1000)/low - 60*high/n
    middle = low/(2*(3*low/4-F(7, 10)))
    large = high/(2*F(158, 5)) + high/n
    assert main == F(69, 80)-F(9, 460)-F(691, 1250000) > F(21, 25)
    assert lifts == F(69, 160)-F(27, 920)-F(2073, 2500000) > F(2, 5)
    assert middle == F(138, 193) < F(3, 4)
    assert large == F(691, 3160)+F(691, 50000000) < F(1, 4)
    # log(n)/n and log(n)/n^(1/4) decrease from this endpoint.
    assert low > 4


def endpoints(n, lam, mu):
    r = 2*lam+3*mu
    tails = [(F(n), F(3*n+lam, 2)), (F(6*n+r, 5), F(2*n+mu))]
    groups = []
    for i in range(1, 7):
        groups.append([(F(6*n+r, 6*i+1), F(n, i)), (F(n, i+1), F(2*n+mu, 2*i+1)),
                       (F(n, i+1), F(3*n+lam, 3*i+1))])
    return tails, groups


def interval_margins(n, lam, mu):
    # Every expression below is affine in n. A nonnegative value and slope
    # at N prove that it is nonnegative throughout the half-line n >= N.
    tails, groups = endpoints(n, lam, mu)
    bounds = [(tails, 2*n+1), *((g, F(n+1, i)) for i, g in enumerate(groups, 1))]
    for intervals, upper in bounds:
        for a, b in intervals:
            yield a-F(n, 7)
            yield b-a
            yield upper-b


def half_length(n, lam, mu):
    tails, groups = endpoints(n, lam, mu)
    return sum(b-a for rows in [tails, *groups] for a,b in rows)/2


def appendix_b():
    N = 250_000
    big = 10**13
    log2, log3 = log_bounds(2), log_bounds(3)
    assert F(69, 100) < log2[0] and log2[1] < F(7, 10)
    assert F(549, 500) < log3[0] and log3[1] < F(11, 10)
    assert log_bounds(9*N)[1] < 15 and log_bounds(9*N)[0] > 1
    assert F(3, 2)*F(11, 10)-2*F(69, 100) == F(27, 100)
    assert F(27, 100)+F(30, N) < F(3, 10)
    energy = log2[0]/2 + log3[0]/3
    assert energy-F(3, 10)**2/4 > F(1, 2)
    assert energy-F(9, 10)**2/4 > F(1, 2)  # Also used in Appendix B.2.
    # At n=2, exponentiate six times the difference after (B.1).
    assert 24**36 > 15**8 * 7**6 * 6**12 * 4**3 * 3**3 * 2**24
    assert 6-F(4, 3)-1-2-F(1, 2) == F(7, 6)  # Lower derivative coefficient.

    harmonic = sum(F(1, i) for i in range(1, 7))
    assert harmonic == F(49, 20)
    q6 = F(180556377763, 157066509600)
    assert q6 < F(23, 20)
    shift = F(5, 4)+F(5, 6)*harmonic
    assert shift < 5 and 5+log_bounds(385)[1] < 12
    for lam in (-1, 1):
        for mu in (-1, 1):
            margins = list(interval_margins(N, lam, mu))
            next_margins = interval_margins(N+1, lam, mu)
            assert all(y >= x >= 0 for x, y in zip(margins, next_margins))
            length = half_length(N, lam, mu)
            assert half_length(N+1, lam, mu)-length == q6
            assert length - N*q6 <= shift

    assert 2*big+1 < 4*big and big//7 >= 10**6
    assert 6 < ((F(39, 10)+1)/2)**2            # 2*sqrt(6)-1 < 3.9.
    assert 1+F(1, N) < F('1.000002')**2 and 2+F(1, N) < F('1.415')**2
    assert F('2.072')*(6*F('1.000002')*F('3.9')+4*F('1.415')) < 61
    assert 6*(1+F(1, big))*harmonic + 4*(2+F(1, big)) < 23
    assert log_bounds(F(big, 7))[0] > 27 and F('0.024')*23/27 < F(21, 1000)

    K = F('12.1')
    assert 12+F(5, N) <= K < F('3.5')**2 and K < F('2.3')**3
    assert 1 < N*F('0.127')**6
    assert 6 < log_bounds(K*N)[0] <= log_bounds(K*N)[1] < 15
    H = F('1.1')*(F('3.5')+F('2.3')*F('0.127')*15/F('0.69'))
    assert H == F('10.835') < 11 and 61+3*11 <= 95

    assert F('1.73')**2 < 3 and 4+3*F('1.73') == 9*F(919, 900)
    assert F(5, 3)*F(549, 500)-F(7, 20)+F(19, 919) == F(34478, 22975) > F(3, 2)
    assert 1 < log_bounds(12*N)[0] <= log_bounds(12*N)[1] < 15
    assert 500**2 == N
    assert F(23, 20)+F(11, 70)+F(95, 500)+F(102, N) == F(1310357, 875000) < F(3, 2)
    assert log_bounds(12*big)[1] < 33 and 10**12 < big
    assert F(33, 10**6)+F(210, big) < F(1, 1000)
    assert F(23, 20)+F(11, 70)+F(22, 1000) < F(4, 3) < F(3, 2)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that the assertions are checked.')
    section_five()
    appendix_b()
    print('Passed the endpoint comparisons of Section 5.2 and Appendix B.1.')
