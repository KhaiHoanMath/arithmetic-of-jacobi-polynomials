"""Recompute both inequalities of Proposition B.2. Run with Python 3.10 or later."""

from itertools import accumulate
from math import isqrt

LOW, HIGH = 8_333, 250_000
SCALE = 10**9
TERMS = 12


def ceil_div(x, y):
    return -(-x // y)


def small_log(num, den):
    """Integer bounds for SCALE * log((1+t)/(1-t)), t = num/den in [0,1/3]."""
    assert 0 <= 3 * num <= den
    lower_power = SCALE * num // den
    upper_power = ceil_div(SCALE * num, den)
    lower = upper = 0
    for j in range(TERMS):
        lower += 2 * lower_power // (2 * j + 1)
        upper += ceil_div(2 * upper_power, 2 * j + 1)
        lower_power = lower_power * num**2 // den**2
        upper_power = ceil_div(upper_power * num**2, den**2)
    # The omitted tail is bounded by 2*SCALE*(1/3)^(2r+1)/((2r+1)*(1-1/9)).
    tail = ceil_div(18 * SCALE, 8 * (2 * TERMS + 1) * 3**(2 * TERMS + 1))
    return lower, upper + tail


LOG_TWO = small_log(1, 3)


def scaled_log(x):
    k = x.bit_length() - 1
    lo, hi = small_log(x - 2**k, x + 2**k)
    return k * LOG_TWO[0] + lo, k * LOG_TWO[1] + hi


def primes_through(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit - p*p) // p + 1)
    return [p for p, flag in enumerate(sieve) if flag]


def level_weights(p, a, b, residue):
    c = (a + b) % p
    d = (a + b) // p
    ea, eb, ec = (int(residue + v >= p) for v in (a, b, c))
    m = int(ea == eb == 1 and d + ec == 1)
    eta = int(c == p - 1)
    moment = 0 if eta else 1 - d
    e = eta + ea + eb - ec + moment - 2*m
    assert m in (0, 1) and e in (0, 1) and m + e <= 1
    return m, m + e


def first_level_totals(lam, mu, log_upper):
    """Upper bound for SCALE*T_0(n), using residue intervals and a difference array."""
    changes = [0] * (HIGH + 2)
    for p, logp in log_upper.items():
        a = lam * pow(3, -1, p) % p
        b = (p + mu) // 2
        c = (a + b) % p
        cuts = sorted({0, p-a, p-b, p-c, p})
        for left, right in zip(cuts, cuts[1:]):
            first, later = level_weights(p, a, b, left)
            # For n<p only m contributes. A nonzero m requires n+b>=p,
            # so p<=2n+1; in particular p<=12n+5, as in the defining sum.
            if first and left <= HIGH:
                changes[left] += logp
                changes[min(right, HIGH + 1)] -= logp
            if later:
                for start in range(p + left, HIGH + 1, p):
                    changes[start] += logp
                    changes[min(start + right - left, HIGH + 1)] -= logp
    return list(accumulate(changes))


def prime_power_totals(log_upper):
    """Upper bound for SCALE*Q(n). A prime power enters at ceil((p^h-5)/12)."""
    changes = [0] * (HIGH + 1)
    for p, logp in log_upper.items():
        power = p*p
        while power <= 12*HIGH + 5:
            changes[max(0, ceil_div(power - 5, 12))] += logp
            power *= p
    return list(accumulate(changes))


def valuation(k, p):
    v = 0
    while k % p == 0:
        k //= p
        v += 1
    return v


def verify(lam, mu, log_upper, higher, ternary_sums):
    first = first_level_totals(lam, mu, log_upper)
    delta = (mu + 1) // 2
    l2, u2 = LOG_TWO
    l3, u3 = scaled_log(3)
    _, u7 = scaled_log(7)
    d2 = d3 = 0
    worst_delta = None
    worst_gap = (0, 1)
    count = 0
    for n in range(1, HIGH + 1):
        d2 += 1 + valuation(3*n + lam, 2)
        d3 += 1 + valuation(2*n + mu, 3)
        if n < LOW:
            continue
        count += 1
        gap = max(d2*u2 - d3*l3, d3*u3 - d2*l2)
        assert 10*gap <= 9*n*SCALE, (lam, mu, n, 'endpoint gap')
        if gap * worst_gap[1] > worst_gap[0] * n:
            worst_gap = gap, n
        v2 = n - n.bit_count()
        v3 = (n - ternary_sums[n]) // 2
        c2 = 216*n + 48*v2 - 24*n.bit_count() - 27*d2 - 192
        c3 = 48*v3 - 22*n - 21*d3 - 8*ternary_sums[2*n + delta]
        lower = (min(c2*l2, c2*u2) + min(c3*l3, c3*u3) - 21*n*u7
                 - 48*first[n] - 144*higher[n])
        assert 1000*lower > 48*n*SCALE, (lam, mu, n, 'Delta')
        if worst_delta is None or lower * worst_delta[1] < worst_delta[0] * n:
            worst_delta = lower, n
    value, n0 = worst_delta
    gap, n1 = worst_gap
    print(f'lambda={lam:+d}, mu={mu:+d}: {count} degrees; '
          f'Delta/n >= {10**6 * value // (48*SCALE*n0)}/1000000; '
          f'endpoint gap/n <= {ceil_div(10**6 * gap, SCALE*n1)}/1000000')


def main():
    # For p>n a nonzero first-level contribution requires p<=2n+1.
    # Every prime contributing to Q has p^2<=12n+5.
    cap = max(2*HIGH + 1, isqrt(12*HIGH + 5))
    log_upper = {p: scaled_log(p)[1] for p in primes_through(cap) if p >= 5}
    higher = prime_power_totals(log_upper)
    ternary_sums = [0] * (2*HIGH + 2)
    for n in range(1, len(ternary_sums)):
        ternary_sums[n] = ternary_sums[n // 3] + n % 3
    for lam in (-1, 1):
        for mu in (-1, 1):
            verify(lam, mu, log_upper, higher, ternary_sums)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that all inequalities are checked.')
    main()
