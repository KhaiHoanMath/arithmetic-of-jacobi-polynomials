"""Verify the small Kaneko–Zagier irreducibility range by Newton polygons and finite fields.

Use Python 3.10+ and python-flint. The final range uses the exact real bounds in appendix_b.
"""

from bisect import bisect_left

from flint import nmod_poly

from appendix_b import primes_through, verify_range

SMALL = 1809
PRIMES = primes_through(12*SMALL + 10000)
PRIME_SET = set(PRIMES)


def reduced_polynomial(n, lam, mu, p):
    # Coefficients of P_n^(lambda/3,mu/2)(1-2t), divided by its nonzero constant term.
    # Here p > 12n+5. Every denominator and the leading coefficient are units.
    c = [1]
    s = 2*lam + 3*mu
    for j in range(n):
        den = 2*(3*(j+1)+lam)*(j+1)
        c.append(c[-1]*(j-n)*(6*(n+j+1)+s)*pow(den, -1, p) % p)
    f = nmod_poly(c, p)
    assert f.degree() == n
    return f


def possible_degrees(f, p, bound):
    """Subset sums through bound of the small factor degrees of a squarefree reduction."""
    x = nmod_poly([0, 1], p)
    residue = x
    counts = [0]
    sums = 1  # Bit d indicates a possible degree d.
    for d in range(1, bound+1):
        residue = pow(residue, p, f)
        total = (residue-x).gcd(f).degree()
        # total = sum(k * count[k] for k dividing d).
        proper = sum(k*counts[k] for k in range(1, d) if d % k == 0)
        count, remainder = divmod(total-proper, d)
        assert remainder == 0 and count >= 0
        counts.append(count)
        for _ in range(count):
            sums |= sums << d
    return sums


def verify_small(n, lam, mu):
    if n == 1:
        return 0
    s = 2*lam + 3*mu
    # At p=6(n+h)+s exactly the h-th coefficient ratio is divisible by p,
    # with valuation one. The Newton polygon thus has a segment of length n-h+1
    # and height one. A smaller rational factor then has degree at most h-1.
    bound = n//2
    for h in range(1, n+1):
        if 2*(h-1) >= n:
            break
        if 6*(n+h)+s in PRIME_SET:
            bound = h-1
            break
    if bound == 0:
        return 0
    candidates = (1 << (bound+1)) - 2
    used = 0
    for i in range(bisect_left(PRIMES, 12*n+6), len(PRIMES)):
        p = PRIMES[i]
        f = reduced_polynomial(n, lam, mu, p)
        if f.gcd(f.derivative()).degree() != 0:
            continue
        candidates &= possible_degrees(f, p, candidates.bit_length()-1)
        used += 1
        if not candidates:
            return used
    raise AssertionError((n, lam, mu, candidates))


def main():
    reductions = 0
    for n in range(1, SMALL+1):
        for lam in (-1, 1):
            for mu in (-1, 1):
                reductions += verify_small(n, lam, mu)
    print(f'All {4*SMALL:,} cases through degree {SMALL} passed; {reductions:,} modular checks.')
    # Proposition B.2's sufficient criterion applies for n >= 11.
    verify_range(SMALL+1, 8332)
    print('All 33,328 parameter-degree pairs through degree 8,332 passed.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that every identity is checked.')
    main()
