"""Check Lemma C.2 with exact integers and finite fields. Requires python-flint."""

from math import factorial, gcd, isqrt, prod

from flint import nmod_poly


def primes_through(limit):
    return [p for p in range(2, limit + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


PRIMES = primes_through(317)
EXCEPTIONS = (
    set(range(1, 26)) | {28, 30, 31, 32, 34, 37, 40, 42, 43, 45, 46, 47},
    set(range(1, 27)) | {29, 31, 32, 33, 34, 35, 37, 38, 41, 43, 44,
                         45, 47, 49, 50, 53, 73},
)


def smooth_part(k, primes):
    leftover = k
    for p in primes:
        while leftover % p == 0:
            leftover //= p
    return k // leftover


def highest_power(p, bound):
    power = p
    while power * p <= bound:
        power *= p
    return power


def integer_test(m, n):
    primes = [p for p in PRIMES if p <= m]
    u, v = (smooth_part(x, primes) for x in (n + 1, n + 2))
    z = prod(highest_power(p, 2*n + 3) for p in primes)
    return 16**m * v**2 > 64*m*(m + 1)**2*z**2*u**2


def primitive_polynomial(m, delta):
    n = 2*m + delta
    coeff = [0] * (2*m + 1)
    for k in range(m + 1):
        numerator = (-1)**k * factorial(2*n + 2 - 2*k)
        denominator = factorial(k) * factorial(n + 1 - k) * factorial(n - 2*k)
        value, remainder = divmod(numerator, denominator)
        assert remainder == 0
        coeff[2*(m-k)] = value
    content = gcd(*coeff)
    return [c // content for c in coeff]


def factor_degree_test(m, delta):
    coeff = primitive_polynomial(m, delta)
    # Bit k is set precisely when degree k is a remaining candidate.
    candidates = (1 << (m + 1)) - 2
    retained = []
    for p in PRIMES:
        f = nmod_poly([c % p for c in coeff], p)
        if f.degree() != 2*m or f.gcd(f.derivative()).degree() != 0:
            continue
        unit, factors = f.factor()
        # Verify the product and total degree, with all multiplicities equal to one.
        product = nmod_poly([int(unit)], p)
        sums = 1
        degree = 0
        for g, exponent in factors:
            assert exponent == 1
            product *= g
            degree += g.degree()
            sums |= sums << g.degree()
        assert product == f and degree == 2*m
        new = candidates & sums
        if new != candidates:
            retained.append(p)
            candidates = new
        if not candidates:
            return retained
    raise AssertionError((m, delta, candidates))


def main():
    inequalities = 0
    all_reductions = []
    failures = []
    for delta in (0, 1):
        exceptional = set()
        for m in range(1, 200):
            if m >= 4 and integer_test(m, 2*m + delta):
                inequalities += 1
            else:
                exceptional.add(m)
                all_reductions.extend(factor_degree_test(m, delta))
        assert exceptional == EXCEPTIONS[delta]
        failures.append(len(exceptional))
    assert (inequalities, failures, len(all_reductions), max(all_reductions)) == (
        318, [37, 43], 254, 317)
    print(f'{inequalities} integer inequalities; {sum(failures)} factor-degree checks '
          f'({failures[0]} even, {failures[1]} odd); {len(all_reductions)} retained '
          f'reductions; largest prime {max(all_reductions)}.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that every identity is checked.')
    main()
