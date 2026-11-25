# Reproducing the finite computations

From the repository root, run the following with Python 3.10 or later. The full run uses python-flint for polynomial arithmetic and for regenerating the Lean certificate data. The other programs use the Python standard library.

```sh
python3 -m pip install python-flint==0.9.0
python3 verification/run_all.py
```

Each program can also be run separately. It stops if an inequality or certificate fails.

| Manuscript calculation | What is checked |
| --- | --- |
| Proposition B.2, four parameter pairs and every degree from 8,333 through 250,000 | Two implementations check both inequalities in every one of the 966,672 cases. The first accumulates prime contributions over residue intervals and uses the series for the logarithm. The second updates the prime contributions by factoring four integers at each degree and encloses logarithms by repeated squaring. [Residue intervals](appendix_b.py) · [Independent check](check_appendix_b_independent.py) |
| Small Kaneko–Zagier irreducibility range | For degrees 1–1,809, Newton polygons and 15,930 modular reductions exclude all possible smaller factors. In degrees 1,810–8,332, the same two inequalities as in Proposition B.2 hold. Together these check 33,328 cases. [Checker](check_kaneko_zagier_irreducibility.py) |
| Finite Galois calculations, assuming irreducibility | For Kaneko–Zagier in degrees below one million, 3,999,945 cases admit the prime pair of Cullinan–Hajir, eight have degree one or two, and 43 use the stored Frobenius witnesses. The script also checks all 46 Legendre quotient polynomials in degrees 3–25. [Checker](check_galois_ranges.py) · [Kaneko–Zagier primes](kz_small_galois_primes.txt) · [Legendre primes](legendre_small_galois_primes.txt) |
| Small Legendre degrees | The order-zero comparison and one-prime irreducibility certificates give a second proof covering all 198 cases in degrees 2–199. [Checker](check_legendre_small.py) |
| Lemma C.2, first derivatives | The original calculation checks 318 inequalities and chooses 254 reductions, with largest prime 317, for the other 80 cases. A second program rechecks the chosen reductions and one full-degree irreducible reduction for each exceptional polynomial, with largest prime 2311. [Original calculation](appendix_c.py) · [Frobenius and gcd checker](check_factor_degrees.py) · [Prime witnesses](appendix_c_primes.txt) |
| Independent Newton-polygon proof of the 80 exceptions | Polygons at primes up to 151 settle 77 cases directly. One translated polygon settles a further case. Only degree two remains in the last two cases, where scalar root tests modulo 13 and 193 finish the proof. [Checker](check_derivative_newton.py) · [Dumas's product rule, pp. 216–217](https://www.numdam.org/item/JMPA_1906_6_2__191_0/) |
| Normalizations, small examples and cutoff constants | The checks reconstruct all 398 derivative models from the Legendre three-term recurrence and all 43 exceptional Kaneko–Zagier models from the defining Jacobi sum. They also check the Appendix A cubic and Newton polygons, the rational logarithm margins in Appendix C, and the explicit cutoff comparisons. [Polynomial examples](check_manuscript_examples.py) · [Cutoff constants](check_cutoff_constants.py) |

Over the full range of Proposition B.2, the independent checker gives $\Delta_n/n\ge 0.136734$ and $|D_{2,n}\log 2-D_{3,n}\log 3|/n\le 0.262378$. The proof requires the first quantity to exceed $0.001$ and the second to be at most $0.9$. Both reported bounds are rounded outwards.

For the small Galois witnesses, the first squarefree reduction gives an `(n−1)`-cycle with one fixed point. Irreducibility gives transitivity, so the stabilizer of that point is transitive on the other roots. The second reduction gives one 2-cycle and only odd cycles otherwise. An odd power is a transposition. Double transitivity then gives the full symmetric group. For a nonmonic integral polynomial with leading coefficient `a` prime to the reduction prime, the monic polynomial `a^(n−1) f(X/a)` has the same cycle degrees. [Cullinan–Hajir](https://doi.org/10.1090/proc/13212) · [Dedekind's theorem in Milne, Theorem 4.28](https://www.jmilne.org/math/Books/FT0.pdf)

In [appendix_c_primes.txt](appendix_c_primes.txt), the first prime after each pair of indices certifies an irreducible reduction of the full degree. The primes that follow exclude factor degrees by the original procedure. The [main README](../README.md#what-the-lean-proofs-use) records which computations enter the formal proofs.

In the Lean proof of the derivative theorem, Eisenstein's criterion applies directly in 45 cases and after reversal in 24. For each of the eleven others, Lean checks a Frobenius identity in the quotient of the prime-field polynomial ring by the degree-`d` reduction. It checks that the `d`th Frobenius iterate fixes `X`, and that the difference between the `(d/q)`th iterate of `X` and `X` is invertible for every prime divisor `q` of `d`. The largest reduction prime in these eleven certificates is 1163.

The full run also calls `python3 verification/generate_derivative_certificates.py --check`, which regenerates the eleven finite-field certificate files and compares them with the published copies. Use `--output-dir DIR` to write a separate set. Lean checks the identities in the certificates when the project builds. [Generator](generate_derivative_certificates.py)
