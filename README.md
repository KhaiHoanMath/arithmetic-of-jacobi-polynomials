# Arithmetic of Jacobi polynomials

**The original Lean formalization was assembled by AxiomProver.**

Formalization of *Arithmetic of Jacobi polynomials* by Khai-Hoan Nguyen-Dang.

The comments in the original modules refer to the preprint supplied to AxiomProver.
The table below lists the declarations for the revised manuscript. The cited theorems are
hypotheses of those declarations. The supplement proves the
all-degree Legendre irreducibility statement from the paper's comparison and the
Holt–Wahab theorem. It also verifies the finite integer calculations described below.
[External inputs](ArithmeticOfJacobiPolynomials/External.lean) · [Legendre proofs](ArithmeticOfJacobiPolynomials/Verification/Legendre.lean)

## Main results

Declaration names below are in namespace `ArithmeticOfJacobiPolynomials`.

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1.1: Mahlburg–Ono conjecture | `mahlburgOnoStatement` |
| Theorem 1.2: Legendre Galois groups | `legendreGalois_of_comparison` |
| Theorem 1.3: unequal integral parameters | `irreducible_galoisGroupIsSymmetric_jacobiP_of_unequalGaloisThreshold_le` |
| Theorem 1.3: effective fixed-field addendum for `E = ℚ[X]/(F)`, with `F` monic integral and irreducible over `ℚ` | `unequalFixedField_of_monicPolynomial_adjoinRoot` |
| Theorem 1.3: fixed-field addendum with an existential threshold for every number field `E` | `unequalIntegralParametersFixedField` |
| Theorem 1.4: symmetric parameters | `symmetricParametersStatement_effective` |
| Theorem 1.5: Legendre polynomials and derivatives | `legendreAndDerivatives_of_comparison` |
| Theorem 1.6: fixed rational parameters | `FixedRationalParameters.fixedRationalParameters_unfolded` |
| Corollary 1.7: derivative Galois groups | `fixedDerivativesGaloisStatement` |
| Corollary 6.1: integral parameters | `integralParametersStatement`, `integralParametersStatement_effective`, `integralParameters_of_integralParametersThreshold_le` (explicit bound) |
| Corollary 6.2: common roots | `commonRoots_of_comparison`, `jacobiP_commonRoots_subset_range` (effective range in part 1) |
| Corollary 6.4: rational roots | `noRationalRootsStatement_of`, `noRationalRoots_of_rationalRootsThreshold_le` |
| Corollary 6.5: cone modes | `coneModesStatement_of`, `coneModes_algebraic_effective`, `coneModes_sqrt_three_effective`, `coneModes_rational_effective` |
| Corollary 6.6: hyperelliptic Jacobians and their powers for every degree `d ≥ 9` with symmetric Galois group | `JacobianSetting.arithmeticConclusions`, `exists_jacobianSetting_arithmeticConclusions_realized` |
| Theorem A.1: local irreducibility over `ℚ₃` | `kanekoZagier_localIrreducibility_of_newton` |

Question 6.7 is stated as an open question, as in the paper.

Corollary 6.6 applies to separable polynomials of even or odd degree in the stated range, including
curves without a rational point. The Jacobian represents the part of the Picard sheaf of degree
zero on geometric fibres. [Basic.lean](ArithmeticOfJacobiPolynomials/Geometry/Jacobian/Basic.lean)

## What the Lean proofs use

| Manuscript result | Proof and remaining inputs |
| --- | --- |
| Legendre irreducibility (first two assertions of Theorem 1.5) | For half-degree `m ≥ 100`, the paper's comparison gives irreducibility. For `m < 100`, Holt–Wahab covers degrees near an odd prime. Lean checks the finite covering and the exact inequalities for the ten other degrees. The external inputs are Holt–Wahab, Hanson's lcm bound and the classical theorem on Jacobi zeros. [Proof](ArithmeticOfJacobiPolynomials/Verification/Legendre.lean) · [Holt–Wahab, in Cullinan–Hajir, Corollary 3.4(b)](https://doi.org/10.1016/j.indag.2014.01.004) |
| Legendre Galois groups (Theorem 1.2) | The wreath-product proof uses the preceding irreducibility result. For the action on pairs, Lean verifies the prime alternatives of Cullinan–Hajir, Theorem 1.7, throughout `26 ≤ n ≤ 10^9`. The published small-degree calculation enters only for `1 ≤ n ≤ 25`. The proof also uses the cited prime-distribution and group-theoretic results. [Prime certificates](ArithmeticOfJacobiPolynomials/Verification/LegendrePrimePairs.lean) · [Cullinan–Hajir, Theorems 1.7 and 1.9(a)](https://doi.org/10.1016/j.indag.2014.01.004) |
| First derivatives (last two assertions of Theorem 1.5) and the Legendre clause of Corollary 6.2 | Lean proves all 318 integer inequalities of Lemma C.2. The 80 modular factor-degree checks remain an explicit hypothesis. The verification below also gives one irreducible reduction for each of the 80 polynomials. [Integer proofs](ArithmeticOfJacobiPolynomials/Verification/FiniteArithmetic.lean) · [Modular hypothesis](ArithmeticOfJacobiPolynomials/External.lean#L1235-L1255) |
| Kaneko–Zagier (Theorem 1.1 and the corresponding case of Corollary 6.6) | The inequalities in Proposition B.2 for `8333 ≤ n ≤ 250000` enter as a computational hypothesis. For `n ≤ 8332` the proof uses Cullinan–Hajir's Magma irreducibility calculation through modular index `10^5`. For `n < 10^6` it uses their Galois result conditional on irreducibility, published through modular index `10^9`. Cullinan and Hajir used PARI/GP for prime pairs and Magma for the remaining small cases. The scripts below independently check both published inputs throughout the degree ranges used here. [Proposition B.2 input](ArithmeticOfJacobiPolynomials/External.lean#L1219) · [Cullinan–Hajir, Remark 4.6 and Theorem 1.8](https://doi.org/10.1090/proc/13212) |
| Integral parameters (Corollary 6.1) | The proof uses the cited results of Theorem 1.3, including the location of Jacobi zeros, the Jacobi discriminant, Jordan's prime-cycle theorem and Dusart's bound for the Chebyshev function. [Statements of the cited results](ArithmeticOfJacobiPolynomials/External.lean) |

For the negative sign, degrees 73–81 use the second alternative of Cullinan–Hajir,
Theorem 1.7. For example, at `n = 73` one can take `q = 47`, for which
`2(2n+1−q)−1 = 199`. The other intervals use primes of the first kind.
[Prime certificates](ArithmeticOfJacobiPolynomials/Verification/LegendrePrimePairs.lean)

Deng's preprint gives the all-degree Legendre irreducibility theorem and the resultant comparison
that motivated this work. The three Legendre declarations in the table of main results now
derive irreducibility within the project. The original declarations taking
`DengLegendreIrreducibility` as an argument remain available. Lean's `#print axioms` reports
the logical axioms in a proof term. The external mathematical inputs can be read in the
theorem's type. The declarations `legendreIrreducibility_of_comparison` and
`firstDerivativeIntegerInequalities_proved` also supply the corresponding inputs to the
original proofs. [Deng, Theorem 1.1](https://arxiv.org/abs/2609.22336v2)

### Reproducing the computations

Run the following commands from the repository root with Python 3.10 or later.

- `python3 verification/appendix_b.py` checks both bounds for all 966,672 parameter-degree
  pairs using outward-rounded integer bounds for logarithms. [Appendix B](verification/appendix_b.py)
- `python3 verification/check_factor_degrees.py` checks the original 254 modular reductions
  (largest prime 317) and an alternative set of 80 primes (largest 2311). For each exceptional
  polynomial, the alternative prime gives an irreducible reduction of the full degree.
  For a single-prime witness of degree `d = 2m`, Rabin's criterion asks for
  `X^(p^d) = X mod H` and coprimality of `H` with `X^(p^(d/q)) − X` for each prime `q | d`.
  The implication from these conditions to rational irreducibility is proved in Lean.
  The declaration `irreducible_derivative_legendreP_of_frobenius_reduction` applies this
  criterion directly to the normalized derivative. The 80 numerical polynomial checks run
  in standard Python. The original factor-degree hypothesis retains its prime bound of 317. The first prime after each index in the data file is the
  irreducible-reduction witness. [Criterion in Lean](ArithmeticOfJacobiPolynomials/Verification/Frobenius.lean) · [Checker](verification/check_factor_degrees.py) · [Primes](verification/appendix_c_primes.txt)
- `python3 verification/appendix_c.py` independently selects the original reductions by
  factorization with python-flint (tested with 0.9.0) and recomputes the 318 integer
  inequalities. [Appendix C](verification/appendix_c.py)
- `python3 verification/check_kaneko_zagier_irreducibility.py` independently verifies all
  33,328 cases of the published irreducibility calculation used by the manuscript. Through
  degree 1,809 it bounds possible factor degrees by a height-one Newton edge when available,
  then excludes the remaining degrees by modular Frobenius calculations. In degrees
  1,810–8,332 it reuses the exact inequalities of Proposition B.2. The finite-field operations
  use python-flint. [Small-degree irreducibility check](verification/check_kaneko_zagier_irreducibility.py)
- `python3 verification/check_galois_ranges.py` checks both small Galois inputs, given
  irreducibility. For Kaneko–Zagier it finds the prime pairs of Cullinan–Hajir,
  Theorem 1.6, in 3,999,945 cases with `1 ≤ n < 10^6`. Eight cases are linear or
  quadratic. The other 43 and all 46 Legendre quotient polynomials in degrees 3–25
  use two squarefree reductions. One Frobenius element is an `(n−1)`-cycle, so the
  stabilizer of its fixed point is transitive on the remaining roots. Another has one
  2-cycle and only odd cycles otherwise, so an odd power is a transposition. Double
  transitivity then gives every transposition. For a nonmonic polynomial with leading coefficient `a` prime to
  the chosen prime, the monic polynomial `a^(n−1) f(X/a)` has the same cycle degrees.
  [Dedekind’s theorem, Milne, Theorem 4.28](https://www.jmilne.org/math/Books/FT0.pdf) · [Checker](verification/check_galois_ranges.py) · [Kaneko–Zagier primes](verification/kz_small_galois_primes.txt) · [Legendre primes](verification/legendre_small_galois_primes.txt)

## Hypotheses made explicit

- **Lemma C.1.** The factor-degree criterion makes the positive-degree assumption `D ≥ 1` explicit.
  The applications in Appendix C use positive degree.
  [FactorDegrees.lean](ArithmeticOfJacobiPolynomials/Polynomial/FactorDegrees.lean#L97)
- **Lemma 5.11.** The cited prime-interval estimate is used for integer `x ≥ 9`. The proof takes
  `x = 2n + 2` or `x = 2n + 4`.
  [External.lean](ArithmeticOfJacobiPolynomials/External.lean#L556)

## Build

With the pinned Lean toolchain, `lake exe cache get` fetches the Mathlib cache, and the second
command fetches the Stacks cache for the pinned Stacks revision. `lake build` then compiles the
project modules.

```sh
lake exe cache get
curl -fsSL https://stacks-cache.axiommath.workers.dev/lake/lake-cache-get-fast.sh | bash -s .
lake build
```

After the build, the following commands display the hypotheses of Theorem 1.2 and
the logical axioms of its proof.

```lean
import ArithmeticOfJacobiPolynomials
#check ArithmeticOfJacobiPolynomials.legendreGalois_of_comparison
#print axioms ArithmeticOfJacobiPolynomials.legendreGalois_of_comparison
```

[Bibliography](references.bib)
