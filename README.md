# Arithmetic of Jacobi polynomials

Lean proofs and verification programs for *Arithmetic of Jacobi polynomials* by Khai-Hoan Nguyen-Dang. AxiomProver assembled the original formalization. The supplementary proofs and computations accompany the revised manuscript. [Original preprint, October 2026](https://hexagonmath.org/2610.00468v1)

The theorem table below identifies the public declarations. Their types give the mathematical hypotheses. The [verification guide](verification/README.md) covers the finite ranges, the certificates and the commands for reproducing them.

## Main results

Declaration names below are in namespace `ArithmeticOfJacobiPolynomials`.

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1.1: Mahlburg–Ono conjecture | `mahlburgOnoStatement` |
| Theorem 1.2: Legendre Galois groups | `legendreGalois_of_prime_bounds` |
| Theorem 1.3: unequal integral parameters | `irreducible_galoisGroupIsSymmetric_jacobiP_of_unequalGaloisThreshold_le` |
| Theorem 1.3: effective fixed-field addendum for `E = ℚ[X]/(F)`, with `F` monic integral and irreducible over `ℚ` | `unequalFixedField_of_monicPolynomial_adjoinRoot` |
| Theorem 1.3: fixed-field addendum with an existential threshold for every number field `E` | `unequalIntegralParametersFixedField` |
| Theorem 1.4: symmetric parameters | `symmetricParametersStatement_effective` |
| Theorem 1.5: Legendre polynomials and derivatives | `legendreAndDerivatives_verified` |
| Theorem 1.6: fixed rational parameters | `FixedRationalParameters.fixedRationalParameters_unfolded` |
| Corollary 1.7: derivative Galois groups | `fixedDerivativesGaloisStatement` |
| Corollary 6.1: integral parameters | `integralParametersStatement`, `integralParametersStatement_effective`, `integralParameters_of_integralParametersThreshold_le` (explicit bound) |
| Corollary 6.2: common roots | `commonRoots_verified`, `jacobiP_commonRoots_subset_range` (effective range in part 1) |
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
| Legendre Galois groups (Theorem 1.2) | The wreath-product proof uses the preceding irreducibility result. For the action on pairs, Lean verifies the prime alternatives of Cullinan–Hajir, Theorem 1.7, throughout `26 ≤ n ≤ 10^9`. The published small-degree calculation enters only for `1 ≤ n ≤ 25`. For the prime interval in Lemma 5.11, twenty primes per residue class cover all integers in `9 ≤ x < 2,000,000`. For `x ≥ 2,000,000` the proof uses the BMOR bound already needed for the Galois argument. [Interval proof](ArithmeticOfJacobiPolynomials/Verification/ModFourInterval.lean) · [Prime certificates](ArithmeticOfJacobiPolynomials/Verification/LegendrePrimePairs.lean) · [Cullinan–Hajir, Theorems 1.7 and 1.9(a)](https://doi.org/10.1016/j.indag.2014.01.004) |
| First derivatives (last two assertions of Theorem 1.5) and the Legendre clause of Corollary 6.2 | Lean checks the 318 integer inequalities. Of the 80 exceptional polynomials, 45 are Eisenstein and 24 have Eisenstein reciprocal. Lean checks an irreducible reduction for each of the other eleven. The statements in the table therefore take no Appendix C computation as a hypothesis. The original 254 reductions at primes up to 317 are independently reproduced by the Python programs. [Eisenstein checks](ArithmeticOfJacobiPolynomials/Verification/DerivativeEisensteinData.lean) · [Frobenius certificates](ArithmeticOfJacobiPolynomials/Verification/Rabin) · [Theorem 1.5 and Corollary 6.2](ArithmeticOfJacobiPolynomials/Verification/DerivativeAll.lean) |
| Kaneko–Zagier (Theorem 1.1 and the corresponding case of Corollary 6.6) | The inequalities in Proposition B.2 for `8333 ≤ n ≤ 250000` enter as a computational hypothesis. For `n ≤ 8332` the proof uses Cullinan–Hajir's Magma irreducibility calculation through modular index `10^5`. For `n < 10^6` it uses their Galois result conditional on irreducibility, published through modular index `10^9`. Cullinan and Hajir used PARI/GP for prime pairs and Magma for the remaining small cases. The verification programs independently check both published inputs throughout the degree ranges used here. [Proposition B.2 input](ArithmeticOfJacobiPolynomials/External.lean#L1219) · [Cullinan–Hajir, Remark 4.6 and Theorem 1.8](https://doi.org/10.1090/proc/13212) |
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

## Hypotheses made explicit

- **Lemma 2.5.** The Vandermonde bound in the manuscript takes `k ≥ 1`. Lean writes its exponent using subtraction of natural numbers, which gives zero for `k − 1` when `k = 0`. For positive `k` the formulas agree. [IntervalVandermonde.lean](ArithmeticOfJacobiPolynomials/Analysis/IntervalVandermonde.lean#L139)
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

After the build, `lake env lean verification/Audit.lean` checks the exported project declarations for logical axioms beyond `propext`, `Classical.choice` and `Quot.sound`. Inspect a theorem's type to see which mathematical assumptions it uses. For example, the following commands display the hypotheses of Theorem 1.2 and
the logical axioms of its proof.

```lean
import ArithmeticOfJacobiPolynomials
#check ArithmeticOfJacobiPolynomials.legendreGalois_of_prime_bounds
#print axioms ArithmeticOfJacobiPolynomials.legendreGalois_of_prime_bounds
```

[Bibliography](references.bib)
