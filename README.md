# Arithmetic of Jacobi polynomials

Lean proofs and verification programs for *Arithmetic of Jacobi polynomials* by Khai-Hoan Nguyen-Dang. [Revised manuscript (PDF)](arithmetic_of_jacobi_polynomials.pdf)

The AxiomProver team supplied the original Lean formalization and identified two missing hypotheses in the preprint. The author is especially grateful to Ken Ono for sharing the formalization and pointing out the team's corrections. For the revision, the author added the supplementary Lean proofs for Legendre polynomials and their first derivatives, the finite certificates, and the independent verification programs. [Original AxiomProver formalization](https://github.com/KhaiHoanMath/arithmetic-of-jacobi-polynomials/tree/5adf9486721d39ff62f6f4e5e38bce2f862c9f01)

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

## What the Lean proofs use

| Manuscript result | Proof and remaining inputs |
| --- | --- |
| Legendre irreducibility (first two assertions of Theorem 1.5) | For half-degree `m ≥ 100`, the paper's comparison gives irreducibility. For `m < 100`, Holt–Wahab covers degrees near an odd prime. Lean checks the finite covering and the exact inequalities for the ten other degrees. The external inputs are Holt–Wahab, Hanson's lcm bound and the classical theorem on Jacobi zeros. [Proof](ArithmeticOfJacobiPolynomials/Verification/Legendre.lean) · [Holt–Wahab, in Cullinan–Hajir, Corollary 3.4(b)](https://doi.org/10.1016/j.indag.2014.01.004) |
| Legendre Galois groups (Theorem 1.2) | The wreath-product proof uses the preceding irreducibility result. For the action on pairs, Lean verifies the prime alternatives of Cullinan–Hajir, Theorem 1.7, throughout `26 ≤ n ≤ 10^9`. The published small-degree calculation enters only for `1 ≤ n ≤ 25`. For the prime interval in Lemma 5.11, twenty primes per residue class cover all integers in `9 ≤ x < 2,000,000`. For `x ≥ 2,000,000` the proof uses the BMOR bound already needed for the Galois argument. [Interval proof](ArithmeticOfJacobiPolynomials/Verification/ModFourInterval.lean) · [Prime certificates](ArithmeticOfJacobiPolynomials/Verification/LegendrePrimePairs.lean) · [Cullinan–Hajir, Theorems 1.7 and 1.9(a)](https://doi.org/10.1016/j.indag.2014.01.004) |
| First derivatives (last two assertions of Theorem 1.5) and the Legendre clause of Corollary 6.2 | Lean checks the 318 integer inequalities. Of the 80 exceptional polynomials, 45 are Eisenstein and 24 have Eisenstein reciprocal. Lean checks an irreducible reduction for each of the other eleven. The statements in the table therefore take no Appendix C computation as a hypothesis. The original 254 reductions at primes up to 317 are independently reproduced by the Python programs. [Eisenstein checks](ArithmeticOfJacobiPolynomials/Verification/DerivativeEisensteinData.lean) · [Frobenius certificates](ArithmeticOfJacobiPolynomials/Verification/Rabin) · [Theorem 1.5 and Corollary 6.2](ArithmeticOfJacobiPolynomials/Verification/DerivativeAll.lean) |
| Kaneko–Zagier (Theorem 1.1 and the corresponding case of Corollary 6.6) | The inequalities in Proposition B.2 for `8333 ≤ n ≤ 250000` enter as a computational hypothesis. For `n ≤ 8332` the proof uses Cullinan–Hajir's Magma irreducibility calculation through modular index `10^5`. For `n < 10^6` it uses their Galois result conditional on irreducibility, published through modular index `10^9`. Cullinan and Hajir used PARI/GP for prime pairs and Magma for the remaining small cases. The verification programs independently check both published inputs throughout the degree ranges used here. [Proposition B.2 input](ArithmeticOfJacobiPolynomials/External.lean#L1219) · [Cullinan–Hajir, Remark 4.6 and Theorem 1.8](https://doi.org/10.1090/proc/13212) |
| Integral parameters (Corollary 6.1) | The proof uses the cited results of Theorem 1.3, including the location of Jacobi zeros, the Jacobi discriminant, Jordan's prime-cycle theorem and Dusart's bound for the Chebyshev function. [Statements of the cited results](ArithmeticOfJacobiPolynomials/External.lean) |

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
