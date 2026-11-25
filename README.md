# Arithmetic of Jacobi polynomials

**Assembled by AxiomProver.**

Formalization of *Arithmetic of Jacobi polynomials* by Khai-Hoan Nguyen-Dang.

Results using external inputs are conditional on the explicit hypotheses in
[ArithmeticOfJacobiPolynomials/External.lean](ArithmeticOfJacobiPolynomials/External.lean).

## Main results

Declaration names below are in namespace `ArithmeticOfJacobiPolynomials`.

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1.1: Mahlburg–Ono conjecture | `mahlburgOnoStatement` |
| Theorem 1.2: Legendre Galois groups | `legendreGaloisStatement` |
| Theorem 1.3: unequal integral parameters | `irreducible_galoisGroupIsSymmetric_jacobiP_of_unequalGaloisThreshold_le` |
| Theorem 1.3: effective fixed-field addendum for `E = ℚ[X]/(F)`, with `F` monic integral and irreducible over `ℚ` | `unequalFixedField_of_monicPolynomial_adjoinRoot` |
| Theorem 1.3: fixed-field addendum with an existential threshold for every number field `E` | `unequalIntegralParametersFixedField` |
| Theorem 1.4: symmetric parameters | `symmetricParametersStatement_effective` |
| Theorem 1.5: Legendre polynomials and derivatives | `legendreAndDerivativesStatement` |
| Theorem 1.6: fixed rational parameters | `FixedRationalParameters.fixedRationalParameters_unfolded` |
| Corollary 1.7: derivative Galois groups | `fixedDerivativesGaloisStatement` |
| Corollary 6.1: integral parameters | `integralParametersStatement`, `integralParametersStatement_effective`, `integralParameters_of_integralParametersThreshold_le` (explicit bound) |
| Corollary 6.2: common roots | `commonRootsStatement`, `jacobiP_commonRoots_subset_range` (effective range in part 1) |
| Corollary 6.4: rational roots | `noRationalRootsStatement_of`, `noRationalRoots_of_rationalRootsThreshold_le` |
| Corollary 6.5: cone modes | `coneModesStatement_of`, `coneModes_algebraic_effective`, `coneModes_sqrt_three_effective`, `coneModes_rational_effective` |
| Corollary 6.6: hyperelliptic Jacobians and their powers for every degree `d ≥ 9` with symmetric Galois group | `JacobianSetting.arithmeticConclusions`, `exists_jacobianSetting_arithmeticConclusions_realized` |
| Theorem A.1: local irreducibility over `ℚ₃` | `kanekoZagier_localIrreducibility_of_newton` |

Question 6.7 is stated as an open question, as in the paper.

Corollary 6.6 applies to separable polynomials of even or odd degree in the stated range, including
curves without a rational point. The Jacobian represents the part of the Picard sheaf of degree
zero on geometric fibres. [Basic.lean](ArithmeticOfJacobiPolynomials/Geometry/Jacobian/Basic.lean)

### Conditional results

- Theorems 1.2 and 1.5 and the Legendre clause of Corollary 6.2 use Deng's theorem on Stieltjes'
  irreducibility conjecture, as in the manuscript. The source is an unrefereed 2026 preprint.
  [External.lean](ArithmeticOfJacobiPolynomials/External.lean#L204)
- Theorem 1.1 and the Kaneko–Zagier case of Corollary 6.6 assume the manuscript's finite-range
  computations in Proposition B.2. [External.lean](ArithmeticOfJacobiPolynomials/External.lean#L1219)
- Theorem 1.1 and the Kaneko–Zagier case of Corollary 6.6 also use two computations of
  Cullinan and Hajir. They used Magma to check irreducibility through modular index
  `10^5`. For the symmetric Galois group conditional on irreducibility through modular
  index `10^9`, they used PARI/GP to find prime pairs and Magma for the remaining small cases.
  See [Remark 4.6 and Theorem 1.8](https://doi.org/10.1090/proc/13212) and the
  [irreducibility](ArithmeticOfJacobiPolynomials/External.lean#L388) and
  [Galois](ArithmeticOfJacobiPolynomials/External.lean#L588) inputs.
- Theorem 1.5 and the Legendre clause of Corollary 6.2 assume the integer inequalities and
  factor-degree checks computed in Lemma C.2.
  [External.lean](ArithmeticOfJacobiPolynomials/External.lean#L1230-L1255)
- Corollary 6.1 uses the cited inputs of Theorem 1.3, including the location of Jacobi zeros,
  the Jacobi discriminant formula, Jordan's prime-cycle theorem, and Dusart's bound on the
  Chebyshev function.
  [External.lean](ArithmeticOfJacobiPolynomials/External.lean)

The Lean proofs take the finite computations in Proposition B.2 and Lemma C.2 as explicit
hypotheses. The following scripts reproduce them independently over their full ranges.

- Run `python3 verification/appendix_b.py` with Python 3.10 or later. It checks all 966,672
  parameter-degree pairs using outward-rounded integer bounds for logarithms.
  [Appendix B script](verification/appendix_b.py)
- Run `python3 verification/appendix_c.py` with [python-flint](https://pypi.org/project/python-flint/)
  installed (tested with 0.9.0). It checks 318 integer inequalities and the 80 remaining
  polynomials by 254 degree-eliminating reductions. The largest prime used is 317.
  [Appendix C script](verification/appendix_c.py)

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

Bibliographic references: [references.bib](references.bib).
