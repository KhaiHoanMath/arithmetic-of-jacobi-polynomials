/- Assembled by AxiomProver. -/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Nat.Log
public import Mathlib.RingTheory.Polynomial.Content
public import ArithmeticOfJacobiPolynomials.Polynomial.FactorDegrees

/-!
# Lemma C.2: the quantities and the two computed statements

Appendix C of the manuscript (Lemma C.2) treats the first derivatives
`P'_{2m+δ+1}(x)/x^δ`, `1 ≤ m ≤ 199`, `δ ∈ {0,1}`, by two finite calculations. This module only
*states* them (and defines the quantities occurring in the statements), so that they can enter
`External.lean` as computer-verified hypotheses without importing the proofs that use them.

* `FirstDerivativeCriterion.partU`, `partV`, `partZ` — `U = ∏_{p ≤ m} p^{v_p(n+1)}`,
  `V = ∏_{p ≤ m} p^{v_p(n+2)}`, `Z = ∏_{p ≤ m} p^{⌊log_p(2n+3)⌋}`, `n = 2m + δ`;
* `FirstDerivativeCriterion.exceptionalIndices` — the sets `E_0`, `E_1` (`37 + 43 = 80` pairs);
* `finiteDerivativeCoefficientPoly` — the rational polynomial
  `∑_{k=0}^{m} (-1)^k (2n+2-2k)! / (k! (n+1-k)! (n-2k)!) x^{n-2k-δ}` of
  (Appendix C.2), `n = 2m + δ`;

The two computed statements themselves (`FirstDerivativeIntegerInequalities`,
`FirstDerivativeFactorDegreeChecks`) are stated in `ComputerVerified` (see
`External.lean`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

namespace FirstDerivativeCriterion

/-- `U = ∏_{p ≤ m} p^{v_p(n+1)}`, `n = 2m + δ`. -/
def partU (m δ : ℕ) : ℕ :=
  ∏ p ∈ (range (m + 1)).filter Nat.Prime, p ^ padicValNat p (2 * m + δ + 1)

/-- `V = ∏_{p ≤ m} p^{v_p(n+2)}`, `n = 2m + δ`. -/
def partV (m δ : ℕ) : ℕ :=
  ∏ p ∈ (range (m + 1)).filter Nat.Prime, p ^ padicValNat p (2 * m + δ + 2)

/-- `Z = ∏_{p ≤ m} p^{⌊log_p(2n+3)⌋}`, `n = 2m + δ`. -/
def partZ (m δ : ℕ) : ℕ :=
  ∏ p ∈ (range (m + 1)).filter Nat.Prime, p ^ Nat.log p (2 * (2 * m + δ) + 3)

theorem partU_eq (m δ : ℕ) : partU m δ =
    ∏ p ∈ (range (m + 1)).filter Nat.Prime, p ^ padicValNat p (2 * m + δ + 1) := (rfl)

theorem partV_eq (m δ : ℕ) : partV m δ =
    ∏ p ∈ (range (m + 1)).filter Nat.Prime, p ^ padicValNat p (2 * m + δ + 2) := (rfl)

theorem partZ_eq (m δ : ℕ) : partZ m δ =
    ∏ p ∈ (range (m + 1)).filter Nat.Prime, p ^ Nat.log p (2 * (2 * m + δ) + 3) := (rfl)

/-- The exceptional sets `E_0`, `E_1` of the proof of Lemma C.2: the indices `m < 4` together
with the failures of (C.2) for `4 ≤ m ≤ 199`. -/
@[expose] def exceptionalIndices : ℕ → List ℕ
  | 0 => List.range' 1 25 ++ [28, 30, 31, 32, 34, 37, 40, 42, 43, 45, 46, 47]
  | _ => List.range' 1 26 ++ [29, 31, 32, 33, 34, 35, 37, 38, 41, 43, 44, 45, 47, 49, 50, 53, 73]

end FirstDerivativeCriterion

/-- The rational polynomial
`∑_{k=0}^{m} (-1)^k (2n+2-2k)! / (k! (n+1-k)! (n-2k)!) · x^{n-2k-δ}`, `n = 2m + δ`
(Appendix C.2). The primitive integral polynomial `H_n` of Lemma C.2 is
the primitive integer polynomial with positive leading coefficient proportional to it. -/
noncomputable def finiteDerivativeCoefficientPoly (m δ : ℕ) : ℚ[X] :=
  ∑ k ∈ range (m + 1),
    C ((-1) ^ k * ((2 * (2 * m + δ) + 2 - 2 * k).factorial : ℚ) /
      ((k.factorial : ℚ) * ((2 * m + δ + 1 - k).factorial : ℚ) *
        ((2 * m + δ - 2 * k).factorial : ℚ))) * polyX ^ (2 * m + δ - 2 * k - δ)

theorem finiteDerivativeCoefficientPoly_eq (m δ : ℕ) : finiteDerivativeCoefficientPoly m δ =
    ∑ k ∈ range (m + 1),
      C ((-1) ^ k * ((2 * (2 * m + δ) + 2 - 2 * k).factorial : ℚ) /
        ((k.factorial : ℚ) * ((2 * m + δ + 1 - k).factorial : ℚ) *
          ((2 * m + δ - 2 * k).factorial : ℚ))) * polyX ^ (2 * m + δ - 2 * k - δ) := (rfl)

end ArithmeticOfJacobiPolynomials
