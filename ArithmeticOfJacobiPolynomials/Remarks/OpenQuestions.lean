/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParameters

/-!
# The manuscript's open Question 6.7

Question 6.7 asks whether these rational parameter families are eventually irreducible.
This proposition records the question. It is neither proved nor used as a hypothesis.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Question 6.7:** eventual irreducibility under the denominator conditions of Theorem 1.6. -/
def EventualRationalJacobiIrreducibilityQuestion : Prop :=
  ∀ α β : ℚ, -1 < α → -1 < β → FixedRationalParameters.DenomCond α β →
    ∃ N : ℕ, ∀ n ≥ N, Irreducible (jacobiP α β n)

end ArithmeticOfJacobiPolynomials
