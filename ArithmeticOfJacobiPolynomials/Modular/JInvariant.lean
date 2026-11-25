/- Assembled by AxiomProver. -/
module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# The `j`-invariant and the weight-two form of [BSS, (2.2)]

Definitions shared by `ArithmeticOfJacobiPolynomials.External` (the cited [BSS] residue criterion)
and the
modular remarks (`Remarks.ModularFormsODE`, `Remarks.PolePolynomials`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open ModularForm UpperHalfPlane

open scoped MatrixGroups

local notation "Δ" => ModularForm.discriminant

/-- The modular `j`-invariant `j = E₄³/Δ`. -/
@[expose] noncomputable def jInvariant (z : ℍ) : ℂ := E₄ z ^ 3 / Δ z

theorem jInvariant_apply (z : ℍ) : jInvariant z = E₄ z ^ 3 / Δ z := rfl

/-- **BSS (2.2).** The weight-two form
`F(z) = η(z)^{4+8ε+12δ} / (E₄(z)^ε E₆(z)^δ) · ∏_j (J(z) - x_j)^{-2}`, `ε = 2a`, `δ = 2b`,
`J = j/1728`, for a multiset `x` of pole invariants. -/
noncomputable def bssWeightTwoForm (a b : ℕ) (x : Multiset ℂ) (z : ℍ) : ℂ :=
  eta z ^ (4 + 16 * a + 24 * b) / (E₄ z ^ (2 * a) * E₆ z ^ (2 * b)) /
    (x.map fun c => (jInvariant z / 1728 - c) ^ 2).prod

end ArithmeticOfJacobiPolynomials
