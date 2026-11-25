/- Assembled by AxiomProver. -/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Short Weierstrass cubics and supersingularity

Definitions used by the cited Hasse criterion (`ArithmeticOfJacobiPolynomials.External`) and by
`ArithmeticOfJacobiPolynomials.Remarks.LegendreElliptic`: the curve `y² = x³ + a₂x² + a₄x + a₆`,
its cubic, and
supersingularity as the absence of nonzero `p`-torsion over an algebraic closure.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace LegendreElliptic

open Polynomial

universe u

/-- The Weierstrass curve with `a₁ = a₃ = 0`, i.e. `y² = x³ + a₂x² + a₄x + a₆`. -/
@[expose] def shortCubicCurve {K : Type*} [CommRing K] (a₂ a₄ a₆ : K) : WeierstrassCurve K :=
  ⟨0, a₂, 0, a₄, a₆⟩

/-- The monic cubic `x³ + a₂x² + a₄x + a₆`. -/
@[expose] noncomputable def monicCubic {K : Type*} [CommRing K] (a₂ a₄ a₆ : K) : K[X] :=
  X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆

open scoped Classical in
/-- **Supersingularity** [KZ, §1]: an elliptic curve `E` over a field `K` of characteristic `p`
is supersingular if the group `E(K̄)` has no nonzero `p`-torsion. Here `K̄` is
`AlgebraicClosure K` and `E(K̄)` is Mathlib's group of points of the affine Weierstrass model
(the point at infinity being its zero; the group law uses classical decidable equality). -/
def IsSupersingular {K : Type u} [Field K] (p : ℕ) (E : WeierstrassCurve K) : Prop :=
  ∀ P : (E.baseChange (AlgebraicClosure K)).toAffine.Point, p • P = 0 → P = 0

end LegendreElliptic

end ArithmeticOfJacobiPolynomials
