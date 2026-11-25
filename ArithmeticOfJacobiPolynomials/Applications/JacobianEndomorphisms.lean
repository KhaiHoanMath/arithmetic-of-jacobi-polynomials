/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Algebra.HyperellipticModel

/-!
# The geometric endomorphism assertion of Corollary 6.6

This specializes the full generality endomorphism clause of Zarhin's Theorem 2.4.
The curve is the smooth projective model of `y² = f(x)` over an algebraic
closure, and the Jacobian represents its relative degree-zero Picard sheaf.
The Hodge, Tate and cycle-class conclusions are proved in `JacobianArithmetic`.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry ArithmeticOfJacobiPolynomials.GroupObject Polynomial

namespace ArithmeticOfJacobiPolynomials

/-- **Corollary 6.6, geometric endomorphisms**.
Every sheaf-theoretic Jacobian of the geometric hyperelliptic model has endomorphism
ring `ℤ`, conditional only on the stated general Zarhin endomorphism input. -/
theorem jacobianEndomorphismRing_of_symmetric
    (hEnd : Zarhin.GeometricEndomorphisms.{0})
    {L : Type} [Field L] [Algebra ℚ L] [IsAlgClosure ℚ L] [CharZero L]
    {f : ℚ[X]} (hf : f.Separable) (hd : 9 ≤ f.natDegree)
    (hS : GaloisGroupIsSymmetric f)
    (B : BigFppfSite.{0})
    (hC : B.Contains (Hyperelliptic.projectiveModel (f.map (algebraMap ℚ L))))
    (hL : B.Contains (Spec (CommRingCat.of L))) (g : B.obj hC ⟶ B.obj hL)
    (hg : B.inclusion.map g = Hyperelliptic.toSpecField (f.map (algebraMap ℚ L)))
    [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim (Hyperelliptic.projectiveModel
      (f.map (algebraMap ℚ L))) ≤ 1)
    (J : Grp (Over (Spec (CommRingCat.of L))))
    (hJ : Jacobian.IsJacobianOf B hC hL g hdim J) :
    letI := hJ.isAbelianVariety
    letI := isCommMonObj_of_isProper_of_geometricallyIntegral J.X
    Nonempty (GrpObjEnd J.X ≃+* ℤ) := by
  have :=  hJ.isAbelianVariety
  have :=  isCommMonObj_of_isProper_of_geometricallyIntegral J.X
  have hdeg : 0 < (f.map (algebraMap ℚ L)).natDegree := by
    rw [natDegree_map]
    omega
  have hCmodel := Zarhin.hyperellipticModel_projectiveModel
    (show (2 : L) ≠ 0 by norm_num) hf.map hdeg
  have hbij := hEnd ℚ L f (by norm_num) hf hd
    (Zarhin.admissibleGalois_of_symmetric hS) _ _ hCmodel B hC hL g hg hdim J hJ
  exact ⟨(RingEquiv.ofBijective (Int.castRingHom (GrpObjEnd J.X)) hbij).symm⟩

end ArithmeticOfJacobiPolynomials
