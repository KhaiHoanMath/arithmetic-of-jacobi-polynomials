/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External

/-!
# The canonical principal polarization of the hyperelliptic Jacobian

The smoothness, projectivity and geometric irreducibility of the constructed model
are proved. The only assumed input is the general Milne JV 6.6/6.11 existence
theorem. The canonical condition uses the Poincaré class and the geometric
negative diagonal correspondence.
-/

public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials

/-- **The polarization underlying Corollary 6.6**.
Every relative Pic-zero Jacobian of the smooth projective model has a
canonical principal polarization, conditional on the general Milne existence input. -/
theorem jacobianCanonicalPolarization_hyperelliptic
    (hCanonical : Jacobian.CanonicalPrincipalPolarizationExists.{u})
    {k : Type u} [Field k] {f : k[X]} (h2 : (2 : k) ≠ 0)
    (hf : f.Separable) (hd : 0 < f.natDegree)
    (B : BigFppfSite.{u}) (hC : B.Contains (Hyperelliptic.projectiveModel f))
    (hk : B.Contains (Spec (.of k))) (g : B.obj hC ⟶ B.obj hk)
    (hg : B.inclusion.map g = Hyperelliptic.toSpecField f)
    [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim (Hyperelliptic.projectiveModel f) ≤ 1)
    (J : Grp (Over (Spec (.of k))))
    (hJ : Jacobian.IsJacobianOf B hC hk g hdim J) :
    ∃ (D : Grp (Over (Spec (.of k))))
      (P : Stacks.Picard.ofScheme (J.X ⊗ D.X).left) (φ : J.X ⟶ D.X)
      (_ : IsMonHom φ),
        Jacobian.IsCanonicalPrincipalPolarization (Over.mk (Hyperelliptic.toSpecField f))
          J D.X P φ := by
  have : IsCurve k (B.inclusion.map g) := by
    rw [hg]
    exact Hyperelliptic.isCurve_toSpecField h2 hf hd
  have : GeometricallyIrreducible (B.inclusion.map g) := by
    rw [hg]
    exact Hyperelliptic.geometricallyIrreducible_toSpecField hf hd
  have : Smooth (B.inclusion.map g) := by
    rw [hg]
    exact Hyperelliptic.smooth_toSpecField h2 hf hd
  have : IsProjectiveVariety k (B.inclusion.map g) := by
    rw [hg]
    exact Hyperelliptic.isProjectiveVariety_toSpecField h2 hf hd
  obtain ⟨D, P, φ, hφ, hCan⟩ := hCanonical k B hC hk g hdim J hJ
  exact ⟨D, P, φ, hφ, by simpa only [hg] using hCan⟩

end ArithmeticOfJacobiPolynomials
