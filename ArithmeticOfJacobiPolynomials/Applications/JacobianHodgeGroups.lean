/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External

/-!
# Corollary 6.6: the Hodge and Mumford--Tate group application

The polynomial is embedded into the complex numbers and its constructed
smooth projective model is checked against the general Zarhin hypotheses.
The Betti form is characterized by its ample line bundle and period values.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial MonoidalCategory

namespace ArithmeticOfJacobiPolynomials

/-- The Hodge/MT conjuncts of Corollary 6.6, for every
Picard-zero Jacobian of the complex smooth projective model. -/
theorem jacobianHodgeGroups_hyperelliptic
    (hZ : Zarhin.HodgeAndMumfordTateGroups)
    {k : Type} [Field k] [Algebra k ℂ] {f : k[X]}
    (hf : f.Separable) (hd : 9 ≤ f.natDegree) (hGal : Zarhin.AdmissibleGalois f)
    (B : BigFppfSite.{0})
    (hC : B.Contains (Hyperelliptic.projectiveModel (f.map (algebraMap k ℂ))))
    (hℂ : B.Contains (Spec (.of ℂ))) (g : B.obj hC ⟶ B.obj hℂ)
    (hg : B.inclusion.map g = Hyperelliptic.toSpecField (f.map (algebraMap k ℂ)))
    [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim (Hyperelliptic.projectiveModel
      (f.map (algebraMap k ℂ))) ≤ 1)
    (J : Grp (Over (Spec (.of ℂ))))
    (hJ : Jacobian.IsJacobianOf B hC hℂ g hdim J)
    (D : Over (Spec (.of ℂ))) [GrpObj D]
    (P : Stacks.Picard.ofScheme (J.X ⊗ D).left) (φ : J.X ⟶ D) [IsMonHom φ]
    (hCan : Jacobian.IsCanonicalPrincipalPolarization
      (Over.mk (Hyperelliptic.toSpecField (f.map (algebraMap k ℂ)))) J D P φ)
    (U : AbelianBettiHodge.UniformizationData J.X)
    (F : AbelianBettiHodge.PolarizationForm J.X U D P φ) :
    U.canonicalHodge.hodgeGroup = symplecticGroup F.riemann.form ∧
      U.canonicalHodge.mumfordTateGroup = similitudeGroup F.riemann.form := by
  have hfℂ : (f.map (algebraMap k ℂ)).Separable := hf.map
  have hdℂ : 0 < (f.map (algebraMap k ℂ)).natDegree := by
    rw [natDegree_map]
    omega
  exact hZ k f hf hd hGal
    (Over.mk (Hyperelliptic.toSpecField (f.map (algebraMap k ℂ))))
    (Zarhin.hyperellipticModel_projectiveModel (by norm_num) hfℂ hdℂ)
    B hC hℂ g hg hdim J hJ D P φ hCan U F

end ArithmeticOfJacobiPolynomials
