/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianArithmetic
public import ArithmeticOfJacobiPolynomials.Applications.JacobianExistence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Realized Jacobian settings for Corollary 6.6

The smooth projective models satisfy the general cited Jacobian existence input.
Stacks supplies a common big fppf site containing the three models and fields.
Thus the corollary's characterized Jacobian setting has a witness (Corollary 6.6).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace ArithmeticOfJacobiPolynomials

/-- The general Milne existence input applies to the manuscript model over
`ℚ`, `ℚ̄` and `ℂ`; Stacks supplies the common site required by the statements. -/
theorem exists_jacobianSetting (hJ : Jacobian.JacobianExists.{0})
    {f : ℚ[X]} (hf : f.Separable) (hd : 0 < f.natDegree) :
    Nonempty (JacobianSetting f) := by
  have hdL : 0 < (f.map (algebraMap ℚ (AlgebraicClosure ℚ))).natDegree := by
    rw [Polynomial.natDegree_map]; exact hd
  have hdC : 0 < (f.map (algebraMap ℚ ℂ)).natDegree := by
    rw [Polynomial.natDegree_map]; exact hd
  obtain ⟨J, hQ⟩ := Hyperelliptic.exists_isJacobianOf hJ (by norm_num) hf hd
  obtain ⟨JL, hL⟩ := Hyperelliptic.exists_isJacobianOf hJ (by norm_num) hf.map hdL
  obtain ⟨JC, hC⟩ := Hyperelliptic.exists_isJacobianOf hJ (by norm_num) hf.map hdC
  let objects : Set Scheme.{0} :=
    {Hyperelliptic.projectiveModel f, Spec (.of ℚ),
      Hyperelliptic.projectiveModel (f.map (algebraMap ℚ (AlgebraicClosure ℚ))),
      Spec (.of (AlgebraicClosure ℚ)),
      Hyperelliptic.projectiveModel (f.map (algebraMap ℚ ℂ)), Spec (.of ℂ)}
  have : Finite objects := by dsimp [objects]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing objects
  have hXQ : B.Contains (Hyperelliptic.projectiveModel (f)) :=
    hB _ (by simp [objects])
  have hkQ : B.Contains (Spec (.of (ℚ))) := hB _ (by simp [objects])
  let gQ : B.obj hXQ ⟶ B.obj hkQ :=
    ObjectProperty.homMk (Hyperelliptic.toSpecField (f))
  have hiQ : IsCurve (ℚ) (Hyperelliptic.toSpecField (f)) :=
    Hyperelliptic.isCurve_toSpecField (by norm_num) hf hd
  have hpQ : IsProper (B.inclusion.map gQ) := Hyperelliptic.isProper_toSpecField (f)
  let dQ := (IsCurve.topologicalKrullDim_eq_one
    (k := (ℚ)) (f := Hyperelliptic.toSpecField (f))).le
  obtain ⟨eQ⟩ := hQ B hXQ hkQ gQ rfl
  have hXL : B.Contains
      (Hyperelliptic.projectiveModel (f.map (algebraMap ℚ (AlgebraicClosure ℚ)))) :=
    hB _ (by simp [objects])
  have hkL : B.Contains (Spec (.of (AlgebraicClosure ℚ))) := hB _ (by simp [objects])
  let gL : B.obj hXL ⟶ B.obj hkL :=
    ObjectProperty.homMk (Hyperelliptic.toSpecField (f.map (algebraMap ℚ (AlgebraicClosure ℚ))))
  have hiL : IsCurve (AlgebraicClosure ℚ)
      (Hyperelliptic.toSpecField (f.map (algebraMap ℚ (AlgebraicClosure ℚ)))) :=
    Hyperelliptic.isCurve_toSpecField (by norm_num) hf.map hdL
  have hpL : IsProper (B.inclusion.map gL) :=
    Hyperelliptic.isProper_toSpecField (f.map (algebraMap ℚ (AlgebraicClosure ℚ)))
  let dL := (IsCurve.topologicalKrullDim_eq_one
    (k := (AlgebraicClosure ℚ))
    (f := Hyperelliptic.toSpecField (f.map (algebraMap ℚ (AlgebraicClosure ℚ))))).le
  obtain ⟨eL⟩ := hL B hXL hkL gL rfl
  have hXC : B.Contains (Hyperelliptic.projectiveModel (f.map (algebraMap ℚ ℂ))) :=
    hB _ (by simp [objects])
  have hkC : B.Contains (Spec (.of (ℂ))) := hB _ (by simp [objects])
  let gC : B.obj hXC ⟶ B.obj hkC :=
    ObjectProperty.homMk (Hyperelliptic.toSpecField (f.map (algebraMap ℚ ℂ)))
  have hiC : IsCurve (ℂ) (Hyperelliptic.toSpecField (f.map (algebraMap ℚ ℂ))) :=
    Hyperelliptic.isCurve_toSpecField (by norm_num) hf.map hdC
  have hpC : IsProper (B.inclusion.map gC) :=
    Hyperelliptic.isProper_toSpecField (f.map (algebraMap ℚ ℂ))
  let dC := (IsCurve.topologicalKrullDim_eq_one
    (k := (ℂ)) (f := Hyperelliptic.toSpecField (f.map (algebraMap ℚ ℂ)))).le
  obtain ⟨eC⟩ := hC B hXC hkC gC rfl
  exact ⟨{
    B := B, hC := hXQ, hQ := hkQ, g := gQ, hg := rfl, proper := hpQ,
    hdim := dQ, J := J, isJacobian := eQ, comm := eQ.isAbelianVariety.isCommMonObj,
    hL := hkL, hCL := hXL, gL := gL, hgL := rfl, properL := hpL,
    hdimL := dL, JL := JL, isJacobianL := eL,
    hℂ := hkC, hCℂ := hXC, gℂ := gC, hgℂ := rfl, properℂ := hpC,
    hdimℂ := dC, Jℂ := JC, isJacobianℂ := eC
  }⟩

end ArithmeticOfJacobiPolynomials
