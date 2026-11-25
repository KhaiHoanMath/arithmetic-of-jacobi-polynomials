/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianArithmetic
public import ArithmeticOfJacobiPolynomials.Applications.JacobianBettiDimension

/-!
# Corollary 6.6: dimensions and base-change witnesses

The conclusions of Corollary 6.6 quantify over the complex Jacobian `S.Jℂ`, its
positive powers, and over origin-preserving morphisms `emb : S.Jℂ.X.left ⟶ S.J.X.left` exhibiting
`S.Jℂ` as the complex base change of `S.J`. This file verifies that these objects exist and have
the manuscript's numerical invariants:

* `JacobianSetting.dimension_complex`: `dim J_ℂ = ⌊(d - 1)/2⌋` (Stacks' genus theorem for the
  Jacobian over `ℂ` and the proved hyperelliptic genus formula);
* `JacobianSetting.dimension_power`: for the general complex-uniformization input, the
  dimension of `J_ℂ^{h+1}` is `(h+1) ⌊(d - 1)/2⌋` (from `finrank H₁`, which is `2 dim` for the
  abelian variety and for its power);
* `JacobianSetting.exists_baseChange_embedding`: an `emb` with
  `IsPullback emb S.Jℂ.X.hom S.J.X.hom (Spec.map ℚ → ℂ)` and `PreservesOrigin emb`: the base
  change of `J` is a Jacobian of the base-changed curve
  (`Jacobian.BaseChange.isJacobianOf_baseChange`), hence isomorphic as a group scheme to
  `S.Jℂ` (`Jacobian.IsJacobianOf.exists_grpIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open ArithmeticOfJacobiPolynomials.GroupObject GroupScheme AbelianBettiHodge AbelianArithmetic

namespace JacobianSetting

variable {f : ℚ[X]} (S : JacobianSetting f)

/-- **`dim J_ℂ = ⌊(d - 1)/2⌋`** for the complex Jacobian of the setting. -/
theorem dimension_complex (hf : f.Separable) (hd : 0 < f.natDegree) :
    Stacks.Groupoids.abelianVarietyDimension S.Jℂ.X = (f.natDegree - 1) / 2 := by
  have hdℂ : 0 < (f.map (algebraMap ℚ ℂ)).natDegree := by
    rw [Polynomial.natDegree_map]; exact hd
  have := S.isJacobianℂ.isAbelianVariety
  have : IsCurve ℂ (S.B.inclusion.map S.gℂ) := by
    rw [S.hgℂ]
    exact Hyperelliptic.isCurve_toSpecField (by norm_num) hf.map hdℂ
  have : IsProjectiveVariety ℂ (S.B.inclusion.map S.gℂ) := by
    rw [S.hgℂ]
    exact Hyperelliptic.isProjectiveVariety_toSpecField (by norm_num) hf.map hdℂ
  have : Smooth (S.B.inclusion.map S.gℂ) := by
    rw [S.hgℂ]
    exact Hyperelliptic.smooth_toSpecField (by norm_num) hf.map hdℂ
  rw [Jacobian.abelianVarietyDimension_eq_genus_of_isAlgClosed S.B S.hCℂ ℂ S.gℂ S.isJacobianℂ,
    S.hgℂ, Hyperelliptic.genus_toSpecField, Polynomial.natDegree_map]

/-- **The dimension of every positive power** `J_ℂ^{h+1}` is `(h+1) ⌊(d - 1)/2⌋`, for the
general complex-uniformization input: `finrank H₁` is `2 dim` for `J_ℂ^{h+1}` and equals
`(h+1) · finrank H₁(J_ℂ) = (h+1) · 2 dim J_ℂ`. -/
theorem dimension_power (hUnif : AbelianBettiHodge.ComplexUniformization)
    (hf : f.Separable) (hd : 0 < f.natDegree) (h : ℕ) :
    letI := S.isJacobianℂ.isAbelianVariety
    Stacks.Groupoids.abelianVarietyDimension (powObj ℂ S.Jℂ.X (h + 1)) =
      (h + 1) * ((f.natDegree - 1) / 2) := by
  have := S.isJacobianℂ.isAbelianVariety
  let DA := Classical.choice (hUnif S.Jℂ.X)
  let D (h : ℕ) := Classical.choice (hUnif (powObj ℂ S.Jℂ.X (h + 1)))
  have h1 := (D h).finrank_bettiOne_eq_twice_dimension (powObj ℂ S.Jℂ.X (h + 1))
  have h2 := DA.finrank_bettiPow S.Jℂ.X D h
  have h3 := DA.finrank_bettiOne_eq_twice_dimension S.Jℂ.X
  rw [S.dimension_complex hf hd] at h3
  rw [h2, h3] at h1
  nlinarith

/-- **The origin-preserving base-change morphism** `J_ℂ ⟶ J`: the complex Jacobian of the
setting is the base change of `J` along `ℚ → ℂ`, by an `emb` forming a pullback square with the
structure maps and preserving the origins. -/
theorem exists_baseChange_embedding :
    ∃ emb : S.Jℂ.X.left ⟶ S.J.X.left,
      IsPullback emb S.Jℂ.X.hom S.J.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ∧ PreservesOrigin emb := by
  have hsq : IsPullback (Hyperelliptic.baseChangeMap ℂ f) (S.B.inclusion.map S.gℂ)
      (S.B.inclusion.map S.g)
      (S.B.inclusion.map (Jacobian.BaseChange.siteMap S.B S.hQ S.hℂ)) := by
    rw [S.hg, S.hgℂ]
    exact Hyperelliptic.isPullback_baseChangeMap ℂ f
  have eK := Jacobian.BaseChange.isJacobianOf_baseChange (Hyperelliptic.baseChangeMap ℂ f) hsq
    S.hdim S.hdimℂ S.isJacobian
  obtain ⟨ε, -⟩ := eK.exists_grpIso S.B S.hCℂ S.hℂ S.gℂ S.hdimℂ S.isJacobianℂ
  let i : S.Jℂ.X.left ≅ pullback S.J.X.hom (Jacobian.BaseChange.specMap ℚ ℂ) :=
    (Over.forget _).mapIso (Jacobian.grpIsoToOverIso ε.symm)
  have hi : i.symm.hom ≫ S.Jℂ.X.hom = pullback.snd _ _ := Over.w ε.hom.hom.hom
  have h1 : η[S.Jℂ.X] ≫ ε.inv.hom.hom = η[((AlgebraicGeometry.GroupScheme.baseChange
      (Jacobian.BaseChange.specMap ℚ ℂ)).obj S.J).X] := IsMonHom.one_hom ε.inv.hom.hom
  have h2 : (η[((AlgebraicGeometry.GroupScheme.baseChange
      (Jacobian.BaseChange.specMap ℚ ℂ)).obj S.J).X]).left ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) ≫ (η[S.J.X]).left := by
    let : GrpObj ((Over.pullback (Jacobian.BaseChange.specMap ℚ ℂ)).obj S.J.X) :=
      AlgebraicGeometry.GroupScheme.grpObjPullbackObj (Jacobian.BaseChange.specMap ℚ ℂ) S.J.X
    have h := congrArg (fun m => m.left)
      (MulEquiv.map_one (AlgebraicGeometry.GroupScheme.pointsMulEquiv
        (Jacobian.BaseChange.specMap ℚ ℂ) S.J.X (𝟙_ (Over (Spec (.of ℂ))))))
    simp only [AlgebraicGeometry.GroupScheme.pointsMulEquiv_apply_left, Hom.one_def,
      Over.comp_left] at h
    have e1 := Over.w (CartesianMonoidalCategory.toUnit (𝟙_ (Over (Spec (.of ℂ)))))
    have e2 := Over.w (CartesianMonoidalCategory.toUnit
      ((Over.map (Jacobian.BaseChange.specMap ℚ ℂ)).obj (𝟙_ (Over (Spec (.of ℂ))))))
    have e1' : (CartesianMonoidalCategory.toUnit (𝟙_ (Over (Spec (.of ℂ))))).left = 𝟙 _ := by
      simp
    have e2' : (CartesianMonoidalCategory.toUnit
        ((Over.map (Jacobian.BaseChange.specMap ℚ ℂ)).obj (𝟙_ (Over (Spec (.of ℂ)))))).left =
        Jacobian.BaseChange.specMap ℚ ℂ := by
      simp
    rw [e1', e2'] at h
    simp only [Category.id_comp] at h
    exact h
  refine ⟨i.hom ≫ pullback.fst _ _, ?_, ?_⟩
  · refine (IsPullback.of_hasPullback S.J.X.hom (Jacobian.BaseChange.specMap ℚ ℂ)).of_iso
      i.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simpa using hi.symm
    · simp
    · simp
  · unfold PreservesOrigin
    have h3 := congrArg (fun m => m.left) h1
    simp only [Over.comp_left] at h3
    rw [← Category.assoc]
    exact (congrArg (fun m => m ≫ pullback.fst _ _) h3).trans h2

end JacobianSetting

end ArithmeticOfJacobiPolynomials

end
