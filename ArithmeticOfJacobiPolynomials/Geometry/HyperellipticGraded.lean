/- Assembled by AxiomProver. -/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The grading of a quotient by a homogeneous ideal

For a graded `R`-algebra `A = ⨁ 𝒜 n` and a homogeneous ideal `I`, the quotient `A ⧸ I` is
graded by the images `(𝒜 n).map (A → A ⧸ I)` (`quotientGrading`, `quotientGradedAlgebra`).
This is used to build the weighted homogeneous coordinate ring
`k[X, Z, Y]/(Y^2 - F(X, Z))` of the smooth projective model of a hyperelliptic curve
(`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace GradedQuotient

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (I : Ideal A)

/-- The image of the grading in the quotient `A ⧸ I`. -/
@[expose]
def quotientGrading (n : ι) : Submodule R (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I).toLinearMap

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
theorem mk_mem_quotientGrading {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I a ∈ quotientGrading 𝒜 I n :=
  ⟨a, ha, rfl⟩

instance : SetLike.GradedMonoid (quotientGrading 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, by simp⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, by simp⟩

/-- The projection of the degree-`n` part. -/
@[expose]
noncomputable def gradeMap (n : ι) : 𝒜 n →+ quotientGrading 𝒜 I n :=
  (LinearMap.submoduleMap (Ideal.Quotient.mkₐ R I).toLinearMap (𝒜 n)).toAddMonoidHom

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
@[simp] theorem coe_gradeMap (n : ι) (a : 𝒜 n) :
    (gradeMap 𝒜 I n a : A ⧸ I) = Ideal.Quotient.mk I (a : A) :=
  rfl

/-- `A → ⨁ (A ⧸ I)_n`, the decomposition of a lift. -/
@[expose]
noncomputable def liftDecompose : A →+ ⨁ n, quotientGrading 𝒜 I n :=
  (DirectSum.map (gradeMap 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

theorem liftDecompose_apply (a : A) :
    liftDecompose 𝒜 I a = DirectSum.map (gradeMap 𝒜 I) (DirectSum.decompose 𝒜 a) :=
  rfl

variable {𝒜 I}

theorem liftDecompose_eq_zero (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) :
    liftDecompose 𝒜 I a = 0 := by
  rw [DirectSum.ext_iff]
  intro n
  rw [liftDecompose_apply, DirectSum.map_apply, DirectSum.zero_apply]
  apply Subtype.ext
  simp only [coe_gradeMap, ZeroMemClass.coe_zero]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hI n ha)

theorem liftDecompose_congr (hI : I.IsHomogeneous 𝒜) {a b : A}
    (h : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b) :
    liftDecompose 𝒜 I a = liftDecompose 𝒜 I b := by
  rw [← sub_eq_zero, ← map_sub (liftDecompose 𝒜 I)]
  exact liftDecompose_eq_zero hI (Ideal.Quotient.eq.mp h)

theorem coe_liftDecompose (a : A) :
    DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I) (liftDecompose 𝒜 I a) =
      Ideal.Quotient.mk I a := by
  have key : ∀ z : ⨁ n, 𝒜 n,
      DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I) (DirectSum.map (gradeMap 𝒜 I) z) =
        Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 z) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of n x => rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of,
        DirectSum.coeAddMonoidHom_of, coe_gradeMap]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [liftDecompose_apply, key]
  congr 1
  exact (DirectSum.decompose 𝒜).symm_apply_apply a

theorem liftDecompose_of_mk_eq (hI : I.IsHomogeneous 𝒜) (z : ⨁ n, quotientGrading 𝒜 I n) :
    ∀ a : A, Ideal.Quotient.mk I a = DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I) z →
      liftDecompose 𝒜 I a = z := by
  induction z using DirectSum.induction_on with
  | zero =>
    intro a ha
    rw [map_zero] at ha
    exact liftDecompose_eq_zero hI ((Ideal.Quotient.eq_zero_iff_mem).mp ha)
  | of n x =>
    intro a ha
    obtain ⟨x, b, hb, hbx⟩ := x
    rw [DirectSum.coeAddMonoidHom_of] at ha
    have hb' : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := by
      rw [ha]
      exact hbx.symm
    rw [liftDecompose_congr hI hb', liftDecompose_apply,
      DirectSum.decompose_of_mem 𝒜 hb, DirectSum.map_of]
    congr 1
    exact Subtype.ext hbx
  | add x y hx hy =>
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
      (DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I) x)
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective
      (DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I) y)
    have hbc : Ideal.Quotient.mk I a = Ideal.Quotient.mk I (b + c) := by
      rw [ha, map_add, map_add, hb, hc]
    rw [liftDecompose_congr hI hbc, map_add, hx b hb, hy c hc]

/-- The decomposition of `A ⧸ I`. -/
@[expose]
noncomputable def quotientDecompose (x : A ⧸ I) : ⨁ n, quotientGrading 𝒜 I n :=
  liftDecompose 𝒜 I (Function.surjInv Ideal.Quotient.mk_surjective x)

variable (𝒜 I)

/-- The quotient of a graded algebra by a homogeneous ideal is graded. -/
@[instance_reducible]
noncomputable def quotientGradedAlgebra (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (quotientGrading 𝒜 I) where
  toGradedMonoid := inferInstance
  decompose' := quotientDecompose
  left_inv x := by
    rw [quotientDecompose, coe_liftDecompose]
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective x
  right_inv z := by
    rw [quotientDecompose]
    exact liftDecompose_of_mk_eq hI z _ (Function.surjInv_eq Ideal.Quotient.mk_surjective _)

end GradedQuotient

end ArithmeticOfJacobiPolynomials
