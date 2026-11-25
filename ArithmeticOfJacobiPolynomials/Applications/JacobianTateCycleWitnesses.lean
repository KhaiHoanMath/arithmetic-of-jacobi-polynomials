/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianArithmetic
public import ArithmeticOfJacobiPolynomials.Applications.JacobianEtaleSite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.PreconnectedRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions

/-!
# Dimensions and roots for the Tate cycle conclusion (Corollary 6.6)

The library's relative-dimension and base-change theorems verify the geometric
hypotheses on the manuscript's Jacobian powers. The compatible roots of unity
are supplied by `exists_tateTwist_isPrimitiveRoot`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open GroupScheme AbelianCycleClass Stacks.AbelianGroup

namespace JacobianSetting

variable {f : ℚ[X]} (S : JacobianSetting f)

/-- The manuscript Jacobian has the indicated relative dimension over `ℚ`. -/
theorem relativeDimension (hf : f.Separable) (hd : 0 < f.natDegree) :
    letI := S.isJacobian.isAbelianVariety
    RelativeDimension S.J.X.hom ((f.natDegree - 1) / 2) := by
  have := S.isJacobian.isAbelianVariety
  have : IsIntegral S.J.X.left :=
    S.isJacobian.isAbelianVariety.toIsProperVariety.toIsVariety.toIsIntegral
  have : Smooth S.J.X.hom := smooth_of_isAbelianVariety ℚ S.J.X
  obtain ⟨d, hrel⟩ := exists_relativeDimension_of_smooth_of_preconnectedSpace S.J.X.hom
  have hdim := topologicalKrullDim_eq_of_relativeDimension S.J.X.hom hrel
  have hg : d = (f.natDegree - 1) / 2 := by
    have h := S.dimension hf hd
    change ((topologicalKrullDim S.J.X.left).unbotD 0).toNat = _ at h
    simpa [hdim] using h
  exact hg ▸ hrel

/-- The `h`-fold Jacobian product has relative dimension `h·g`. -/
theorem relativeDimension_power (hf : f.Separable) (hd : 0 < f.natDegree) (h : ℕ) :
    letI := S.isJacobian.isAbelianVariety
    RelativeDimension (powObj ℚ S.J.X h).hom (h * ((f.natDegree - 1) / 2)) := by
  have := S.isJacobian.isAbelianVariety
  induction h with
  | zero =>
    have h0 := (locallyQuasiFinite_iff_relativeDimension_zero (𝟙 (Spec (.of ℚ)))).mp
      inferInstance
    simpa only [powObj_zero, Over.tensorUnit_hom, Nat.zero_mul] using h0
  | succ h ih =>
    have hfst := RelativeDimension.of_isPullback
      (IsPullback.of_hasPullback S.J.X.hom (powObj ℚ S.J.X h).hom).flip
      ih
    have hrel := RelativeDimension.comp_of_flat
      (pullback.fst S.J.X.hom (powObj ℚ S.J.X h).hom) S.J.X.hom hfst
      (S.relativeDimension hf hd)
    simpa only [powObj_succ, Over.tensorObj_hom, Nat.succ_mul] using hrel

/-- The number-field base change of each power keeps its relative dimension. -/
theorem relativeDimension_numberFieldPower (hf : f.Separable) (hd : 0 < f.natDegree)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : ℕ) :
    letI := S.isJacobian.isAbelianVariety
    RelativeDimension
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ E)))).obj
        (powObj ℚ S.J.X h)).hom) (h * ((f.natDegree - 1) / 2)) := by
  have := S.isJacobian.isAbelianVariety
  exact RelativeDimension.of_isPullback (IsPullback.of_hasPullback _ _)
    (S.relativeDimension_power hf hd h)

end JacobianSetting

/-- A compatible primitive-root system on the manuscript's coefficient field exists. -/
theorem exists_jacobianRootSystem (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (RootSystem ℓ (AlgebraicClosure ℚ)) := by
  obtain ⟨x, hx⟩ := exists_tateTwist_isPrimitiveRoot (L := AlgebraicClosure ℚ) ℓ
    (natCast_ne_zero_algebraicClosure_rat ℓ)
  exact ⟨{
    root := fun n => ((Additive.toMul
      ((x : ℕ → Additive ((AlgebraicClosure ℚ)ˣ)) (n + 1)) : (AlgebraicClosure ℚ)ˣ) :
        AlgebraicClosure ℚ)
    isPrimitive := fun n => IsPrimitiveRoot.coe_units_iff.mpr (hx (n + 1))
    pow_root := fun n => by
      have h := congrArg (fun y : Additive ((AlgebraicClosure ℚ)ˣ) =>
        ((Additive.toMul y : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) (smul_seq_succ x (n + 1))
      simpa only [toMul_nsmul, Units.val_pow_eq_pow_val] using h
  }⟩

end ArithmeticOfJacobiPolynomials
