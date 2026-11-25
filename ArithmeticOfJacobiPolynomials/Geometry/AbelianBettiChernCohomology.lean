/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianHodgeClasses
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Reading alternating period forms as Betti cohomology classes

Corollary 6.6 uses the form induced by a line bundle. This module
supplies the linear algebra step from its rational alternating period form to
singular cohomology. The comparison is fixed by singular cup products and
the universal coefficient pairing. Mathlib's perfect exterior-power pairing
gives uniqueness from evaluation on exterior products of homology classes.

The Chern form of a line bundle, which supplies such a form, is constructed in
`AbelianBettiChernClass`.
-/

public noncomputable section

namespace ArithmeticOfJacobiPolynomials.AbelianBettiChernCohomology

open CategoryTheory AlgebraicGeometry
open ArithmeticOfJacobiPolynomials.ComplexRealization
  ArithmeticOfJacobiPolynomials.AbelianBettiHodge
open ArithmeticOfJacobiPolynomials.AbelianBettiCohomology
  ArithmeticOfJacobiPolynomials.AbelianHodgeClasses

variable (A : Over (Spec (.of ℂ))) (r : ℕ)

/-- Exterior powers of the universal coefficient equivalence. -/
@[expose] def exteriorUC :
    (⋀[ℚ]^r (bettiCohomology A 1)) ≃ₗ[ℚ] ⋀[ℚ]^r (Module.Dual ℚ (bettiOne A)) :=
  LinearEquiv.ofBijective (exteriorPower.map r (bettiUC A 1).toLinearMap)
    ⟨exteriorPower.map_injective_field (bettiUC A 1).injective,
      exteriorPower.map_surjective (bettiUC A 1).surjective⟩

theorem exteriorUC_apply (x : ⋀[ℚ]^r (bettiCohomology A 1)) :
    exteriorUC A r x = hodgeToDual A r x := rfl

variable [FiniteDimensional ℚ (bettiOne A)]

/-- The cohomology class is determined by its pairing with exterior products
of first homology. All three equivalences use canonical library maps. -/
@[expose] def periodEvaluationEquiv (c : CupComparison A r) :
    bettiCohomology A r ≃ₗ[ℚ] Module.Dual ℚ (⋀[ℚ]^r (bettiOne A)) :=
  (c.toEquiv.symm.trans (exteriorUC A r)).trans
    (LinearEquiv.ofBijective (exteriorPower.pairingDual ℚ (bettiOne A) r)
      (exteriorPower.bijective_pairingDual (R := ℚ) (n := r) (bettiOne A)))

theorem periodEvaluationEquiv_apply (c : CupComparison A r) (x : bettiCohomology A r) :
    periodEvaluationEquiv A r c x =
      exteriorPower.pairingDual ℚ (bettiOne A) r
        (hodgeToDual A r (c.toEquiv.symm x)) := rfl

/-- Cup normalization makes the evaluation independent of the comparison datum. -/
theorem periodEvaluationEquiv_eq (c c' : CupComparison A r) :
    periodEvaluationEquiv A r c = periodEvaluationEquiv A r c' := by
  unfold periodEvaluationEquiv
  rw [CupComparison.toEquiv_unique c c']

/-- Read a rational alternating form as a class in degree-two singular
cohomology. Evaluation on pairs of homology classes characterizes this class. -/
@[expose] def classOfAlternatingForm (c : CupComparison A 2)
    (F : (bettiOne A) [⋀^Fin 2]→ₗ[ℚ] ℚ) : bettiCohomology A 2 :=
  (periodEvaluationEquiv A 2 c).symm (exteriorPower.alternatingMapLinearEquiv F)

/-- The class evaluates to the supplied form, with no factorial normalization. -/
theorem classOfAlternatingForm_evaluate (c : CupComparison A 2)
    (F : (bettiOne A) [⋀^Fin 2]→ₗ[ℚ] ℚ) (v : Fin 2 → bettiOne A) :
    periodEvaluationEquiv A 2 c (classOfAlternatingForm A c F)
      (exteriorPower.ιMulti ℚ 2 v) = F v := by
  rw [classOfAlternatingForm, LinearEquiv.apply_symm_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- Equality of evaluations on all pairs proves equality of classes. -/
theorem classOfAlternatingForm_unique (c : CupComparison A 2)
    (F : (bettiOne A) [⋀^Fin 2]→ₗ[ℚ] ℚ) (x : bettiCohomology A 2)
    (hx : ∀ v : Fin 2 → bettiOne A,
      periodEvaluationEquiv A 2 c x (exteriorPower.ιMulti ℚ 2 v) = F v) :
    x = classOfAlternatingForm A c F := by
  apply (periodEvaluationEquiv A 2 c).injective
  apply exteriorPower.linearMap_ext
  ext v
  exact (hx v).trans (classOfAlternatingForm_evaluate A c F v).symm

theorem classOfAlternatingForm_eq (c c' : CupComparison A 2)
    (F : (bettiOne A) [⋀^Fin 2]→ₗ[ℚ] ℚ) :
    classOfAlternatingForm A c F = classOfAlternatingForm A c' F := by
  unfold classOfAlternatingForm
  rw [periodEvaluationEquiv_eq A 2 c c']

section Naturality

variable {A r} {B : Over (Spec (.of ℂ))} [FiniteDimensional ℚ (bettiOne B)]

omit [FiniteDimensional ℚ (bettiOne A)] [FiniteDimensional ℚ (bettiOne B)] in
/-- Exterior duality commutes with the homology map. -/
theorem pairingDual_natural (f : A ⟶ B) :
    exteriorPower.pairingDual ℚ (bettiOne A) r ∘ₗ
        exteriorPower.map r (bettiOneMap f).dualMap =
      (exteriorPower.map r (bettiOneMap f)).dualMap ∘ₗ
        exteriorPower.pairingDual ℚ (bettiOne B) r := by
  apply exteriorPower.linearMap_ext
  ext u v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti, LinearMap.dualMap_apply]
  rfl

/-- The evaluation of a pulled-back class on homology agrees with evaluation of
the original class on the corresponding exterior product of images. -/
theorem periodEvaluationEquiv_natural (f : A ⟶ B)
    (cA : CupComparison A r) (cB : CupComparison B r)
    (x : bettiCohomology B r) (v : ⋀[ℚ]^r (bettiOne A)) :
    periodEvaluationEquiv A r cA ((bettiCohomologyMap f r).hom x) v =
      periodEvaluationEquiv B r cB x (exteriorPower.map r (bettiOneMap f) v) := by
  have hcup : cA.toEquiv.symm ((bettiCohomologyMap f r).hom x) =
      exteriorPower.map r (bettiCohomologyMap f 1).hom (cB.toEquiv.symm x) := by
    apply cA.toEquiv.injective
    rw [LinearEquiv.apply_symm_apply,
      ← CupComparison.natural f cA cB, LinearEquiv.apply_symm_apply]
  rw [periodEvaluationEquiv_apply, hcup, hodgeToDual_natural]
  exact LinearMap.congr_fun (LinearMap.congr_fun (pairingDual_natural f)
    (hodgeToDual B r (cB.toEquiv.symm x))) v

/-- Pullback of the class constructed from a form is the class constructed from
the pulled-back form. -/
theorem classOfAlternatingForm_natural (f : A ⟶ B)
    (cA : CupComparison A 2) (cB : CupComparison B 2)
    (F : (bettiOne B) [⋀^Fin 2]→ₗ[ℚ] ℚ) :
    (bettiCohomologyMap f 2).hom (classOfAlternatingForm B cB F) =
      classOfAlternatingForm A cA (F.compLinearMap (bettiOneMap f)) := by
  apply classOfAlternatingForm_unique
  intro v
  rw [periodEvaluationEquiv_natural, exteriorPower.map_apply_ιMulti,
    classOfAlternatingForm_evaluate]
  rfl

end Naturality

end ArithmeticOfJacobiPolynomials.AbelianBettiChernCohomology
