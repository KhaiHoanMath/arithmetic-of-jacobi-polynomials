/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianArithmetic
public import ArithmeticOfJacobiPolynomials.Applications.JacobianTateConsequences

/-!
# Corollary 6.6 with the Tate conjunct derived from Zarhin's Theorem 8.1

Manuscript Corollary 6.6. `JacobianSetting.arithmeticConclusions_of_cycleClasses` takes the
cycle-class conjunct (`JacobianSetting.CycleClasses`, the Tate conjecture on every power over every
number field) as a hypothesis for a given cycle-class predicate. The results below use the
canonical predicate.

* `JacobianSetting.cycleClasses`: `S.CycleClasses EtaleCycleClassInterface.CanonicalCycleClass`
  from the characteristic-zero assertion of Zarhin's Theorem 8.1
  (`Zarhin.TateClassesDivisorProducts`) by the manuscript's finite-extension representation and
  rational averaging (`Zarhin.TateClassesDivisorProducts.cycleClasses_rat`);
* `JacobianSetting.arithmeticConclusions`: the entire conjunction `S.ArithmeticConclusions
  CanonicalCycleClass`, from the cited hypotheses of `arithmeticConclusions_of_cycleClasses`
  and `hZarhinTate`. The preceding result supplies the cycle-class conjunct.
-/

@[expose] public noncomputable section

open Polynomial

namespace ArithmeticOfJacobiPolynomials

namespace JacobianSetting

variable {f : ℚ[X]} (S : JacobianSetting f)

/-- **The cycle class conjunct of Corollary 6.6**: for every number field
`E ⊂ ℚ̄`, prime `ℓ`, power `J_f^{h+1}` and codimension `c`, the canonical cycle class map of
`(J_f^{h+1})_E` is surjective onto the Galois invariants of `H^{2c}_ét(·_{ℚ̄}, ℚ_ℓ(c))`. This is
Zarhin's Theorem 8.1 (characteristic-zero assertion) with the manuscript's averaging descent; it is
`Zarhin.TateClassesDivisorProducts.cycleClasses_rat` applied to the fields of `S`. -/
theorem cycleClasses (hZarhinTate : Zarhin.TateClassesDivisorProducts) (hf : f.Separable)
    (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) :
    S.CycleClasses EtaleCycleClassInterface.CanonicalCycleClass := by
  intro E _ ℓ _ h c i _ B' _ X _ fX _ π hπ F hF
  exact hZarhinTate.cycleClasses_rat f hf hd (Zarhin.admissibleGalois_of_symmetric hS) S.B S.hC
    S.hQ S.g S.hg S.hdim S.J S.isJacobian E ℓ h c i B' X fX π hπ F hF

/-- **Corollary 6.6**, the entire conclusion, relative to the canonical cycle class
predicate. The cited inputs are Zarhin Theorems 2.4, 2.6, 8.1 (characteristic-zero
assertion `hZarhinTate`) and 9.1/Remark 9.2, the canonical principal polarization, complex
uniformization, the Riemann form, Weil pairings, and the Hodge-class and Mumford–Tate inputs.
The Tate (cycle class) conjuncts are discharged by `cycleClasses`. -/
theorem arithmeticConclusions (hZarhinTate : Zarhin.TateClassesDivisorProducts)
    (hEnd : Zarhin.GeometricEndomorphisms.{0})
    (hCanon : Jacobian.CanonicalPrincipalPolarizationExists.{0})
    (hUnif : AbelianBettiHodge.ComplexUniformization)
    (hRiem : AbelianBettiHodge.PolarizationRiemannForm)
    (hHM : Zarhin.HodgeAndMumfordTateGroups)
    (hExist : AbelianVariety.WeilPairingsExist.{0})
    (hAlt : AbelianVariety.PolarizedWeilAlternating.{0}) (hTate : Zarhin.TateLieAlgebra.{0})
    (hHC : JacobianArithmeticInputs.HodgeClassDivisorProducts)
    (hMT : JacobianArithmeticInputs.MumfordTateLieEquality)
    (hf : f.Separable) (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) :
    S.ArithmeticConclusions EtaleCycleClassInterface.CanonicalCycleClass :=
  S.arithmeticConclusions_of_cycleClasses EtaleCycleClassInterface.CanonicalCycleClass
    hEnd hCanon hUnif
    hRiem hHM hExist hAlt hTate hHC hMT hf hd hS (S.cycleClasses hZarhinTate hf hd hS)

end JacobianSetting

end ArithmeticOfJacobiPolynomials

end
