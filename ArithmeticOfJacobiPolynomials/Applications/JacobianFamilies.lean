/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianArithmeticConsequences
public import ArithmeticOfJacobiPolynomials.Applications.ZarhinHypotheses

/-!
# Corollary 6.6 for the polynomial families of the paper (§6.5)

Manuscript §6.5 applies Corollary 6.6 to the Kaneko–Zagier family, unequal integer
parameters, dominant factors and the derivative families by checking its hypotheses: separable of
degree at least nine with symmetric Galois group (`ZarhinHypotheses`, proved from
the proved Galois theorems and their cited and computational inputs). The families enter
only through `ZarhinHypotheses f`; the full conclusion is then
  `JacobianSetting.ArithmeticConclusions` for
every Jacobian setting of `f`.
-/

@[expose] public section

open Polynomial

namespace ArithmeticOfJacobiPolynomials

/-- The hypotheses of Corollary 6.6 are exactly the three of `ZarhinHypotheses`: this is the
manuscript's reduction of the families (§6.5) to the corollary. -/
theorem JacobianSetting.arithmeticConclusions_of_zarhinHypotheses {f : ℚ[X]} (S : JacobianSetting f)
    (hZarhinTate : Zarhin.TateClassesDivisorProducts)
    (hEnd : Zarhin.GeometricEndomorphisms.{0})
    (hCanon : Jacobian.CanonicalPrincipalPolarizationExists.{0})
    (hUnif : AbelianBettiHodge.ComplexUniformization)
    (hRiem : AbelianBettiHodge.PolarizationRiemannForm)
    (hHM : Zarhin.HodgeAndMumfordTateGroups)
    (hExist : AbelianVariety.WeilPairingsExist.{0})
    (hAlt : AbelianVariety.PolarizedWeilAlternating.{0}) (hTate : Zarhin.TateLieAlgebra.{0})
    (hHC : JacobianArithmeticInputs.HodgeClassDivisorProducts)
    (hMT : JacobianArithmeticInputs.MumfordTateLieEquality)
    (hZ : ZarhinHypotheses f) :
    S.ArithmeticConclusions EtaleCycleClassInterface.CanonicalCycleClass := by
  obtain ⟨hf, hd, hS⟩ := (zarhinHypotheses_iff f).mp hZ
  exact S.arithmeticConclusions hZarhinTate hEnd hCanon hUnif hRiem hHM hExist hAlt hTate hHC hMT
    hf hd hS

end ArithmeticOfJacobiPolynomials
