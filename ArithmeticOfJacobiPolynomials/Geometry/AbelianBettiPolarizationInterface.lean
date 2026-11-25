/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiChernClass
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianPolarization
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiGroups

/-!
# Characterization of the Betti form induced by a polarization

This file contains only interfaces needed by Corollary 6.6. The form lives on
singular first homology. Its values on integral periods are fixed by the
transition functions of an ample invertible module (up to the sign
convention explained at `PolarizationForm`), and that module
induces the specified morphism to the Picard dual. Existence is a general
Milne, Abelian Varieties, Chapter I, Example 13.3 input in External.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials.AbelianBettiHodge

open ArithmeticOfJacobiPolynomials.ComplexRealization ArithmeticOfJacobiPolynomials.AbelianDuality
open ArithmeticOfJacobiPolynomials.AbelianBettiChern

variable (A : Over (Spec (.of ℂ))) [GrpObj A]
  (D : UniformizationData A)
  (Â : Over (Spec (.of ℂ))) [GrpObj Â]
  (P : Stacks.Picard.ofScheme (A ⊗ Â).left) (φ : A ⟶ Â)

/-- The line bundle induces `φ` by the translation-minus-original
Picard class. The Poincaré fibre is pulled back along `(id, φ(a))`. -/
def InducesPolarization (M : Stacks.Picard.ofScheme A.left) : Prop :=
  ∀ a : 𝟙_ (Over (Spec (.of ℂ))) ⟶ A,
    Stacks.Picard.schemePullbackClass
      (lift (𝟙 A) (toUnit A ≫ a ≫ φ)).left P = inducedClass A M a

/-- The form induced by the specified polarization. Period normalization is
tested on all pullback trivializations, and the existence of such a
trivialization is recorded.

**Sign convention.** The first Chern form `chernForm` of an ample invertible module is the
classical Riemann form `E_L = Im H` of Milne (Chapter I, Lemma 2.4 and Example 13.3) and
Birkenhake–Lange (Theorem 2.1.2): `E_L (i x) x = H(x, x) > 0`, equivalently
`E_L x (i x) < 0`, where `i` is the complex structure `J` of the canonical Hodge structure.
The positivity convention of `HodgeStructureNegOne.Polarization` is `ψ_ℝ x (J x) > 0`
(Deligne's `ψ(x, C y)` positive). The polarization `riemann` of the canonical Hodge structure
that the line bundle induces is therefore `-E_L`: `period_normalization` states
`riemann.form = -chernForm` on integral periods. `IsBettiFirstChern` uses `chernForm = E_L`, and
the induced polarization is `-E_L`.
The symplectic and similitude groups of `ψ` and `-ψ` are equal, so the Hodge and Mumford–Tate
statements hold with either sign. For the
Jacobi theta function on `ℂ/(ℤ + ℤ i)` one finds `chernForm 1 i = -1`, so the polarization has
`ψ(1, i · 1) = +1 > 0`. -/
structure PolarizationForm where
  /-- An invertible module on the original complex abelian variety. -/
  lineBundle : A.left.Modules
  invertible : Stacks.Ample.IsInvertibleModule A.left lineBundle
  ample : @Stacks.Ample.IsAmple A.left lineBundle invertible
  induces : InducesPolarization A Â P φ
    (Stacks.SheafOfModules.picardClass A.left.presheaf
      (Stacks.RingedSpace.structureIsSheaf A.left.toRingedSpace) lineBundle invertible)
  covers : CoversPoints lineBundle
  trivialization : ∃ s : ExpSection D lineBundle, s.NonVanishing
  /-- The rational Riemann form on first singular homology. -/
  riemann : D.canonicalHodge.Polarization
  /-- The polarization is minus the first Chern form `E_L`, computed from
  transition-function logarithms, on every pair of integral periods (see the sign
  convention above: `E_L (x) (J x) < 0` for ample `L`, while a polarization has
  `ψ x (J x) > 0`). -/
  period_normalization : ∀ (s : ExpSection D lineBundle) (_ : s.NonVanishing)
    (a b : bettiOne A),
    IsPeriod D (D.period (1 ⊗ₜ[ℚ] a)) → IsPeriod D (D.period (1 ⊗ₜ[ℚ] b)) →
      riemann.form a b =
        -(chernForm (hL := covers) s (D.period (1 ⊗ₜ[ℚ] a))
          (D.period (1 ⊗ₜ[ℚ] b)) : ℚ)

end ArithmeticOfJacobiPolynomials.AbelianBettiHodge
