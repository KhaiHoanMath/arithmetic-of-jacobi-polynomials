/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticCechSections
public import ArithmeticOfJacobiPolynomials.Geometry.StructureSheafTwoCover

/-!
# The genus of the hyperelliptic model

Let `k` be a field, `f ∈ k[x]` and `X = projectiveModel f`, covered by the two affine charts
`U = chartOpen f` (`D₊(Z)`) and `V = chartOpenAtInfinity f` (`D₊(X)`). Stacks' derived-functor
cohomology of the structure sheaf (`AlgebraicGeometry.structureSheafCohomology`, the group defining
`AlgebraicGeometry.genus`, Tag 0BY7) is compared with the explicit two-chart quotient as follows.

* `ArithmeticOfJacobiPolynomials.TwoCover.structureSheafCohomologyOneEquiv` (general, proved from
Stacks'
  alternating Čech complex `Stacks.TwoAffineCech.cohomologyOneIso`) identifies
  `H¹(X, 𝒪_X)` with the cokernel of `(a, b) ↦ a|_{U ⊓ V} - b|_{U ⊓ V}` on the sections.
* The sections of the structure module are the sections `Γ(X, W)` of the scheme (identity map,
  `k`-linear), so the two restriction differentials agree and
  `structureSheafCohomologyOneEquivCechH1 : H¹(X, 𝒪_X) ≃ₗ[k] CechH1 f`.
* **`genus_projectiveModel`**: `AlgebraicGeometry.genus (toSpecField f) = ⌊(deg f - 1)/2⌋`.

Both sides of the comparison are Stacks' definitions.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory Limits Opposite Stacks.TwoAffineCech

universe u

variable {k : Type u} [Field k] (f : k[X])

/-! ### The two-chart cover -/

theorem chartOpen_sup_chartOpenAtInfinity : chartOpen f ⊔ chartOpenAtInfinity f = ⊤ := by
  rw [chartOpen, chartOpenAtInfinity, opensRange_affineChart, opensRange_affineChartAtInfinity]
  exact iSup_chart_eq_top f

theorem isAffineOpen_chartOpen : IsAffineOpen (chartOpen f) :=
  isAffineOpen_opensRange _

theorem isAffineOpen_chartOpenAtInfinity : IsAffineOpen (chartOpenAtInfinity f) :=
  isAffineOpen_opensRange _

/-! ### Sections of the structure module are the sections of the scheme -/

/-- The sections `Γ(𝒪_X, W)` of the structure sheaf viewed as a module over itself, with the
`k`-module structure of Stacks' Čech complexes (`Stacks.Cech.sectionsModule`), are `Γ(X, W)` with
the `k`-module structure `sectionsAlgebra` (identity map). -/
@[expose]
noncomputable def structureModuleSectionsEquiv (W : (projectiveModel f).Opens) :
    letI := Stacks.Cech.sectionsModule (toSpecField f)
      (TwoCover.structureModule (projectiveModel f)) W
    Γ(TwoCover.structureModule (projectiveModel f), W) ≃ₗ[k] Γ(projectiveModel f, W) :=
  letI := Stacks.Cech.sectionsModule (toSpecField f)
    (TwoCover.structureModule (projectiveModel f)) W
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The Čech differential of `TwoCover` on the structure module agrees with
`sectionsCechDifferential` under the identifications of sections. -/
theorem structureModuleSections_comm :
    letI := Stacks.Cech.sectionsModule (toSpecField f)
      (TwoCover.structureModule (projectiveModel f)) (chartOpen f)
    letI := Stacks.Cech.sectionsModule (toSpecField f)
      (TwoCover.structureModule (projectiveModel f)) (chartOpenAtInfinity f)
    letI := Stacks.Cech.sectionsModule (toSpecField f)
      (TwoCover.structureModule (projectiveModel f)) (chartOpen f ⊓ chartOpenAtInfinity f)
    (structureModuleSectionsEquiv f (chartOpen f ⊓ chartOpenAtInfinity f)).toLinearMap ∘ₗ
        TwoCover.cechRestrictDifference (toSpecField f) (chartOpen f) (chartOpenAtInfinity f)
          (TwoCover.structureModule (projectiveModel f)) =
      sectionsCechDifferential f ∘ₗ
        ((structureModuleSectionsEquiv f (chartOpen f)).prodCongr
          (structureModuleSectionsEquiv f (chartOpenAtInfinity f))).toLinearMap := by
  let _ := Stacks.Cech.sectionsModule (toSpecField f)
    (TwoCover.structureModule (projectiveModel f)) (chartOpen f)
  let _ := Stacks.Cech.sectionsModule (toSpecField f)
    (TwoCover.structureModule (projectiveModel f)) (chartOpenAtInfinity f)
  let _ := Stacks.Cech.sectionsModule (toSpecField f)
    (TwoCover.structureModule (projectiveModel f)) (chartOpen f ⊓ chartOpenAtInfinity f)
  exact LinearMap.ext fun _ => rfl

/-! ### `H¹` of the structure sheaf -/

/-- **`H¹(X, 𝒪_X) ≃ₗ[k] CechH1 f`**: the derived-functor `H¹` of the structure sheaf of the
hyperelliptic model is the two-chart Čech `H¹`. -/
@[expose]
noncomputable def structureSheafCohomologyOneEquivCechH1 :
    structureSheafCohomology (toSpecField f) 1 ≃ₗ[k] CechH1 f :=
  have := isSeparated_toSpecField f
  letI := Stacks.Cech.sectionsModule (toSpecField f)
    (TwoCover.structureModule (projectiveModel f)) (chartOpen f)
  letI := Stacks.Cech.sectionsModule (toSpecField f)
    (TwoCover.structureModule (projectiveModel f)) (chartOpenAtInfinity f)
  letI := Stacks.Cech.sectionsModule (toSpecField f)
    (TwoCover.structureModule (projectiveModel f)) (chartOpen f ⊓ chartOpenAtInfinity f)
  ((TwoCover.structureSheafCohomologyOneEquiv (toSpecField f) (chartOpen f)
      (chartOpenAtInfinity f) (isAffineOpen_chartOpen f) (isAffineOpen_chartOpenAtInfinity f)
      (chartOpen_sup_chartOpenAtInfinity f)).trans
    (cokerEquivOfComm _ _
      ((structureModuleSectionsEquiv f (chartOpen f)).prodCongr
        (structureModuleSectionsEquiv f (chartOpenAtInfinity f)))
      (structureModuleSectionsEquiv f (chartOpen f ⊓ chartOpenAtInfinity f))
      (structureModuleSections_comm f))).trans (sectionsCechH1Equiv f)

/-- **The genus of the hyperelliptic model**: `dim_k H¹(X, 𝒪_X) = ⌊(deg f - 1)/2⌋`, with
`H¹(X, 𝒪_X)` the right-derived-functor cohomology of the structure sheaf. -/
theorem genus_projectiveModel :
    AlgebraicGeometry.genus (toSpecField f) = (f.natDegree - 1) / 2 :=
  genus_eq_of_linearEquiv f (structureSheafCohomologyOneEquivCechH1 f)

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
