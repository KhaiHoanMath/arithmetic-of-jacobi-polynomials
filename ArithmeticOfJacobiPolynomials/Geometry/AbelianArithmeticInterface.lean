/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiPolarizationInterface
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianHodgeClasses
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianCycleClass
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeGeometricPoints
public import ArithmeticOfJacobiPolynomials.Algebra.TateRational
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Minimal characterized interfaces needed to state Corollary 6.6

Manuscript Corollary 6.6. Only definitions required to *state* the corollary and the cited general
theorems it uses (Zarhin 8.1, 9.1) are introduced. See `External.lean` for the literature each
interface stands for.

## Betti side

* Mathlib's `exteriorPower.pairingDual` evaluates an exterior form on the exterior product of
  a tuple of vectors. Its determinant formula identifies degree-two exterior forms with
  alternating forms.
* `IsBettiFirstChern c₂ c1`: an additive map `c1 : Pic(A) → H²(A(ℂ), ℚ)` **is the first Chern
  class, up to the global sign convention of `PolarizationForm`**, when, read as an alternating
  form on `H₁` through the cup-normalized comparison `c₂ : ⋀² H¹ ≃ H²`, its value on every pair of
  integral periods is the logarithmic transition-function pairing `chernForm` (the classical
  Riemann form `E_L`) of every nonvanishing exponential section of the line bundle. The zero map
  fails whenever some line bundle has a nonzero Chern form (every ample one). The sign of `c1`
  relative to an oriented geometric Chern class is fixed only by this convention, not asserted
  independently; the polarization that a line bundle induces on the canonical Hodge structure is
  `-chernForm` (see `PolarizationForm`), and every use of `c1` here (divisor spans and the
  statements built on them) is invariant under a global sign. Existence is Milne, *Abelian
  Varieties* (v2.00), Ch. I, §2 and Ex. 13.3, read with this convention.
* `divisorProductSpan c₂ c1 c`: the `ℚ`-span of products of `c` divisor classes, taken in the
  exterior algebra of `H¹` (where `H^{2c} ≃ ⋀^{2c} H¹` is the cup-normalized comparison).

## Étale side

* `CycleClassPredicate`: a predicate on the functoriality packages of cycle class systems selecting
  the *canonical* cycle class map. The library's `CycleClassFunctoriality` does not characterize the
  cycle map (zero satisfies it); the characterization is supplied by the curves interface
  (`AbelianCycleClass`, `EtaleFundamentalClass`). Statements below are parametric in it.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials.AbelianArithmetic

section Betti

open ArithmeticOfJacobiPolynomials.AbelianBettiHodge ArithmeticOfJacobiPolynomials.AbelianBettiChern
  ArithmeticOfJacobiPolynomials.AbelianHodgeClasses
    ArithmeticOfJacobiPolynomials.AbelianBettiCohomology
  ArithmeticOfJacobiPolynomials.ComplexRealization

variable {A : CSch} [GrpObj A] {U : UniformizationData A}

/-- **`c1` is the first Chern class map, up to the global sign convention of `PolarizationForm`**,
`Pic(A) → H²(A(ℂ), ℚ)`: through the cup-normalized comparison `c₂`, its alternating form on
`H₁(A(ℂ), ℚ)` takes, on every pair of integral periods, the value of the transition-function
logarithm pairing `chernForm` (the classical Riemann form `E_L`) of every nonvanishing
exponential section of the line bundle. The induced Hodge polarization is `-chernForm`, and the
sign of `c1` against an oriented geometric Chern class is not pinned by this definition; all
uses of `c1` are invariant under a global sign. -/
def IsBettiFirstChern (c₂ : CupComparison A 2)
    (c1 : Stacks.Picard.ofScheme A.left →+ bettiCohomology A 2) : Prop :=
  ∀ (M : A.left.Modules) (hM : Stacks.Ample.IsInvertibleModule A.left M) (hc : CoversPoints M)
    (s : ExpSection U M), s.NonVanishing → ∀ a b : bettiOne A,
      IsPeriod U (U.period (1 ⊗ₜ[ℚ] a)) → IsPeriod U (U.period (1 ⊗ₜ[ℚ] b)) →
        exteriorPower.pairingDual ℚ (bettiOne A) 2 (hodgeToDual A 2 (c₂.toEquiv.symm (c1
          (Stacks.SheafOfModules.picardClass A.left.presheaf
            (Stacks.RingedSpace.structureIsSheaf A.left.toRingedSpace) M hM))))
          (exteriorPower.ιMulti ℚ 2 ![a, b]) =
          (chernForm (hL := hc) s (U.period (1 ⊗ₜ[ℚ] a)) (U.period (1 ⊗ₜ[ℚ] b)) : ℚ)

/-- The span of the divisor classes, in the exterior algebra of `H¹(A(ℂ), ℚ)`. -/
def divisorSpan (c₂ : CupComparison A 2)
    (c1 : Stacks.Picard.ofScheme A.left →+ bettiCohomology A 2) :
    Submodule ℚ (ExteriorAlgebra ℚ (bettiCohomology A 1)) :=
  Submodule.span ℚ (Set.range fun M => ((c₂.toEquiv.symm (c1 M) : ⋀[ℚ]^2 (bettiCohomology A 1)) :
    ExteriorAlgebra ℚ (bettiCohomology A 1)))

/-- The span of the products of `c` divisor classes, in the exterior algebra of `H¹(A(ℂ), ℚ)`. -/
def divisorProductSpan (c₂ : CupComparison A 2)
    (c1 : Stacks.Picard.ofScheme A.left →+ bettiCohomology A 2) (c : ℕ) :
    Submodule ℚ (ExteriorAlgebra ℚ (bettiCohomology A 1)) :=
  divisorSpan c₂ c1 ^ c

/-- **A Betti cycle class system** on the complex abelian variety `A`, in codimension `c`
(Chow dimension `i`, with `i + c = dim A` in applications): a homomorphism from the Stacks Chow
group
`A_i(A)` to the singular cohomology `H^{2c}(A(ℂ), ℚ)` such that

* `mem_hodge`: every cycle class is a (canonical) Hodge class;
* `divisor_products`: every `ℚ`-linear combination of products of `c` divisor classes
  (first Chern classes `c1`) is the class of a `ℚ`-combination of cycles — the multiplicativity of
  the
  cycle class map (cup product ↔ intersection product) with `cl` of a divisor equal to `c1`.

This is a *characterized interface*: the zero map fails whenever some product of
divisor classes is nonzero (every power of an ample class), and a map into non-Hodge classes fails
`mem_hodge`. Existence for every complex abelian variety is the cited cycle class map of Milne,
*Abelian Varieties* (v2.00), Ch. I Example 13.3 and Fulton, *Intersection Theory*, §19.1
(`BettiCycleClassExists` in `External.lean`). -/
structure BettiCycleClassSystem [LocallyOfFiniteType A.hom] (U : UniformizationData A)
    (c₂ : CupComparison A 2) (c1 : Stacks.Picard.ofScheme A.left →+ bettiCohomology A 2)
    (c : ℕ) (cr : CupComparison A (2 * c)) (i : ℤ) where
  /-- The cycle class map `A_i(A) → H^{2c}(A(ℂ), ℚ)`. -/
  cl : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation ℂ) A.hom i →+
    bettiCohomology A (2 * c)
  mem_hodge : ∀ α, cl α ∈ canonicalHodgeClasses U cr
  divisor_products : ∀ y ∈ divisorProductSpan c₂ c1 c,
    ∃ z ∈ Submodule.span ℚ (Set.range cl),
      ((cr.toEquiv.symm z : ⋀[ℚ]^(2 * c) (bettiCohomology A 1)) :
        ExteriorAlgebra ℚ (bettiCohomology A 1)) = y

/-- **Zariski tangent Lie algebra at `1`** of the Zariski closure in `GL(V)` of a subgroup
`G ≤ GL(V)(ℚ)`, in the coordinates of the basis `b`: the `X ∈ End V` annihilated by the differential
at `1` of every polynomial in the matrix entries vanishing on `G`. This is the Lie algebra of the
`ℚ`-algebraic group whose `ℚ`-points are `G` when `G` is Zariski dense in it (as for `Hdg`, `MT`:
the characterization of these groups in `HodgeGroup`). -/
def zariskiLie {V : Type*} [AddCommGroup V] [Module ℚ V]
    {idx : Type*} [Fintype idx] [DecidableEq idx]
    (b : Module.Basis idx ℚ V) (G : Subgroup (V ≃ₗ[ℚ] V)) : Set (Module.End ℚ V) :=
  {X | ∀ P : MvPolynomial (idx × idx) ℚ,
    (∀ g ∈ G, MvPolynomial.eval
      (fun p => LinearMap.toMatrix b b (g : V →ₗ[ℚ] V) p.1 p.2) P = 0) →
      ∑ p : idx × idx, MvPolynomial.eval (fun p => (1 : Matrix idx idx ℚ) p.1 p.2)
        (MvPolynomial.pderiv p P) * LinearMap.toMatrix b b X p.1 p.2 = 0}

/-- **The `ℂ`-point `p` of `Aℂ` is induced by the `L`-point `x` of `A`** through the embedding
`σ : L → ℂ` over `K`: `p` and `Spec σ ≫ x` agree as morphisms to `A` (`emb : Aℂ → A` is the
base-change morphism). -/
def IsInducedPoint {K : Type} [Field K] [Algebra K ℂ] {L : Type} [Field L] [Algebra K L]
    {A : Over (Spec (.of K))} {Aℂ : CSch} (emb : Aℂ.left ⟶ A.left) (σ : L →ₐ[K] ℂ)
    (x : GroupScheme.GeomPoints K L A) (p : Points Aℂ) : Prop :=
  p.left ≫ emb = Spec.map (CommRingCat.ofHom (σ : L →+* ℂ)) ≫
    (GroupScheme.GeomPoints.toHom K L A x).left

/-- A morphism from a complex base change to an abelian variety over `K`
preserves the distinguished origins of the two group schemes. -/
def PreservesOrigin {K : Type} [Field K] [Algebra K ℂ]
    {A : Over (Spec (.of K))} [GrpObj A] {Aℂ : CSch} [GrpObj Aℂ]
    (emb : Aℂ.left ⟶ A.left) : Prop :=
  (η[Aℂ]).left ≫ emb =
    Spec.map (CommRingCat.ofHom (algebraMap K ℂ)) ≫ (η[A]).left

/-- **The Betti–Tate comparison, characterized by periods and torsion.** Let `A` be an abelian
variety over a subfield `K ⊂ ℂ`, `Aℂ` a complex abelian variety with a morphism `emb : Aℂ → A` over
`Spec K → …` (the base change), `U` a uniformization of `Aℂ` (`A(ℂ) = Lie A / Λ`, `Λ = H₁(A(ℂ), ℤ)`
via the period isomorphism, Milne, *Abelian Varieties* (v2.00), Ch. I, Prop. 2.1 and Thm. 2.3), `σ`
an embedding of an algebraic closure `L` of `K` into `ℂ`, `ℓ` a prime, `bV` a basis of
`V = H₁(A(ℂ), ℚ)` and `bW` a basis of `V_ℓ(A) = T_ℓ(A(L)) ⊗ ℚ_ℓ`. The predicate says `bV i ↦ bW i`
is the canonical isomorphism: for each `i` there are `m ≠ 0` and `t ∈ T_ℓ(A(L))` such that
`m · bV i` is an integral period (`∈ Λ`), `bW i = m⁻¹ · t`, and for every `k` the `ℓ^k`-torsion
point `t_k` of `A(L)` induces on `A(ℂ)` the torsion point `exp(ℓ⁻ᵏ · period(m · bV i))` (the
isomorphism `ℓ⁻ᵏΛ/Λ ≅ A[ℓᵏ]`). Existence for every `A`, `U` and `bV` is
the cited `BettiTateComparisonExists`. -/
def IsBettiTateComparison {K : Type} [Field K] [Algebra K ℂ] {L : Type} [Field L] [Algebra K L]
    {A : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A] {Aℂ : CSch} [GrpObj Aℂ]
    (U : UniformizationData Aℂ) (emb : Aℂ.left ⟶ A.left) (σ : L →ₐ[K] ℂ) (ℓ : ℕ) [Fact ℓ.Prime]
    {n : ℕ} (bV : Module.Basis (Fin n) ℚ (bettiOne Aℂ))
    (bW : Module.Basis (Fin n) ℚ_[ℓ] (rationalTate ℓ (GroupScheme.GeomPoints K L A))) : Prop :=
  ∀ i, ∃ (m : ℕ) (t : Stacks.AbelianGroup.tateModule (GroupScheme.GeomPoints K L A) ℓ),
    m ≠ 0 ∧ IsPeriod U (U.period (1 ⊗ₜ[ℚ] (m • bV i))) ∧
    bW i = ((m : ℚ_[ℓ])⁻¹) • rationalTate.ofTate ℓ _ t ∧
    ∀ k : ℕ, IsInducedPoint emb σ ((t : ℕ → GroupScheme.GeomPoints K L A) k)
      (U.exp ((((ℓ : ℂ) ^ k)⁻¹) • U.period (1 ⊗ₜ[ℚ] (m • bV i))))

/-- Coordinates of a `ℚ`-endomorphism of `V` in the basis `b`, as an `ℚ_ℓ`-endomorphism of
`ℚ_ℓⁿ`. -/
def liftEnd (ℓ : ℕ) [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℚ V) (X : Module.End ℚ V) :
    (Fin n → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin n → ℚ_[ℓ]) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin' ((LinearMap.toMatrix b b X).map (algebraMap ℚ ℚ_[ℓ])))

end Betti

section Etale

open ArithmeticOfJacobiPolynomials.AbelianEtale ArithmeticOfJacobiPolynomials.AbelianCycleClass

/-- A predicate on functoriality packages of cycle class systems, to be instantiated by the
*canonical* (supports-normalized, Kummer-oriented) cycle class map of the curves interface. -/
abbrev CycleClassPredicate : Type _ :=
  ∀ (B : BigEtaleSite.{0}) (ℓ : ℕ) [Fact ℓ.Prime] [EllAdicSite B ℓ] (X : B.Scheme)
    [IsNoetherian X.1] {k : Type} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
    (kbar : Type) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar] [Normal k kbar]
    (c : ℕ) (i : ℤ), CycleClassFunctoriality B ℓ X f kbar c i → Prop

end Etale

end ArithmeticOfJacobiPolynomials.AbelianArithmetic
