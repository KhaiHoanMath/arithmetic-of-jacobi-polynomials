/- Assembled by AxiomProver. -/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.GlobalPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.Flag
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagPurityProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagAffineSpace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopDegreeFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerNondivisibleReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointClassLevelSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointClassReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyPointClassProof

/-!
# Fundamental classes with supports: purity classes and their Kummer normalisation

The cycle class map `cl : CH^c(X) → H^{2c}_{ét}(X, ℚ_ℓ(c))` of Corollary 6.6 has
to be the *fundamental class* map: the class of an integral closed subscheme `Z ⊆ X` is the image
in `H^{2c}(X)` of a generator of the group `H^{2c}_Z(X) = Ext^{2c}_X(i_* Λ_Z, Λ_X)` of classes with
supports.  The Stacks library constructs the supports-level objects for smooth pairs
at the coefficient ring `Λ = ℤ/ℓ`:

* `Stacks.EtaleCohomology.IsPurityClass` (`Purity/LocalPurity`, `Duality/DenseOpenSmoothDuality`):
  a class `γ ∈ Ext^c_Y(i_* Λ_T, Λ_Y)` with `Ext^q_T(G, Λ_T) ≅ Ext^{q+c}_Y(i_* G, Λ_Y)`,
  `y ↦ i_*(y) ∘ γ`, bijective for every `G`, `q`, and `Ext^q_Y(i_* G, Λ_Y) = 0` for `q < c`;
* `Stacks.EtaleCohomology.Purity.exists_isPurityClass_of_smooth`: a purity class of degree `2c`
  exists for every closed immersion of smooth `k`-schemes of relative codimension `c` over an
  algebraically closed field `k` (SGA 4 XVI 3.7, via the local and gluing
  steps of `Purity/GlobalPurity`);
* `Stacks.EtaleCohomology.KummerFlag.kummerFlagClass` and
  `Stacks.EtaleCohomology.KummerFlag.kummerFlagPurity`: the canonical (no scalar ambiguity)
  *Kummer-normalised* class of a point of a smooth scheme over an algebraically closed field,
  built from the Kummer coboundary of the coordinate functions and Yoneda composition along the
  flag of coordinate hyperplanes, and its proof that it is a purity class of the point.

A purity class is determined only up to a unit of `ℤ/ℓ`.  This file records, for arbitrary
closed immersions and arbitrary data:

* `IsFundamentalClass`: purity class of degree `2c` — the *support/Ext normalisation*;
* `exists_isFundamentalClass_of_smooth`: existence for every smooth closed pair;
* `IsPurityClass.ne_zero`: **the zero class is never a purity class of a nonempty subscheme**
  (so the zero system fails the characterisation on every point, divisor, …);
* `IsPurityClass.exists_unit_smul`: two purity classes of a connected subscheme differ by a unit
  of `ℤ/ℓ` — the ambiguity that Kummer normalisation removes;
* `compClass`, `IsPurityClass.compClass`: purity classes compose along flags
  `T ⊆ Y ⊆ X` (transitivity of Gysin classes);
* `kummerNormalisedClass` and its properties: for every étale coordinate chart `ψ : U → 𝔸^d`
  centred at a point `y`, the Kummer flag class, transported to `i_* Λ_T`, is a purity class, is
  nonzero, and every purity class of the point is a unit multiple of it; it depends on the chart
  and on the primitive root `ζ` only, never on a choice of unit;

The statements that are not in the library are recorded, with their locators, in
`External.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace ArithmeticOfJacobiPolynomials.EtaleFundamentalClass

attribute [local instance] moduleCat_hasLimitsOfSize
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Purity

/-- **A fundamental class of the closed immersion `i : T ⟶ Y`, of codimension `c`**: a class
`γ ∈ H^{2c}_T(Y, Λ) = Ext^{2c}_Y(i_* Λ_T, Λ_Y)`, `Λ = ℤ/ℓ`, such that `y ↦ i_*(y) ∘ γ` is a
bijection `Ext^q_T(G, Λ_T) ≅ Ext^{q+2c}_Y(i_* G, Λ_Y)` for every sheaf `G` and every `q`, and
`Ext^q_Y(i_* G, Λ_Y) = 0` for `q < 2c`.  This is the library's `IsPurityClass`. -/
def IsFundamentalClass {T Y : Scheme.{u}} (i : T ⟶ Y) [IsClosedImmersion i] (c : ℕ)
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
      (unitSheaf (X := Y) ℓ) (2 * c)) : Prop :=
  IsPurityClass i (unitSheaf (X := Y) ℓ) γ

/-- **Existence of fundamental classes of smooth closed pairs** (SGA 4 XVI 3.7; the library's
`Purity.exists_isPurityClass_of_smooth`): for `Y` smooth of relative
dimension `d + c` over an algebraically closed field `k`, `ℓ` a prime invertible in `k` and
`i : T ⟶ Y` a closed immersion of a quasi-compact `T` smooth of relative dimension `d`, there is a
fundamental class of degree `2c`.  Nothing is specialised: this is the library theorem. -/
theorem exists_isFundamentalClass_of_smooth (k : Type u) [Field k] [IsAlgClosed k]
    (hℓ : IsUnit (ℓ : k)) (Y T : Scheme.{u}) (p : Y ⟶ Spec (.of k)) (i : T ⟶ Y)
    [IsClosedImmersion i] (d c : ℕ) [SmoothOfRelativeDimension (d + c) p]
    [SmoothOfRelativeDimension d (i ≫ p)] [CompactSpace T] :
    ∃ γ, IsFundamentalClass (ℓ := ℓ) i c γ :=
  Purity.exists_isPurityClass_of_smooth k ℓ hℓ Y T p i d c

/-- **The zero class is never a purity class of a nonempty subscheme**: taking `G = Λ_T`, `q = 0`,
the Gysin map sends `id_{Λ_T}` to `γ`; if `γ = 0` the Gysin map vanishes, so injectivity forces
`id_{Λ_T} = 0`, which is false for `T ≠ ∅`.  In particular the zero assignment fails the
characterisation of fundamental classes on every point, every divisor, every nonempty `Z ⊆ X`. -/
theorem _root_.Stacks.EtaleCohomology.IsPurityClass.ne_zero {T Y : Scheme.{u}} {i : T ⟶ Y}
    [IsClosedImmersion i] [Nonempty T] {A : EtaleModules.{u, 0} (ZMod ℓ) Y} {c : ℕ}
    {γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) A c}
    (hγ : IsPurityClass i A γ) : γ ≠ 0 := by
  intro h0
  have : Fact (1 < ℓ) := ⟨(Fact.out : ℓ.Prime).one_lt⟩
  have hinj := (hγ.1 (unitSheaf (X := T) ℓ) 0).1
  have h1 : (fun y : Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 0 =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ
        (rfl : 0 + c = 0 + c)) (Ext.mk₀ (𝟙 _)) =
      (fun y : Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 0 =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ
        (rfl : 0 + c = 0 + c)) (Ext.mk₀ 0) := by
    simp only [h0, Ext.comp_zero]
  have h2 := (Ext.mk₀_bijective _ _).1 (hinj h1)
  exact KummerFlag.id_unitSheaf_ne_zero T h2

/-- **Purity classes of a connected subscheme are unique up to a unit of `ℤ/ℓ`.**  If `γ`, `γ'`
are purity classes of the same degree for `i : T ⟶ Y` with `T` irreducible, then
`γ' = (r · id_{Λ_T}) ∘ γ` for a unit `r ∈ (ℤ/ℓ)ˣ` (the Gysin map at `Λ_T` is bijective in degree
zero, and `End(Λ_T) = ℤ/ℓ`).  This is the ambiguity of a bare existence statement; the Kummer
normalisation below removes it. -/
theorem _root_.Stacks.EtaleCohomology.IsPurityClass.exists_unit_smul {T Y : Scheme.{u}}
    {i : T ⟶ Y} [IsClosedImmersion i] [IrreducibleSpace T] {c : ℕ}
    {γ γ' : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
      (unitSheaf (X := Y) ℓ) c}
    (hγ : IsPurityClass i (unitSheaf (X := Y) ℓ) γ)
    (hγ' : IsPurityClass i (unitSheaf (X := Y) ℓ) γ') :
    ∃ r : ZMod ℓ, IsUnit r ∧ γ' = (Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).map
      (r • 𝟙 (unitSheaf (X := T) ℓ)))).comp γ (zero_add c) := by
  have hF := hγ.isPurityClassFun
  obtain ⟨u, hu⟩ := (hF.1 (unitSheaf (X := T) ℓ) 0 c (zero_add c)).2 γ'
  obtain ⟨v, rfl⟩ := (Ext.mk₀_bijective _ _).2 u
  obtain ⟨r, rfl⟩ := Purity.exists_eq_smul_id_unitSheaf T v
  simp only [Ext.mapExactFunctor_mk₀] at hu
  refine ⟨r, ?_, hu.symm⟩
  rcases eq_or_ne r 0 with rfl | hr
  · exfalso
    obtain ⟨t, -⟩ := (IrreducibleSpace.isIrreducible_univ T).nonempty
    have : Nonempty T := ⟨t⟩
    refine hγ'.ne_zero ?_
    rw [← hu, zero_smul, Functor.map_zero, Ext.mk₀_zero, Ext.zero_comp]
  · exact hr.isUnit

end Purity

section Flags

variable {T Y X : Scheme.{u}} (i' : T ⟶ Y) (i : Y ⟶ X) [IsClosedImmersion i'] [IsClosedImmersion i]

/-- **The composite class along a flag `T ⊆ Y ⊆ X`**: for `γ ∈ Ext^n_Y(i'_* Λ_T, Λ_Y)` and
`δ ∈ Ext^m_X(i_* Λ_Y, Λ_X)`, `i_*(γ) ∘ δ ∈ Ext^{n+m}_X((i' ≫ i)_* Λ_T, Λ_X)`. -/
def compClass {n m : ℕ}
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := T) ℓ))
      (unitSheaf (X := Y) ℓ) n)
    (δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Y) ℓ))
      (unitSheaf (X := X) ℓ) m) :
    Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i' ≫ i)).obj (unitSheaf (X := T) ℓ))
      (unitSheaf (X := X) ℓ) (n + m) :=
  (Ext.mk₀ ((etaleModuleDirectImageComp.{u, 0} (ZMod ℓ) i' i (i' ≫ i) rfl).inv.app
    (unitSheaf (X := T) ℓ))).comp
      ((γ.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp δ rfl)
      (zero_add _)

/-- **Transitivity of purity classes along flags**: the composite of purity classes of
`T ⊆ Y` and `Y ⊆ X` is a purity class of `T ⊆ X`, in degree the sum. -/
theorem IsPurityClass.compClass {n m : ℕ}
    {γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := T) ℓ))
      (unitSheaf (X := Y) ℓ) n}
    {δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Y) ℓ))
      (unitSheaf (X := X) ℓ) m}
    (hγ : IsPurityClass i' (unitSheaf (X := Y) ℓ) γ)
    (hδ : IsPurityClass i (unitSheaf (X := X) ℓ) δ) :
    IsPurityClass (i' ≫ i) (unitSheaf (X := X) ℓ) (compClass i' i γ δ) :=
  (((hγ.isPurityClassFun).comp (hδ.isPurityClassFun)).ofIso
    (etaleModuleDirectImageComp.{u, 0} (ZMod ℓ) i' i (i' ≫ i) rfl)).isPurityClass

end Flags

section Kummer

open Stacks.EtaleCohomology.KummerFlag

variable {K : Type u} [Field K]

/-- **The Kummer-normalised class of a flag of divisor data, read on `i_* Λ_T`.**  For divisor data
`D = (D_0, …, D_{d-1})` on `U` over `K`, a primitive `ℓ`-th root of unity `ζ` and an isomorphism
`e : E_0 ⋯ E_{d-1} Λ_U ≅ i_* Λ_T` of the flag sheaf with the direct image from a closed `T`, this is
`e⁻¹ ∘ γ_Kummer` for the library's Kummer flag class `γ_Kummer`
(`Stacks.EtaleCohomology.KummerFlag.kummerFlagClass`: Yoneda composite of the Kummer divisor
classes `δ(a_m) = (j_! κ(a_m)) ∘ [0 → j_! j⁻¹ Λ → Λ → i_* i⁻¹ Λ → 0]`).  It involves no choice
of a unit: it depends only on `ζ` and on the units `a_m`. -/
def kummerNormalisedClass {U T : Scheme.{u}} (fU : U ⟶ Spec (.of K)) {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K)) {d : ℕ} (D : Fin d → DivisorDatum U)
    (i : T ⟶ U)
    (e : flagSheaf (N := ℓ) D ≅
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) :
    Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
      (unitSheaf (X := U) ℓ) (2 * d) :=
  (Ext.mk₀ e.inv).comp (kummerFlagClass hζ hℓ fU D) (zero_add _)

/-- **Kummer normalisation selects one purity class.**  If the Kummer-normalised class of a flag
is a purity class of an irreducible closed `T` (as it is for étale charts,
`kummerChart_isFundamentalClass`), then it is nonzero, and every purity class of `T` of the same
degree is a unit multiple of it.  Thus the set of purity classes is a `(ℤ/ℓ)ˣ`-torsor, of which the
Kummer class is a distinguished element fixed by `ζ` and the coordinate functions. -/
theorem kummerNormalisedClass_properties {U T : Scheme.{u}} (fU : U ⟶ Spec (.of K)) {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K)) {d : ℕ} (D : Fin d → DivisorDatum U)
    (i : T ⟶ U) [IsClosedImmersion i] [IrreducibleSpace T]
    (e : flagSheaf (N := ℓ) D ≅
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
    (h : IsFundamentalClass i d (kummerNormalisedClass fU hζ hℓ D i e)) :
    kummerNormalisedClass fU hζ hℓ D i e ≠ 0 ∧
      ∀ γ' : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
          (unitSheaf (X := U) ℓ) (2 * d),
        IsFundamentalClass i d γ' →
          ∃ r : ZMod ℓ, IsUnit r ∧ γ' = (Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).map
            (r • 𝟙 (unitSheaf (X := T) ℓ)))).comp (kummerNormalisedClass fU hζ hℓ D i e)
              (zero_add _) := by
  obtain ⟨t, -⟩ := (IrreducibleSpace.isIrreducible_univ T).nonempty
  have : Nonempty T := ⟨t⟩
  exact ⟨IsPurityClass.ne_zero h, fun γ' hγ' => IsPurityClass.exists_unit_smul h hγ'⟩

variable [IsAlgClosed K]

/-- **Kummer-normalised fundamental classes of points on étale charts** (a consequence of the
library's `Stacks.EtaleCohomology.KummerFlag.kummerFlagPurity`).  Let `K` be algebraically closed,
`ℓ` a prime invertible in `K`, `ζ` a primitive `ℓ`-th root of unity, `U` affine irreducible over
`K` and `ψ : U ⟶ 𝔸^d_K` étale whose coordinate functions vanish simultaneously exactly at one point
`y`.  Then the canonical map `Λ_U → E_0 ⋯ E_{d-1} Λ_U` is nonzero, and there are a closed immersion
`i : T ⟶ U` of a point (irreducible, étale over `K`) and an isomorphism `e` of the flag sheaf with
`i_* Λ_T` such that the Kummer-normalised class is a fundamental class of `i` of degree `2d`
(support/Ext normalisation), it is nonzero, and every fundamental class of `i` is a unit
multiple of it.  The **zero system therefore fails on every point**. -/
theorem kummerChart_isFundamentalClass (U : Scheme.{u}) [IsAffine U] [IrreducibleSpace U]
    (fU : U ⟶ Spec (.of K)) (d : ℕ) (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K)))
    (hψe : Etale ψ) (hψ : ψ ≫ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) = fU)
    (y : U)
    (hy : ∀ x : U, (∀ m : Fin d, x ∉ U.basicOpen
        (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ↔ x = y)
    {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K)) :
    flagUnit (N := ℓ) (fun m => functionDatum
        (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ≠ 0 ∧
      ∃ (T : Scheme.{u}) (i : T ⟶ U) (_ : IsClosedImmersion i) (_ : IrreducibleSpace T)
        (_ : SmoothOfRelativeDimension 0 (i ≫ fU))
        (e : flagSheaf (N := ℓ) (fun m => functionDatum
            (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ≅
          (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)),
        IsFundamentalClass i d (kummerNormalisedClass fU hζ hℓ (fun m => functionDatum
          (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) i e) ∧
        kummerNormalisedClass fU hζ hℓ (fun m => functionDatum
          (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) i e ≠ 0 ∧
        ∀ γ' : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
            (unitSheaf (X := U) ℓ) (2 * d),
          IsFundamentalClass i d γ' →
            ∃ r : ZMod ℓ, IsUnit r ∧ γ' = (Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).map
              (r • 𝟙 (unitSheaf (X := T) ℓ)))).comp (kummerNormalisedClass fU hζ hℓ
                (fun m => functionDatum
                  (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) i e)
                (zero_add _) := by
  obtain ⟨hflag, T, i, hi, hT, hTs, e, hpur⟩ :=
    kummerFlagPurity (K := K) ℓ U fU d ψ hψe hψ y hy hζ hℓ
  exact ⟨hflag, T, i, hi, hT, hTs, e, hpur,
    kummerNormalisedClass_properties fU hζ hℓ _ i e hpur⟩

end Kummer

section RationalPoint

open Stacks.Frobenius

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (kbar : Type u)
  [Field kbar] [Algebra k kbar] (d : ℕ)

/-- **The Kummer point class of a rational point of a connected smooth proper variety is not
divisible by `ℓ`, at every level `ℓⁿ⁺¹`** (`RationalPointKummerClassNondivisible`), *proved*: the
library reduces it to three statements, all of which are theorems of the library —
the top-degree point class generates `H^{2d}(Y, ℤ/ℓ)` (`topCohomologyPointClass`), the Kummer
flag class of an étale chart is a purity class of its centre (`kummerFlagPurity`), and the
compatibility of Kummer point classes with reduction of the level
(`kummerPointClassReductionSquare`).  Here `Y = X_{k̄}` is connected and smooth of relative
dimension `d`, and the Kummer point class is the cycle class of the rational point `x = s(pt)`
computed in `H^{2d}(X_{k̄}, ℤ/ℓⁿ⁺¹)` from any étale chart centred at `x`, through the adapted map.
In particular the Kummer-normalised point classes, which form a compatible system in `n`
(`kummerPointClassReductionSquare`), are *nonzero modulo ℓ*, so the zero system fails on points
at every `ℓ`-power level. -/
theorem rationalPointKummerClassNondivisible [IsAlgClosed kbar] [IsProper f]
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar)) :
    RationalPointKummerClassNondivisible f kbar ℓ d :=
  rationalPointKummerClassNondivisible_of_kummerFlagPurity f kbar ℓ d hℓ
    (topCohomologyPointClass ℓ kbar hℓ) (KummerFlag.kummerFlagPurity kbar ℓ)
    (KummerFlag.kummerPointClassLevelReduction_of_reductionSquare _ _
      (KummerFlag.kummerPointClassReductionSquare _ _))

end RationalPoint

section PointDatum

open Stacks.Frobenius

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (kbar : Type u)
  [Field kbar] [Algebra k kbar] (ℓ d n : ℕ)

/-- **The geometric data computing the finite-level class of a rational point** (the data
quantified over in the library's `RationalPointKummerClassNondivisible`): a `k`-rational point `s`
of `X` (a closed immersion splitting `f`), an affine open `V ∋ s` with an étale map
`π : V ⟶ 𝔸^d_k` whose coordinates vanish simultaneously exactly at `s`, and a map
`z : Λ_{X_{k̄}} ⟶ n_!(E_0 ⋯ E_{d-1} Λ)` adapted to the canonical one (level `ℓⁿ⁺¹`), through which
the Kummer point class is read.  Nothing is specialised: `X`, `k`, `k̄`, `ℓ`, `d`, `n` are
arbitrary. -/
structure KummerPointDatum where
  /-- The rational point. -/
  s : Spec (.of k) ⟶ X
  [isClosedImmersion : IsClosedImmersion s]
  section_eq : s ≫ f = 𝟙 _
  /-- The affine open containing the point. -/
  V : X.Opens
  hV : IsAffineOpen V
  /-- The étale coordinates. -/
  π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k))
  etale : Etale π
  comp : π ≫ (𝔸(ULift.{u} (Fin d); Spec (.of k)) ↘ Spec (.of k)) = V.ι ≫ f
  mem : ∃ v : V, V.ι.base v ∈ Set.range s.base
  zeroLocus : ∀ v : V, (∀ m : Fin d, v ∉ V.toScheme.basicOpen
      (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))) ↔
    V.ι.base v ∈ Set.range s.base
  /-- The map `Λ_{X_{k̄}} ⟶ n_!(E_0 ⋯ E_{d-1} Λ)`. -/
  z : unitSheaf (X := fieldBaseChange (Over.mk f) kbar) (ℓ ^ (n + 1)) ⟶
    (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι).obj
      (KummerFlag.flagSheaf (N := ℓ ^ (n + 1)) (chartDatum f kbar d V hV π))
  adapted : KummerFlag.IsAdapted (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι
    (KummerFlag.flagUnit (N := ℓ ^ (n + 1)) (chartDatum f kbar d V hV π)) z

attribute [instance] KummerPointDatum.isClosedImmersion

variable {f kbar ℓ d n}

/-- **The Kummer-normalised finite-level fundamental class of the point**, in
`H^{2d}(X_{k̄}, ℤ/ℓⁿ⁺¹) = Ext^{2d}(Λ, Λ)`, for a primitive `ℓⁿ⁺¹`-th root of unity `ζ ∈ k̄`: the
library's `KummerFlag.kummerPointClass` through the adapted map `z`. -/
noncomputable def KummerPointDatum.kummerClass (D : KummerPointDatum f kbar ℓ d n) {ζ : kbar}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ (n + 1))) (hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar)) :
    Ext (unitSheaf (X := fieldBaseChange (Over.mk f) kbar) (ℓ ^ (n + 1)))
      (unitSheaf (X := fieldBaseChange (Over.mk f) kbar) (ℓ ^ (n + 1))) (2 * d) :=
  KummerFlag.kummerPointClass hζ hN (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
    (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ D.V).ι (chartDatum f kbar d D.V D.hV D.π) D.z

/-- **The Kummer point class is nonzero** (at every level `ℓⁿ⁺¹`), granted the library's
`RationalPointKummerClassNondivisible` (a theorem of the library for connected smooth proper
`X_{k̄}` over an algebraically closed `k̄`, `rationalPointKummerClassNondivisible`): it is not
`ℓ` times any class, in particular not `ℓ · 0`.  So **the zero system fails the normalisation on
every rational point of such a variety**. -/
theorem KummerPointDatum.kummerClass_ne_zero (hnd : RationalPointKummerClassNondivisible f kbar ℓ d)
    (D : KummerPointDatum f kbar ℓ d n) {ζ : kbar} (hζ : IsPrimitiveRoot ζ (ℓ ^ (n + 1)))
    (hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar)) : D.kummerClass hζ hN ≠ 0 := by
  intro h0
  refine hnd n hζ hN D.s D.section_eq D.V D.hV D.π D.etale D.comp D.mem D.zeroLocus D.z D.adapted
    ⟨0, ?_⟩
  rw [smul_zero]
  exact h0

end PointDatum

end ArithmeticOfJacobiPolynomials.EtaleFundamentalClass
