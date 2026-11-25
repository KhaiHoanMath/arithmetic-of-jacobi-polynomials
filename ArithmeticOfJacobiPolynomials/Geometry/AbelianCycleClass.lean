/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianEtaleCohomology
public import ArithmeticOfJacobiPolynomials.Geometry.ChowGaloisDescent
public import ArithmeticOfJacobiPolynomials.Geometry.EtaleFundamentalClass
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Functorial cycle classes and rational descent (Corollary 6.6)

Corollary 6.6 asserts that the cycle class map
`CH^c((J^h)_K) ⊗ ℚ_ℓ → H^{2c}_{ét}((J^h)_{Q̄}, ℚ_ℓ(c))^{Gal(Q̄/K)}` is surjective, the last step
of the proof being: *a Galois-invariant class represented by algebraic cycles over a finite
extension descends with rational coefficients by averaging over a finite Galois extension.*

This file states and proves that step for an arbitrary proper
`k`-scheme `X` and arbitrary `(c, i)`:

* the target is `ArithmeticOfJacobiPolynomials.AbelianEtale.etaleCohomologyTwistSpace`, the Stacks
`ℓ`-adic
  cohomology `H^{2c}_{ét}(X_{k̄}, ℚ_ℓ)` of a proper `k`-scheme, twisted by `ℚ_ℓ(c)`, with its
  Galois representation `etaleCohomologyTwistRep`
  (`ArithmeticOfJacobiPolynomials/Geometry/AbelianEtaleCohomology.lean`; its underlying
  `ℤ_ℓ`-module is the
  library's `geometricCompactlySupportedCohomology`, `galoisCohomologyForgetIso`);
* the source is the Stacks Chow group `A_i(X)` (and `A_i(X_E)` for finite subextensions `E ⊂ k̄`,
  over `Spec k`).

## What `CycleClassFunctoriality` is, and what it is not

`CycleClassFunctoriality` is **only the functoriality package** of a family of homomorphisms
`cl_E : A_i(X_E) → H^{2c}_{ét}(X_{k̄}, ℚ_ℓ(c))`: compatibility with the flat pullback
`π^* : A_i(X) → A_i(X_E)`, equivariance for `Aut(E/k)`, and invariance of `cl_k`.  **It does not
characterise the cycle class map**: the zero maps satisfy every field.  It is the
interface used by the descent argument.  The cycle class map itself
(`cl(Z)` the fundamental class of a subvariety, normalised by Kummer classes of divisors and
trace-one classes of points, multiplicative for the intersection product) is **not** constructed
in the Stacks project, which has Chow groups (`Stacks.Chow`), the purity class of a smooth pair
over an algebraically closed field with `ℤ/ℓ` coefficients
(`Stacks.EtaleCohomology.Purity.exists_isPurityClass_of_smooth`, SGA 4 XVI 3.7), the Kummer class
of a divisor (`Stacks.EtaleCohomology.Purity.kummerDivisorSection`)
and the trace of a smooth proper curve (`Stacks.Kummer.smoothProperCurveTrace`, Tags 03RM, 03RQ),
but no `ℓ`-adic
cohomology with supports and Galois action, no trace in all dimensions, and no cycle class in all
codimensions.  The full statement that would have to be cited for the existence of a
`CycleClassFunctoriality` that *is* the cycle class map, with its locators, is recorded in
`External.lean`.  The supports-level objects that *do* pin down
fundamental classes — purity classes, Kummer-normalised point classes, the proved
non-divisibility of Kummer point classes at every `ℓ`-power level — are in
`ArithmeticOfJacobiPolynomials/Geometry/EtaleFundamentalClass.lean`.

## What is proved here

* `trace_formula`: `cl_k(π_* δ) = ∑_{σ ∈ Gal(E/k)} σ̃ · cl_E(δ)` (the lifts `σ̃ ∈ Gal(k̄/k)`),
  from the two functorialities and the **proved** Chow-level Mackey formula
  `π^* π_* = ∑_σ σ` (`ArithmeticOfJacobiPolynomials.ChowGaloisDescent.mackeyFormula`, on the
  Stacks Chow
  groups, for every finite Galois `E/k` and every `X` locally of finite type, proper over `k`);
* `mem_span_range_clBase_of_invariant`: a `Gal(k̄/k)`-invariant vector of the span of the classes of
  cycles on `X_E` lies in the span of the classes of cycles on `X` (the averaging step, with the
  Stacks transfer of `ArithmeticOfJacobiPolynomials.Algebra.CycleDescent`);
* `span_range_clBase_eq_invariants`: the surjectivity `cl ⊗ ℚ_ℓ ↠ H^{2c}(…)^{Gal}` of Corollary 6.6
  from the Tate statement over finite extensions; the Mackey formula is proved.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow Stacks.EtaleCohomology

universe u

namespace ArithmeticOfJacobiPolynomials

namespace AbelianCycleClass

open AbelianEtale

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [EllAdicSite B ℓ]
  (X : B.Scheme) [IsNoetherian X.1]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar] [Normal k kbar]
  (c : ℕ) (i : ℤ)

/-- **The functoriality package of a system of cycle class maps** for the proper `k`-scheme `X`
in codimension `c` (dimension index `i`): homomorphisms `cl_k` for `X` and `cl_E` for `X_E`
(`E ⊂ k̄` finite), with values in `H^{2c}_{ét}(X_{k̄}, ℚ_ℓ(c))` (for `X_E` this uses the canonical
identification `(X_E)_{k̄} = X_{k̄}`), satisfying the functorialities of the cycle class map.
This does **not** pin down the cycle class map (zero satisfies it); see the module docstring.

* `cl_piStar`: compatibility with the flat pullback `π^* : A_i(X) → A_i(X_E)`;
* `cl_galoisPushforward`: compatibility with the isomorphisms `1 × Spec σ` of `X_E` (`σ ∈ Aut(E/k)`
  lifted to `Gal(k̄/k)`): `σ̃ · cl_E(a) = cl_E(σ · a)`;
* `clBase_invariant`: the class of a cycle defined over `k` is `Gal(k̄/k)`-invariant. -/
structure CycleClassFunctoriality where
  /-- The cycle class map of `X`. -/
  clBase : chowGroup (fieldChowSituation k) f i →+ etaleCohomologyTwistSpace B ℓ X f kbar c
  /-- The cycle class map of `X_E`, for a finite subextension `E ⊂ k̄`. -/
  cl : ∀ (E : IntermediateField k kbar) [FiniteDimensional k E],
    Chow.galoisChowGroup E f i →+ etaleCohomologyTwistSpace B ℓ X f kbar c
  cl_piStar : ∀ (E : IntermediateField k kbar) [FiniteDimensional k E]
    (α : chowGroup (fieldChowSituation k) f i),
    cl E (ChowGaloisDescent.piStar E f i α) = clBase α
  cl_galoisPushforward : ∀ (E : IntermediateField k kbar) [FiniteDimensional k E] [Normal k E]
    (σ : kbar ≃ₐ[k] kbar) (a : Chow.galoisChowGroup E f i),
    etaleCohomologyTwistRep B ℓ X f kbar c σ (cl E a) =
      cl E (Chow.galoisPushforward E f (AlgEquiv.restrictNormalHom E σ) i a)
  clBase_invariant : ∀ (σ : kbar ≃ₐ[k] kbar) (α : chowGroup (fieldChowSituation k) f i),
    etaleCohomologyTwistRep B ℓ X f kbar c σ (clBase α) = clBase α

variable {B ℓ X f kbar c i}

/-- The finite group `Aut(E/k)` of a finite subextension. -/
noncomputable instance instFintypeAut (E : IntermediateField k kbar) [FiniteDimensional k E] :
    Fintype (E ≃ₐ[k] E) :=
  Fintype.ofFinite _

section Descent

variable (S : CycleClassFunctoriality B ℓ X f kbar c i) (E : IntermediateField k kbar)
  [FiniteDimensional k E] [IsGalois k E]

/-- Lifts `σ̃ ∈ Gal(k̄/k)` of the elements `σ ∈ Aut(E/k)`: a section of the surjection
`Gal(k̄/k) ↠ Gal(E/k)` (`k̄/k` normal). -/
noncomputable def galoisLift : (E ≃ₐ[k] E) → (kbar ≃ₐ[k] kbar) :=
  Function.surjInv (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E) kbar)

omit [Algebra.IsSeparable k kbar] [FiniteDimensional k E] in
theorem restrictNormalHom_galoisLift (σ : E ≃ₐ[k] E) :
    AlgEquiv.restrictNormalHom E (galoisLift E σ) = σ :=
  Function.surjInv_eq (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E) kbar) σ

/-- **The trace formula** `cl_k(π_* δ) = ∑_{σ ∈ Gal(E/k)} σ̃ · cl_E(δ)` for the transfer
`π_* : A_i(X_E) → A_i(X)` and the functorial cycle classes `S`, from the proved Mackey formula
`π^* π_* = ∑_σ σ` for `E/k` (`ArithmeticOfJacobiPolynomials.ChowGaloisDescent.mackeyFormula`). -/
theorem CycleClassFunctoriality.trace_formula (δ : Chow.galoisChowGroup E f i) :
    S.clBase (Chow.baseChangePushforward E f i δ) =
      ∑ σ : E ≃ₐ[k] E, etaleCohomologyTwistRep B ℓ X f kbar c (galoisLift E σ) (S.cl E δ) := by
  rw [← S.cl_piStar E, ChowGaloisDescent.mackeyFormula E f i δ]
  unfold Chow.galoisNorm
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [S.cl_galoisPushforward E (galoisLift E σ), restrictNormalHom_galoisLift]

/-- **Rational descent of invariant cycle classes (Corollary 6.6, last sentence of the proof).**
Let `E ⊂ k̄` be a finite Galois subextension of `k`.  A vector of
`H^{2c}_{ét}(X_{k̄}, ℚ_ℓ(c))` invariant under `Gal(k̄/k)` and lying in the `ℚ_ℓ`-span of the classes
of cycles on `X_E` lies in the `ℚ_ℓ`-span of the classes of cycles on `X` itself: it is the
average `[E : k]^{-1} ∑_σ σ̃ · w` of its conjugates, each of which is `cl_k(π_* δ)` for the transfer
`π_*` of a cycle class `δ` of `X_E`. -/
theorem CycleClassFunctoriality.mem_span_range_clBase_of_invariant
    {w : etaleCohomologyTwistSpace B ℓ X f kbar c}
    (hw : w ∈ (etaleCohomologyTwistRep B ℓ X f kbar c).invariants)
    (hwE : w ∈ Submodule.span ℚ_[ℓ] (Set.range (S.cl E))) :
    w ∈ Submodule.span ℚ_[ℓ] (Set.range S.clBase) := by
  refine CycleDescent.span_range_descent S.clBase (S.cl E) (Chow.baseChangePushforward E f i)
    (etaleCohomologyTwistRep B ℓ X f kbar c) (galoisLift E) ?_ (S.trace_formula E) hw hwE
  have : 0 < Fintype.card (E ≃ₐ[k] E) := Fintype.card_pos
  exact Nat.cast_ne_zero.mpr this.ne'

end Descent

section Surjectivity

variable (S : CycleClassFunctoriality B ℓ X f kbar c i)

/-- **Surjectivity of the cycle class map onto the invariants (Corollary 6.6).**  Suppose
the Tate statement holds over finite extensions: every `Gal(k̄/k)`-invariant vector of
`H^{2c}_{ét}(X_{k̄}, ℚ_ℓ(c))` is a `ℚ_ℓ`-linear combination of classes of cycles on some `X_E`.
Then the `ℚ_ℓ`-span of the classes of cycles on `X` is exactly the invariants, i.e.
`CH(X) ⊗ ℚ_ℓ → H^{2c}(…)^{Gal(k̄/k)}` is surjective. -/
theorem span_range_clBase_eq_invariants
    (hTate : ∀ w ∈ (etaleCohomologyTwistRep B ℓ X f kbar c).invariants,
      ∃ (E : IntermediateField k kbar) (_ : FiniteDimensional k E) (_ : Normal k E),
        w ∈ Submodule.span ℚ_[ℓ] (Set.range (S.cl E))) :
    Submodule.span ℚ_[ℓ] (Set.range S.clBase) =
      (etaleCohomologyTwistRep B ℓ X f kbar c).invariants := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨α, rfl⟩ σ
    exact S.clBase_invariant σ α
  · intro w hw
    obtain ⟨E, _, _, hwE⟩ := hTate w hw
    have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E kbar
    have : IsGalois k E := ⟨⟩
    exact S.mem_span_range_clBase_of_invariant E hw hwE

end Surjectivity

section Geometric

open Opposite CategoryTheory.Abelian ArithmeticOfJacobiPolynomials.EtaleFundamentalClass

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

/-- The unit `χ^c` of `ℚ_ℓ` times the image of `(χ⁻¹)^c` is `1`, for a unit `χ` of `ℤ_ℓ`. -/
theorem algebraMap_units_pow_mul_inv_pow (u : ℤ_[ℓ]ˣ) (c : ℕ) :
    ((((Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom u) ^ c : ℚ_[ℓ]ˣ)) : ℚ_[ℓ]) *
      algebraMap ℤ_[ℓ] ℚ_[ℓ] ((u⁻¹ ^ c : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := by
  rw [← map_pow (Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom) u c]
  change algebraMap ℤ_[ℓ] ℚ_[ℓ] ((u ^ c : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) *
      algebraMap ℤ_[ℓ] ℚ_[ℓ] ((u⁻¹ ^ c : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1
  rw [← map_mul, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one, map_one]

/-- A **compatible system of primitive `ℓ`-power roots of unity** `ζ_n ∈ k̄` (`ζ_n` of order
`ℓⁿ⁺¹`, `ζ_{n+1}^ℓ = ζ_n`): a generator of the Tate module `ℤ_ℓ(1)` of `k̄`.  It fixes the
identification of the Tate twist `ℚ_ℓ(c)` with `ℚ_ℓ` (the line `ℚ_ℓ · 1` of `tateTwistQlRep`, on
which `σ` acts by `χ_ℓ(σ)^c`) and the orientation of the Kummer classes at every finite level. -/
structure RootSystem (ℓ : ℕ) (kbar : Type u) [Field kbar] where
  /-- The `ℓⁿ⁺¹`-th root of unity. -/
  root : ℕ → kbar
  isPrimitive : ∀ n, IsPrimitiveRoot (root n) (ℓ ^ (n + 1))
  pow_root : ∀ n, root (n + 1) ^ ℓ = root n

variable (B ℓ X f kbar c i)

/-- **Finite-level fundamental-class normalisation at rational points.**  A class
`cl : A_i(X) → H^{2c}(X_{k̄}, ℤ_ℓ)` of the `ℓ`-adic limit satisfies it for the root system `ζ` if,
when `i = 0` (zero-cycles), for every level `ℓⁿ⁺¹` and every `k`-rational point `s` of `X` with
étale coordinates `π : V → 𝔸^c` centred at `s` (a `KummerPointDatum`), the `n`-th level of
`cl [s]`, read in `H^{2c}(X_{k̄}, ℤ/ℓⁿ⁺¹) = Ext^{2c}(Λ, Λ)` through the library's
`levelExtEquiv` (`LAdicSheaf.constantLevelCohomologyAddEquiv`), **is the Kummer-normalised
fundamental class of the point** `KummerFlag.kummerPointClass` (Yoneda product of the Kummer
divisor classes of the coordinate flag, read in `H^{2c}` through the adapted map).
Since the compact-support and ordinary cohomology of a *proper* `X` agree (identity
compactification), this is the class of a point in the usual `H^{2c}(X_{k̄}, ℤ/ℓⁿ⁺¹)`. -/
def IsPointNormalised (ζ : RootSystem ℓ kbar)
    (cl : chowGroup (fieldChowSituation k) f i →+
      (constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)).V) : Prop :=
  i = 0 → ∀ (n : ℕ) (D : KummerPointDatum f kbar ℓ c n)
    (hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar)),
    levelExtEquiv B ℓ X f kbar (2 * c) n
      ((levelProj B ℓ X f kbar ((2 * c : ℕ) : ℤ) n).hom
        (cl (QuotientAddGroup.mk
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f D.s i)))) =
      D.kummerClass (ζ.isPrimitive n) hN

/-- **A point-normalized cycle class system on `X`**: a
homomorphism from the Stacks Chow group `A_i(X)` — so rational equivalence and additivity are
built in — to the `ℓ`-adic limit `H^{2c}_{ét}(X_{k̄}, ℤ_ℓ) = lim_n H^{2c}(X_{k̄}, ℤ/ℓⁿ⁺¹)` of the
library's cohomology (transitions in `ℓ`-power levels built in), such that

* `point`: **its finite levels are the Kummer-normalised fundamental classes of rational points**
  (`IsPointNormalised`) — the zero map fails this (`not_isPointNormalised_zero`);
* `galois`: on cycles defined over `k` the Galois action is the inverse `c`-th power of the
  cyclotomic character: `σ · cl(α) = χ_ℓ(σ)^{-c} cl(α)`, i.e. `cl(α) ⊗ 1 ∈ H^{2c}(ℚ_ℓ) ⊗ ℚ_ℓ(c)`
  is invariant (`clQl_invariant`).  This is Galois equivariance of the fundamental class (the
  Kummer class of `ζ` and `σζ = ζ^{χ(σ)}`). -/
-- Point normalization constrains the classes of zero-cycles (`i = 0`) at rational points with
-- étale coordinate data. The canonical cycle class map is characterized by supported fundamental
-- classes of all integral subvarieties (`EtaleCycleClassInterface`).
structure PointNormalizedCycleClass (ζ : RootSystem ℓ kbar) where
  /-- The `ℓ`-adic cycle class map. -/
  cl : chowGroup (fieldChowSituation k) f i →+
    (constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)).V
  galois : ∀ (σ : kbar ≃ₐ[k] kbar) (α : chowGroup (fieldChowSituation k) f i),
    ((constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)).ρ σ).asHom.hom (cl α) =
      (((cyclotomicCharacterZl ℓ k kbar σ)⁻¹ ^ c : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • cl α
  point : IsPointNormalised B ℓ X f kbar c i ζ cl

variable {B ℓ X f kbar c i} {ζ : RootSystem ℓ kbar}

omit [Normal k kbar] in
/-- **The zero map fails the normalisation** whenever the library's non-divisibility of Kummer
point classes holds (it does, for connected smooth proper `X_{k̄}` over algebraically closed `k̄`,
`rationalPointKummerClassNondivisible`) and there is one rational point datum. -/
theorem not_isPointNormalised_zero [IsAlgClosed kbar]
    (hnd : RationalPointKummerClassNondivisible f kbar ℓ c) (hi : i = 0) (n : ℕ)
    (D : KummerPointDatum f kbar ℓ c n) (hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar)) :
    ¬ IsPointNormalised B ℓ X f kbar c i ζ 0 := by
  intro h
  have h1 := h hi n D hN
  simp only [AddMonoidHom.zero_apply, map_zero] at h1
  exact D.kummerClass_ne_zero hnd (ζ.isPrimitive n) hN h1.symm

namespace PointNormalizedCycleClass

variable (S : PointNormalizedCycleClass B ℓ X f kbar c i ζ)

omit [Normal k kbar] in
/-- The class of a rational point is nonzero at every level: the system `cl` is never zero. -/
theorem cl_point_ne_zero [IsAlgClosed kbar]
    (hnd : RationalPointKummerClassNondivisible f kbar ℓ c) (hi : i = 0) (n : ℕ)
    (D : KummerPointDatum f kbar ℓ c n) (hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar)) :
    S.cl (QuotientAddGroup.mk
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f D.s i)) ≠ 0 := by
  intro h0
  have h1 := S.point hi n D hN
  rw [h0, map_zero, map_zero] at h1
  exact D.kummerClass_ne_zero hnd (ζ.isPrimitive n) hN h1.symm

/-- The `n`-th finite level `H^{2c}(X_{k̄}, ℤ/ℓⁿ⁺¹)` of the cycle class map. -/
noncomputable def levelClass (n : ℕ) :
    chowGroup (fieldChowSituation k) f i →+
      levelModule B ℓ X f kbar ((2 * c : ℕ) : ℤ) n :=
  (levelProj B ℓ X f kbar ((2 * c : ℕ) : ℤ) n).hom.toAddMonoidHom.comp S.cl

omit [Normal k kbar] in
/-- **Compatibility of the `ℓ`-power levels**: the level `n + 1` class reduces to the level `n`
class under the transition of the inverse system. -/
theorem levelClass_succ (n : ℕ) (α : chowGroup (fieldChowSituation k) f i) :
    ((constantLevelSystem B ℓ X f kbar ((2 * c : ℕ) : ℤ)).map
        (homOfLE (n.le_add_right 1)).op).hom.hom (S.levelClass (n + 1) α) =
      S.levelClass n α :=
  congrArg (fun φ => φ.hom.hom (S.cl α))
    (limit.w (constantLevelSystem B ℓ X f kbar ((2 * c : ℕ) : ℤ)) (homOfLE (n.le_add_right 1)).op)

/-- **The rational cycle class map** `A_i(X) → H^{2c}(X_{k̄}, ℚ_ℓ) ⊗ ℚ_ℓ(c)`, `α ↦ cl(α) ⊗ 1`:
the assembly of the `ℓ`-adic limit of finite-level classes. -/
noncomputable def clQl : chowGroup (fieldChowSituation k) f i →+
    etaleCohomologyTwistSpace B ℓ X f kbar c :=
  (twistMk B ℓ X f kbar c).comp S.cl

omit [Normal k kbar] in
/-- **Invariance of the rational class of a cycle defined over `k`** (derived: from the finite
level Galois law `galois`, the transformation law `twistRep_twistMk` and
`χ_ℓ^c · χ_ℓ^{-c} = 1`). -/
theorem clQl_invariant (σ : kbar ≃ₐ[k] kbar) (α : chowGroup (fieldChowSituation k) f i) :
    etaleCohomologyTwistRep B ℓ X f kbar c σ (S.clQl α) = S.clQl α := by
  have hu : ((cyclotomicCharacterQl ℓ k kbar σ ^ c : ℚ_[ℓ]ˣ) : ℚ_[ℓ]) *
      algebraMap ℤ_[ℓ] ℚ_[ℓ] (((cyclotomicCharacterZl ℓ k kbar σ)⁻¹ ^ c : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := by
    rw [cyclotomicCharacterQl_eq ℓ k kbar]
    exact algebraMap_units_pow_mul_inv_pow (cyclotomicCharacterZl ℓ k kbar σ) c
  change etaleCohomologyTwistRep B ℓ X f kbar c σ (twistMk B ℓ X f kbar c (S.cl α)) =
    twistMk B ℓ X f kbar c (S.cl α)
  rw [twistRep_twistMk, S.galois, twistMk_smul, smul_smul, hu, one_smul]

/-- **The functoriality package from a point-normalized cycle class system.** Given the
classes `cl_E` of finite subextensions with the two functorialities, the base class is
the point-normalized one
and its invariance follows from the specified Galois law (`clQl_invariant`). -/
noncomputable def toFunctoriality
    (clE : ∀ (E : IntermediateField k kbar) [FiniteDimensional k E],
      Chow.galoisChowGroup E f i →+ etaleCohomologyTwistSpace B ℓ X f kbar c)
    (h_piStar : ∀ (E : IntermediateField k kbar) [FiniteDimensional k E]
      (α : chowGroup (fieldChowSituation k) f i),
      clE E (ChowGaloisDescent.piStar E f i α) = S.clQl α)
    (h_gal : ∀ (E : IntermediateField k kbar) [FiniteDimensional k E] [Normal k E]
      (σ : kbar ≃ₐ[k] kbar) (a : Chow.galoisChowGroup E f i),
      etaleCohomologyTwistRep B ℓ X f kbar c σ (clE E a) =
        clE E (Chow.galoisPushforward E f (AlgEquiv.restrictNormalHom E σ) i a)) :
    CycleClassFunctoriality B ℓ X f kbar c i where
  clBase := S.clQl
  cl := clE
  cl_piStar := h_piStar
  cl_galoisPushforward := h_gal
  clBase_invariant := S.clQl_invariant

end PointNormalizedCycleClass

end Geometric

end AbelianCycleClass

end ArithmeticOfJacobiPolynomials
