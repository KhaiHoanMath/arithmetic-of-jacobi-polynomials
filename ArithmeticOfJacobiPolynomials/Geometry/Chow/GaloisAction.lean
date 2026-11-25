/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Chow.Functoriality
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Galois.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre

/-!
# Isomorphism invariance of Chow groups and the Galois action on a base change

Chow groups are the library's `Stacks.Chow.chowGroup C sX k` (Stacks 02RW), and the
only functoriality used is the library's proper pushforward on Chow groups
`Stacks.Chow.properChowPushforward` (Stacks 0GU8), which descends from cycles because proper
pushforward preserves rational equivalence
(`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`, Stacks 02S2) and is
functorial (`Stacks.Chow.properChowPushforward_comp`, Stacks 02R5). This file adds the
bookkeeping specific to the manuscript's Galois descent of algebraic cycles ("a Galois-invariant
class represented by algebraic cycles over a finite extension descends with rational coefficients
by averaging over a finite Galois extension"), none of which is in the library.

## Isomorphism invariance

An isomorphism `e : X ≅ Y` over the base is proper, so
`ArithmeticOfJacobiPolynomials.Chow.chowGroupEquivOfIso C sX sY e` is the isomorphism
`A_k(X) ≃+ A_k(Y)` given by pushforward along `e.hom`, with inverse the pushforward along
`e.inv`; its functoriality is `chowPushforward_id` and `chowPushforward_comp`.

## The Galois action

Let `p : X ⟶ Spec K` be locally of finite type and `L/K` a finite extension. The base change is
`X_L = ArithmeticOfJacobiPolynomials.Chow.baseChangeScheme L p = X ×_{Spec K} Spec L`, with
projection
`π = ArithmeticOfJacobiPolynomials.Chow.baseChangeProj L p`. An automorphism `σ ∈ L ≃ₐ[K] L`
induces the
automorphism `1 × Spec σ` of `X_L` (`ArithmeticOfJacobiPolynomials.Chow.galoisMap L p σ`), which
commutes with `π`.
Since `Spec` is contravariant, `galoisMap (σ * τ) = galoisMap σ ≫ galoisMap τ`, so `σ` acts on the
Chow group `A_i(X_L)` of `X_L` over `K` (the group `chowGroup (fieldChowSituation K) (π ≫ p) i`)
by **pushforward along `galoisMap σ⁻¹`**, which is a left action
(`ArithmeticOfJacobiPolynomials.Chow.galoisChowAction : (L ≃ₐ[K] L) →* AddMonoid.End (A_i(X_L))`).

The projection `π : X_L ⟶ X` is finite, hence proper, so it has a pushforward
`ArithmeticOfJacobiPolynomials.Chow.baseChangePushforward L p i : A_i(X_L) →+ A_i(X)` on Chow
groups, and since
`galoisMap σ ≫ π = π` it is Galois invariant
(`ArithmeticOfJacobiPolynomials.Chow.baseChangePushforward_galoisChowAction`). For a finite
automorphism group the
norm `galoisNorm a = ∑_σ σ • a` is Galois invariant and
`π_*(∑_σ σ • a) = #Aut(L/K) • π_* a`, which is `[L : K] • π_* a` for `L/K` finite Galois
(`ArithmeticOfJacobiPolynomials.Chow.baseChangePushforward_galoisNorm_of_isGalois`): **this is the
averaging
statement at the level of Chow groups**, not only cycles.

The finite-extension pullback and transfer formulas are proved in `CycleDescent` and
`ChowGaloisDescent`; the cycle-class application is in `AbelianCycleClass`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace Chow

/-! ### Proper pushforward on Chow groups, over a fixed base -/

section Pushforward

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]

/-- Proper pushforward on Chow groups along a proper morphism over the base: the library's
`Stacks.Chow.properChowPushforward` (Stacks 0GU8), with its hypothesis (Stacks 02S2) discharged
by `properPushforwardFactorsThroughRationalEquivalence_of_isProper`. -/
@[expose] noncomputable def chowPushforward (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (k : ℤ) :
    chowGroup C sX k →+ chowGroup C sY k :=
  properChowPushforward C sX sY f hf k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY f hf k)

@[simp]
theorem chowPushforward_mk (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (k : ℤ)
    (α : CycleGroup C sX k) :
    chowPushforward C sX sY f hf k (QuotientAddGroup.mk α) =
      QuotientAddGroup.mk (properPushforward C sX sY f hf k α) :=
  rfl

/-- Pushforward only depends on the morphism. -/
theorem chowPushforward_congr {f f' : X ⟶ Y} [IsProper f] [IsProper f'] (h : f = f')
    (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (k : ℤ) :
    chowPushforward C sX sY f hf k = chowPushforward C sX sY f' hf' k := by
  subst h
  rfl

/-- Pushforward along the identity is the identity. -/
theorem chowPushforward_id (k : ℤ) :
    chowPushforward C sX sX (𝟙 X) (Category.id_comp sX) k = AddMonoidHom.id _ := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun α => ?_)
  exact congrArg QuotientAddGroup.mk (properPushforward_id C sX k α)

/-- **Functoriality** (Stacks 02R5, 0GU8): pushing forward along `f` and then `g` is pushing
forward along `f ≫ g`. -/
theorem chowPushforward_comp (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ) :
    (chowPushforward C sY sZ g hg k).comp (chowPushforward C sX sY f hf k) =
      chowPushforward C sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) k :=
  properChowPushforward_comp C sX sY sZ f g hf hg k _ _

theorem chowPushforward_comp_apply (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ) (a : chowGroup C sX k) :
    chowPushforward C sY sZ g hg k (chowPushforward C sX sY f hf k a) =
      chowPushforward C sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) k a :=
  DFunLike.congr_fun (chowPushforward_comp C sX sY sZ f g hf hg k) a

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
theorem inv_comp_structure (e : X ≅ Y) (he : e.hom ≫ sY = sX) : e.inv ≫ sX = sY := by
  rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- **Isomorphism invariance of Chow groups**: an isomorphism `e : X ≅ Y` over the base induces
`A_k(X) ≃+ A_k(Y)`, the pushforward along `e.hom` with inverse the pushforward along `e.inv`. -/
@[expose] noncomputable def chowGroupEquivOfIso (e : X ≅ Y) (he : e.hom ≫ sY = sX) (k : ℤ) :
    chowGroup C sX k ≃+ chowGroup C sY k where
  toFun := chowPushforward C sX sY e.hom he k
  invFun := chowPushforward C sY sX e.inv (inv_comp_structure C sX sY e he) k
  left_inv a := by
    rw [chowPushforward_comp_apply C sX sY sX e.hom e.inv he (inv_comp_structure C sX sY e he) k a,
      chowPushforward_congr C sX sX e.hom_inv_id _ (Category.id_comp sX) k, chowPushforward_id]
    rfl
  right_inv b := by
    rw [chowPushforward_comp_apply C sY sX sY e.inv e.hom (inv_comp_structure C sX sY e he) he k b,
      chowPushforward_congr C sY sY e.inv_hom_id _ (Category.id_comp sY) k, chowPushforward_id]
    rfl
  map_add' := map_add _

end Pushforward

/-! ### The base change `X_L` and its Galois automorphisms -/

section Galois

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K))

/-- The structure morphism `Spec L ⟶ Spec K`. -/
noncomputable abbrev specStructure (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

instance quasiCompact_specStructure : QuasiCompact (specStructure K L) :=
  inferInstance

/-- The base change `X_L = X ×_{Spec K} Spec L`. -/
noncomputable abbrev baseChangeScheme : Scheme.{u} :=
  pullback p (specStructure K L)

/-- The projection `π : X_L ⟶ X`. -/
noncomputable abbrev baseChangeProj : baseChangeScheme L p ⟶ X :=
  pullback.fst p (specStructure K L)

/-- For `X` locally Noetherian and `L/K` finite, `X_L` is locally Noetherian. -/
instance isLocallyNoetherian_baseChangeScheme [IsLocallyNoetherian X] [Module.Finite K L] :
    IsLocallyNoetherian (baseChangeScheme L p) := by
  have : LocallyOfFiniteType (specStructure K L) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.Finite.to_finiteType (RingHom.finite_algebraMap.mpr inferInstance))
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.fst p (specStructure K L))

theorem specMap_galois (σ : L ≃ₐ[K] L) :
    Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ specStructure K L = specStructure K L := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => σ.commutes x))

/-- The automorphism `1 × Spec σ` of `X_L = X ×_{Spec K} Spec L` induced by `σ ∈ Aut(L/K)`. -/
@[expose]
noncomputable def galoisMap (σ : L ≃ₐ[K] L) : baseChangeScheme L p ⟶ baseChangeScheme L p :=
  pullback.lift (pullback.fst p (specStructure K L))
    (pullback.snd p (specStructure K L) ≫ Spec.map (CommRingCat.ofHom (σ : L →+* L)))
    (by rw [Category.assoc, specMap_galois]; exact pullback.condition)

theorem galoisMap_fst (σ : L ≃ₐ[K] L) :
    galoisMap L p σ ≫ pullback.fst p (specStructure K L) = pullback.fst p (specStructure K L) :=
  pullback.lift_fst _ _ _

theorem galoisMap_snd (σ : L ≃ₐ[K] L) :
    galoisMap L p σ ≫ pullback.snd p (specStructure K L) =
      pullback.snd p (specStructure K L) ≫ Spec.map (CommRingCat.ofHom (σ : L →+* L)) :=
  pullback.lift_snd _ _ _

theorem galoisMap_one : galoisMap L p 1 = 𝟙 _ := by
  have h : CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L) = 𝟙 (CommRingCat.of L) :=
    CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  apply pullback.hom_ext
  · rw [galoisMap_fst, Category.id_comp]
  · rw [galoisMap_snd, h, Spec.map_id, Category.comp_id, Category.id_comp]

/-- `σ ↦ 1 × Spec σ` reverses the order of composition (as maps of points,
`1 × Spec (στ) = (1 × Spec τ) ∘ (1 × Spec σ)`). -/
theorem galoisMap_mul (σ τ : L ≃ₐ[K] L) :
    galoisMap L p (σ * τ) = galoisMap L p σ ≫ galoisMap L p τ := by
  have h : CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L) =
      CommRingCat.ofHom (τ : L →+* L) ≫ CommRingCat.ofHom (σ : L →+* L) :=
    CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  apply pullback.hom_ext
  · rw [galoisMap_fst, Category.assoc, galoisMap_fst, galoisMap_fst]
  · rw [galoisMap_snd, Category.assoc, galoisMap_snd, ← Category.assoc, galoisMap_snd,
      Category.assoc, h, Spec.map_comp]

/-- The automorphism `1 × Spec σ` as an isomorphism `X_L ≅ X_L`. -/
@[expose]
noncomputable def galoisIso (σ : L ≃ₐ[K] L) : baseChangeScheme L p ≅ baseChangeScheme L p where
  hom := galoisMap L p σ
  inv := galoisMap L p σ⁻¹
  hom_inv_id := by rw [← galoisMap_mul, mul_inv_cancel, galoisMap_one]
  inv_hom_id := by rw [← galoisMap_mul, inv_mul_cancel, galoisMap_one]

instance isIso_galoisMap (σ : L ≃ₐ[K] L) : IsIso (galoisMap L p σ) :=
  (galoisIso L p σ).isIso_hom

theorem galoisIso_one_symm : (galoisIso L p 1).symm = Iso.refl _ :=
  Iso.ext (by
    change galoisMap L p 1⁻¹ = 𝟙 _
    rw [inv_one, galoisMap_one])

theorem galoisIso_mul_symm (σ τ : L ≃ₐ[K] L) :
    (galoisIso L p (σ * τ)).symm = (galoisIso L p τ).symm ≪≫ (galoisIso L p σ).symm :=
  Iso.ext (by
    change galoisMap L p (σ * τ)⁻¹ = galoisMap L p τ⁻¹ ≫ galoisMap L p σ⁻¹
    rw [mul_inv_rev, galoisMap_mul])

/-! ### The Galois action on the Chow groups of `X_L` -/

section ChowAction

variable [LocallyOfFiniteType p] [Module.Finite K L]

omit [LocallyOfFiniteType p] in
instance isFinite_specStructure : IsFinite (specStructure K L) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The structure morphism `X_L ⟶ X ⟶ Spec K` over which the Chow groups of `X_L` are taken. -/
noncomputable abbrev baseChangeStructure : baseChangeScheme L p ⟶ Spec (CommRingCat.of K) :=
  baseChangeProj L p ≫ p

omit [LocallyOfFiniteType p] [Module.Finite K L] in
theorem galoisMap_structure (σ : L ≃ₐ[K] L) :
    galoisMap L p σ ≫ baseChangeStructure L p = baseChangeStructure L p := by
  rw [baseChangeStructure, ← Category.assoc, galoisMap_fst]

/-- The Chow group `A_i(X_L)` of the base change, as a scheme over `K`. -/
abbrev galoisChowGroup (i : ℤ) : Type u :=
  chowGroup (fieldChowSituation K) (baseChangeStructure L p) i

/-- The action of `σ ∈ Aut(L/K)` on `A_i(X_L)`: **pushforward along `1 × Spec σ⁻¹`**, i.e.
pullback along `1 × Spec σ` (the library's proper pushforward, `1 × Spec σ⁻¹` being an
isomorphism). -/
@[expose] noncomputable def galoisPushforward (σ : L ≃ₐ[K] L) (i : ℤ) :
    galoisChowGroup L p i →+ galoisChowGroup L p i :=
  chowPushforward (fieldChowSituation K) (baseChangeStructure L p) (baseChangeStructure L p)
    (galoisMap L p σ⁻¹) (galoisMap_structure L p σ⁻¹) i

theorem galoisPushforward_one (i : ℤ) : galoisPushforward L p 1 i = AddMonoidHom.id _ := by
  unfold galoisPushforward
  rw [chowPushforward_congr _ _ _ (f' := 𝟙 _) (by rw [inv_one, galoisMap_one]) _
    (Category.id_comp _) i]
  exact chowPushforward_id _ _ i

/-- `(στ) • a = σ • (τ • a)`. -/
theorem galoisPushforward_mul (σ τ : L ≃ₐ[K] L) (i : ℤ) :
    galoisPushforward L p (σ * τ) i =
      (galoisPushforward L p σ i).comp (galoisPushforward L p τ i) := by
  unfold galoisPushforward
  rw [chowPushforward_comp]
  exact chowPushforward_congr _ _ _ (by rw [mul_inv_rev, galoisMap_mul]) _ _ i

theorem galoisPushforward_mul_apply (σ τ : L ≃ₐ[K] L) (i : ℤ) (a : galoisChowGroup L p i) :
    galoisPushforward L p (σ * τ) i a =
      galoisPushforward L p σ i (galoisPushforward L p τ i a) :=
  DFunLike.congr_fun (galoisPushforward_mul L p σ τ i) a

/-- **The Galois action on the Chow groups of `X_L`**: a left action of `Aut(L/K)` by additive
endomorphisms. -/
@[expose] noncomputable def galoisChowAction (i : ℤ) :
    (L ≃ₐ[K] L) →* AddMonoid.End (galoisChowGroup L p i) where
  toFun σ := galoisPushforward L p σ i
  map_one' := galoisPushforward_one L p i
  map_mul' σ τ := galoisPushforward_mul L p σ τ i

/-- The pushforward `π_* : A_i(X_L) ⟶ A_i(X)` along the projection `π : X_L ⟶ X`, which is finite
(hence proper) because `L/K` is finite. -/
@[expose] noncomputable def baseChangePushforward (i : ℤ) :
    galoisChowGroup L p i →+ chowGroup (fieldChowSituation K) p i :=
  chowPushforward (fieldChowSituation K) (baseChangeStructure L p) p (baseChangeProj L p) rfl i

/-- **`π_*` is Galois invariant**: `π_* (σ • a) = π_* a`, because `(1 × Spec σ⁻¹) ≫ π = π`. -/
theorem baseChangePushforward_galoisPushforward (σ : L ≃ₐ[K] L) (i : ℤ)
    (a : galoisChowGroup L p i) :
    baseChangePushforward L p i (galoisPushforward L p σ i a) = baseChangePushforward L p i a := by
  unfold baseChangePushforward galoisPushforward
  rw [chowPushforward_comp_apply]
  exact DFunLike.congr_fun
    (chowPushforward_congr _ _ _ (galoisMap_fst L p σ⁻¹) _ _ i) a

/-! ### Averaging over a finite automorphism group -/

section Norm

variable [Fintype (L ≃ₐ[K] L)]

/-- The norm `∑_σ σ • a` of a class on `X_L`. -/
@[expose] noncomputable def galoisNorm (i : ℤ) (a : galoisChowGroup L p i) :
    galoisChowGroup L p i :=
  ∑ σ : L ≃ₐ[K] L, galoisPushforward L p σ i a

/-- The norm of a class is Galois invariant. -/
theorem galoisPushforward_galoisNorm (τ : L ≃ₐ[K] L) (i : ℤ) (a : galoisChowGroup L p i) :
    galoisPushforward L p τ i (galoisNorm L p i a) = galoisNorm L p i a := by
  unfold galoisNorm
  rw [map_sum]
  exact Fintype.sum_bijective (τ * ·) (Group.mulLeft_bijective τ) _ _
    fun σ => (galoisPushforward_mul_apply L p τ σ i a).symm

/-- **Averaging**: `π_* (∑_σ σ • a) = #Aut(L/K) • π_* a` in `A_i(X)`. -/
theorem baseChangePushforward_galoisNorm (i : ℤ) (a : galoisChowGroup L p i) :
    baseChangePushforward L p i (galoisNorm L p i a) =
      Fintype.card (L ≃ₐ[K] L) • baseChangePushforward L p i a := by
  unfold galoisNorm
  simp only [map_sum, baseChangePushforward_galoisPushforward, Finset.sum_const,
    Finset.card_univ]

/-- **Averaging over a finite Galois extension**: `π_* (∑_σ σ • a) = [L : K] • π_* a`. -/
theorem baseChangePushforward_galoisNorm_of_isGalois [IsGalois K L] (i : ℤ)
    (a : galoisChowGroup L p i) :
    baseChangePushforward L p i (galoisNorm L p i a) =
      Module.finrank K L • baseChangePushforward L p i a := by
  rw [baseChangePushforward_galoisNorm, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

end Norm

end ChowAction

end Galois

end Chow

end ArithmeticOfJacobiPolynomials
