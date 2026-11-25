/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Chow.GaloisAction
public import ArithmeticOfJacobiPolynomials.Algebra.CycleDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.GaloisFieldExtension

/-!
# Rational descent of Galois-invariant Chow classes over a finite Galois extension

Proof of the last sentence of the proof of Corollary 6.6 (§6.5): *a Galois-invariant
class represented by algebraic cycles over a finite extension descends with rational coefficients
by averaging over a finite Galois extension*, on the **Stacks Chow groups**.

Let `E/k` be a finite field extension and `f : X ⟶ Spec k` locally of finite type.  Two additive
maps connect the Chow groups of `X` and of `X_E`, both regarded over `Spec k`
(`ArithmeticOfJacobiPolynomials.Chow.galoisChowGroup E f i = A_i(X_E)`):

* the flat pullback `π^* = piStar E f i : A_i(X) →+ A_i(X_E)` (Stacks 0FVJ on classes; the
  base-change map of `ArithmeticOfJacobiPolynomials.CycleDescent` followed by the identification of
  the Chow
  groups of `X_E` over `Spec E` and over `Spec k`);
* the proper pushforward `π_* = ArithmeticOfJacobiPolynomials.Chow.baseChangePushforward E f i`.

The identity `π_* π^* = [E : k]` is
`ArithmeticOfJacobiPolynomials.CycleDescent.pushforward_baseChange`, and for the Galois action
`ArithmeticOfJacobiPolynomials.Chow.galoisChowAction` one has `π_* (∑_σ σ • a) = [E : k] • π_* a`.

## Contents

* `ArithmeticOfJacobiPolynomials.ChowGaloisDescent.piStar`, `baseChangePushforward_piStar`:
  `π_* π^* = [E : k]` in the `Spec k`-based Chow groups.
* `ArithmeticOfJacobiPolynomials.ChowGaloisDescent.MackeyFormula E f i`: the double coset formula
  `π^* π_* a = ∑_σ σ • a` for every class `a` of `A_i(X_E)` (a `Prop`), and its **proof**
  `ArithmeticOfJacobiPolynomials.ChowGaloisDescent.mackeyFormula` for a finite Galois extension
  `E/k`.
* From it (`piStar_baseChangePushforward_of_invariant`,
  `exists_piStar_eq_smul_of_invariant`): every Galois-invariant class `a` of `A_i(X_E)` satisfies
  `[E : k] • a = π^* (π_* a)`, i.e. descends to `X` after multiplication by `[E : k]`
  (descent with rational coefficients).

## Proof of the Mackey formula

The formula is proved on cycles from three library facts:

1. *flat pullback commutes with proper pushforward in a cartesian square*
   (Stacks 02RG, `Stacks.Chow.flatPullback_properPushforward_unconditional`), applied to the
   square `X_E ×_X X_E ⇉ X_E ⟶ X` of the finite locally free projection `π`, which gives
   `π^* π_* z = (pr₂)_* (pr₁)^* z`;
2. *the Galois splitting of the self product of a finite Galois extension*
   (Stacks 0CDR, `Stacks.Descent.isIso_galoisCoverComparison_baseChange`):
   `∐_σ X_E ≅ X_E ×_X X_E` through the sections `θ_σ = (id, 1 × Spec σ)` of `pr₁`, which are open
   immersions with pairwise disjoint images covering `X_E ×_X X_E`;
3. *flat pullback along an open immersion is restriction, and flat pullback is functorial*
   (Stacks 02RB, 02RD), so that `(pr₁^* z)(θ_σ w) = z(w)`.

The fibre of `pr₂` over a point `x` is then `{θ_σ (σ⁻¹ x)}_σ`, each point having residue degree
one and the correct relative dimension (open immersions and isomorphisms), so that
`((pr₂)_* pr₁^* z)(x) = ∑_σ z(σ⁻¹ x)`, which is the coefficient function of `∑_σ σ_* z`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace ArithmeticOfJacobiPolynomials

namespace ChowGaloisDescent

variable {k : Type u} [Field k] (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (i : ℤ)

/-- **The flat pullback `π^* : A_i(X) →+ A_i(X_E)`** along the projection `π : X_E ⟶ X` of a
finite field extension, with the Chow group of `X_E` taken over `Spec k`. -/
noncomputable def piStar :
    chowGroup (fieldChowSituation k) f i →+ Chow.galoisChowGroup E f i :=
  (CycleDescent.chowLift k E f i).comp (CycleDescent.baseChangeMap k E f i)

/-- `π_* π^* = [E : k]` on `A_i(X)` (Stacks 02RH, `CycleDescent.pushforward_baseChange`). -/
theorem baseChangePushforward_piStar (α : chowGroup (fieldChowSituation k) f i) :
    Chow.baseChangePushforward E f i (piStar E f i α) = (Module.finrank k E : ℤ) • α :=
  CycleDescent.pushforward_baseChange k E f i α

/-! ### The self fibre product `X_E ×_X X_E` of a finite Galois extension -/

section SelfProduct

open Stacks.Descent Stacks.Descent.GaloisDescentData

omit [FiniteDimensional k E] in
/-- `X_E ×_X X_E`, the fibre product of the projection `π : X_E ⟶ X` with itself. -/
noncomputable abbrev selfProduct : Scheme.{u} :=
  pullback (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)

omit [FiniteDimensional k E] in
/-- The section `θ_σ = (id, 1 × Spec σ)` of the first projection of `X_E ×_X X_E`. -/
noncomputable def theta (σ : E ≃ₐ[k] E) :
    Chow.baseChangeScheme E f ⟶ selfProduct E f :=
  pullback.lift (𝟙 _) (Chow.galoisMap E f σ)
    ((Category.id_comp _).trans (Chow.galoisMap_fst E f σ).symm)

omit [FiniteDimensional k E] [LocallyOfFiniteType f] in
@[simp, reassoc]
theorem theta_fst (σ : E ≃ₐ[k] E) : theta E f σ ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

omit [FiniteDimensional k E] [LocallyOfFiniteType f] in
@[simp, reassoc]
theorem theta_snd (σ : E ≃ₐ[k] E) : theta E f σ ≫ pullback.snd _ _ = Chow.galoisMap E f σ :=
  pullback.lift_snd _ _ _

variable [IsGalois k E]

/-- The Galois cover comparison `∐_σ X_E ⟶ X_E ×_X X_E` (Stacks 0CDR). -/
noncomputable def coverComparison :
    (∐ fun _ : E ≃ₐ[k] E => Chow.baseChangeScheme E f) ⟶ selfProduct E f :=
  galoisCoverComparison (baseChangeProjection k E (Over.mk f))
    (baseChangeOverAction k E (Over.mk f))

instance isIso_coverComparison : IsIso (coverComparison E f) :=
  isIso_galoisCoverComparison_baseChange k E (Over.mk f)

omit [LocallyOfFiniteType f] [IsGalois k E] in
theorem sigmaι_coverComparison (σ : E ≃ₐ[k] E) :
    Sigma.ι (fun _ : E ≃ₐ[k] E => Chow.baseChangeScheme E f) σ ≫ coverComparison E f =
      theta E f σ := by
  unfold coverComparison
  rw [galoisCoverComparison_ι]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact (theta_fst E f σ).symm
  · rw [pullback.lift_snd]
    refine Eq.trans ?_ (theta_snd E f σ).symm
    rw [twist, baseChangeOverAction_hom_left]
    apply pullback.hom_ext
    · exact (baseChangeAction_comp_fst k E (Over.mk f) (.op σ)).trans
        (Chow.galoisMap_fst E f σ).symm
    · refine (baseChangeAction_comp_snd k E (Over.mk f) (.op σ)).trans ?_
      exact (Chow.galoisMap_snd E f σ).symm

instance isOpenImmersion_theta (σ : E ≃ₐ[k] E) : IsOpenImmersion (theta E f σ) := by
  rw [← sigmaι_coverComparison]
  infer_instance

omit [LocallyOfFiniteType f] in
/-- Every point of `X_E ×_X X_E` is the image of a point of `X_E` under some `θ_σ`. -/
theorem exists_theta_apply (y : selfProduct E f) :
    ∃ (σ : E ≃ₐ[k] E) (w : Chow.baseChangeScheme E f), (theta E f σ).base w = y := by
  obtain ⟨p, rfl⟩ := (coverComparison E f).surjective y
  obtain ⟨σ, w, rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι _ p
  exact ⟨σ, w, by rw [← sigmaι_coverComparison]; rfl⟩

omit [LocallyOfFiniteType f] in
/-- The images of the `θ_σ` are pairwise disjoint. -/
theorem eq_of_theta_apply_eq {σ τ : E ≃ₐ[k] E} {w w' : Chow.baseChangeScheme E f}
    (h : (theta E f σ).base w = (theta E f τ).base w') : σ = τ := by
  by_contra hne
  rw [← sigmaι_coverComparison, ← sigmaι_coverComparison] at h
  have h' := (coverComparison E f).isOpenEmbedding.injective h
  exact Set.disjoint_left.mp (Stacks.Chow.pairwise_disjoint_range_sigmaι
    (fun _ : E ≃ₐ[k] E => Chow.baseChangeScheme E f) hne) ⟨w, rfl⟩ ⟨w', h'.symm⟩

omit [FiniteDimensional k E] [LocallyOfFiniteType f] [IsGalois k E] in
theorem galoisMap_apply_galoisMap_inv (σ : E ≃ₐ[k] E) (x : Chow.baseChangeScheme E f) :
    (Chow.galoisMap E f σ).base ((Chow.galoisMap E f σ⁻¹).base x) = x := by
  have h : Chow.galoisMap E f σ⁻¹ ≫ Chow.galoisMap E f σ = 𝟙 _ := by
    rw [← Chow.galoisMap_mul, inv_mul_cancel, Chow.galoisMap_one]
  exact congrArg (fun g => g.base x) h

omit [FiniteDimensional k E] [LocallyOfFiniteType f] [IsGalois k E] in
theorem galoisMap_inv_apply_galoisMap (σ : E ≃ₐ[k] E) (x : Chow.baseChangeScheme E f) :
    (Chow.galoisMap E f σ⁻¹).base ((Chow.galoisMap E f σ).base x) = x := by
  simpa using galoisMap_apply_galoisMap_inv E f σ⁻¹ x

/-- The point of the fibre of the second projection over `x` lying in the `σ`-th piece. -/
noncomputable def fibrePoint (x : Chow.baseChangeScheme E f) (σ : E ≃ₐ[k] E) : selfProduct E f :=
  (theta E f σ).base ((Chow.galoisMap E f σ⁻¹).base x)

omit [FiniteDimensional k E] [LocallyOfFiniteType f] [IsGalois k E] in
theorem snd_fibrePoint (x : Chow.baseChangeScheme E f) (σ : E ≃ₐ[k] E) :
    (pullback.snd (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)).base
      (fibrePoint E f x σ) = x := by
  have h := congrArg (fun g => g.base ((Chow.galoisMap E f σ⁻¹).base x)) (theta_snd E f σ)
  exact h.trans (galoisMap_apply_galoisMap_inv E f σ x)

omit [LocallyOfFiniteType f] in
theorem fibrePoint_injective (x : Chow.baseChangeScheme E f) :
    Function.Injective (fibrePoint E f x) := fun _ _ h => eq_of_theta_apply_eq E f h

omit [LocallyOfFiniteType f] in
/-- The fibre of the second projection of `X_E ×_X X_E` over `x` is the set of the points
`θ_σ (σ⁻¹ x)`. -/
theorem snd_preimage_singleton (x : Chow.baseChangeScheme E f) :
    (pullback.snd (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)).base ⁻¹' {x} =
      Set.range (fibrePoint E f x) := by
  ext y
  constructor
  · intro hy
    obtain ⟨σ, w, rfl⟩ := exists_theta_apply E f y
    have hy0 : (pullback.snd (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)).base
        ((theta E f σ).base w) = x := hy
    have hy' : (Chow.galoisMap E f σ).base w = x :=
      (congrArg (fun g => g.base w) (theta_snd E f σ)).symm.trans hy0
    refine ⟨σ, ?_⟩
    unfold fibrePoint
    rw [← hy', galoisMap_inv_apply_galoisMap]
  · rintro ⟨σ, rfl⟩
    exact snd_fibrePoint E f x σ

/-! #### Flat pullback along the first projection -/

open Stacks.Chow

omit [IsGalois k E] in
instance : Flat (Chow.baseChangeProj E f) := CycleDescent.instFlatProj k E f

omit [IsGalois k E] in
instance : IsProper (Chow.baseChangeProj E f) := CycleDescent.instIsProperProj k E f

omit [IsGalois k E] in
instance : LocallyOfFiniteType (Chow.baseChangeProj E f) :=
  CycleDescent.instLocallyOfFiniteTypeProj k E f

omit [IsGalois k E] in
instance : LocallyOfFiniteType (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
    Chow.baseChangeStructure E f) := by
  infer_instance

omit [IsGalois k E] [LocallyOfFiniteType f] in
theorem relativeDimension_baseChangeProj :
    AlgebraicGeometry.RelativeDimension (Chow.baseChangeProj E f) 0 :=
  Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)

variable {E f}

/-- The coefficient of the flat pullback `fst^* z` at the point `θ_σ (w)` is the coefficient of
`z` at `w`: restriction along the open immersion `θ_σ` followed by `fst ∘ θ_σ = id`. -/
theorem coeff_flatPullback_fst_theta {i : ℤ}
    (hrd : AlgebraicGeometry.RelativeDimension
      (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)) 0)
    (z : CycleGroup (fieldChowSituation k) (Chow.baseChangeStructure E f) i)
    (σ : E ≃ₐ[k] E) (w : Chow.baseChangeScheme E f) :
    (flatPullback (fieldChowSituation k)
      (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
        Chow.baseChangeStructure E f) (Chow.baseChangeStructure E f)
      (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)) rfl 0 hrd i z).1
      ((theta E f σ).base w) = z.1 w := by
  have hθ := theta_fst E f σ
  have : IsOpenImmersion (theta E f σ ≫ pullback.fst (Chow.baseChangeProj E f)
      (Chow.baseChangeProj E f)) := by rw [hθ]; infer_instance
  have h1 := congrArg (fun c => c.1 w)
    (cycleGroupRestrict_eq_flatPullback (fieldChowSituation k)
      (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
        Chow.baseChangeStructure E f) (Chow.baseChangeStructure E f) (theta E f σ)
      (by rw [theta_fst_assoc]) (relativeDimension_of_isOpenImmersion _) (i + ((0 : ℕ) : ℤ))
      (flatPullback (fieldChowSituation k)
        (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
          Chow.baseChangeStructure E f) (Chow.baseChangeStructure E f)
        (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)) rfl 0 hrd i z))
  have h2 := flatPullback_comp_apply (fieldChowSituation k) (Chow.baseChangeStructure E f)
    (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
      Chow.baseChangeStructure E f) (Chow.baseChangeStructure E f) (theta E f σ)
    (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f))
    (by rw [theta_fst_assoc]) rfl 0 0 (relativeDimension_of_isOpenImmersion _) hrd i z w
  have h3 := congrArg (fun c => c.1 w)
    (cycleGroupRestrict_eq_flatPullback (fieldChowSituation k) (Chow.baseChangeStructure E f)
      (Chow.baseChangeStructure E f) (theta E f σ ≫ pullback.fst (Chow.baseChangeProj E f)
        (Chow.baseChangeProj E f)) (by rw [Category.assoc, theta_fst_assoc])
      (relativeDimension_of_isOpenImmersion _) i z)
  refine Eq.trans (Eq.trans (rfl : _ = _) (h1.trans h2)) (h3.symm.trans ?_)
  change z.1 ((theta E f σ ≫ pullback.fst (Chow.baseChangeProj E f)
    (Chow.baseChangeProj E f)).base w) = z.1 w
  rw [hθ]
  rfl

variable (E f)

end SelfProduct

variable [Fintype (E ≃ₐ[k] E)]

/-- **The double coset (Mackey) formula** for the finite Galois extension `E/k`:
`π^* π_* a = ∑_{σ ∈ Aut(E/k)} σ • a` for every `a ∈ A_i(X_E)`. -/
def MackeyFormula : Prop :=
  ∀ a : Chow.galoisChowGroup E f i,
    piStar E f i (Chow.baseChangePushforward E f i a) = Chow.galoisNorm E f i a

/-! #### Cycles on `X_E ×_X X_E` -/

section Cycles

variable [IsGalois k E]

variable {E f}

/-- The coefficient at `x` of the pushforward along the second projection of `X_E ×_X X_E` is the
sum over `σ` of the coefficients of the cycle at the points `θ_σ (σ⁻¹ x)` of the fibre. -/
theorem coeff_properPushforward_snd {j : ℤ}
    (h : pullback.snd (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
      Chow.baseChangeStructure E f =
      pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
        Chow.baseChangeStructure E f)
    (β : CycleGroup (fieldChowSituation k)
      (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
        Chow.baseChangeStructure E f) j)
    (x : Chow.baseChangeScheme E f) :
    (properPushforward (fieldChowSituation k) _ (Chow.baseChangeStructure E f)
      (pullback.snd (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)) h j β).1 x =
      ∑ σ : E ≃ₐ[k] E, β.1 (fibrePoint E f x σ) := by
  rw [properPushforward_apply, snd_preimage_singleton,
    finsum_mem_range (fibrePoint_injective E f x), finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hy : fibrePoint E f x σ = (theta E f σ).base ((Chow.galoisMap E f σ⁻¹).base x) := rfl
  have hx : x = (Chow.galoisMap E f σ).base ((Chow.galoisMap E f σ⁻¹).base x) :=
    (galoisMap_apply_galoisMap_inv E f σ x).symm
  have hd1 : relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
        Chow.baseChangeStructure E f) (fibrePoint E f x σ) =
      relativeDimension (fieldChowSituation k).dimensionFunction (Chow.baseChangeStructure E f)
        ((Chow.galoisMap E f σ⁻¹).base x) := by
    rw [hy, ← relativeDimension_comp_isOpenImmersion _ (theta E f σ), theta_fst_assoc]
  have hd2 : relativeDimension (fieldChowSituation k).dimensionFunction
      (Chow.baseChangeStructure E f)
      ((pullback.snd (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)).base
        (fibrePoint E f x σ)) =
      relativeDimension (fieldChowSituation k).dimensionFunction (Chow.baseChangeStructure E f)
        ((Chow.galoisMap E f σ⁻¹).base x) := by
    rw [snd_fibrePoint]
    conv_lhs => rw [hx]
    rw [← relativeDimension_comp_isOpenImmersion _ (Chow.galoisMap E f σ),
      Chow.galoisMap_structure]
  have hres : (pullback.snd (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)).residueDegree
      (fibrePoint E f x σ) = 1 := by
    rw [hy, ← residueDegree_isOpenImmersion_comp (theta E f σ), theta_snd]
    exact residueDegree_eq_one_of_isOpenImmersion _ _
  simp only [hd1.trans hd2.symm, ite_true, hres]
  simp

variable (E f)

/-- **The Mackey formula on cycles.** For a finite Galois extension `E/k`, the flat pullback
`π^*` of the proper pushforward `π_* z` of a cycle `z` of `X_E` has the coefficient function of
`∑_σ (1 × Spec σ⁻¹)_* z`. -/
theorem cycleLift_baseChange_pushforward_eq_sum
    (z : CycleGroup (fieldChowSituation k) (Chow.baseChangeStructure E f) i) :
    CycleDescent.cycleLift k E f i
      (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k E) rfl f
        (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g) i
        (properPushforward (fieldChowSituation k) (Chow.baseChangeStructure E f) f
          (Chow.baseChangeProj E f) rfl i z)) =
      ∑ σ : E ≃ₐ[k] E, properPushforward (fieldChowSituation k) (Chow.baseChangeStructure E f)
        (Chow.baseChangeStructure E f) (Chow.galoisMap E f σ⁻¹)
        (Chow.galoisMap_structure E f σ⁻¹) i z := by
  have hrd := relativeDimension_baseChangeProj E f
  have key := flatPullback_properPushforward_unconditional (fieldChowSituation k)
    (Chow.baseChangeStructure E f) f
    (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f) ≫
      Chow.baseChangeStructure E f) (Chow.baseChangeStructure E f)
    (Chow.baseChangeProj E f) (Chow.baseChangeProj E f)
    (pullback.fst (Chow.baseChangeProj E f) (Chow.baseChangeProj E f))
    (pullback.snd (Chow.baseChangeProj E f) (Chow.baseChangeProj E f))
    (IsPullback.of_hasPullback _ _) rfl rfl rfl 0 hrd i z
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hlift := val_baseChangeCyclePullbackOfIsPullback_eq_val_flatPullback k E f hrd i
    (properPushforward (fieldChowSituation k) (Chow.baseChangeStructure E f) f
      (Chow.baseChangeProj E f) rfl i z)
  have hterm : ∀ σ : E ≃ₐ[k] E,
      (properPushforward (fieldChowSituation k) (Chow.baseChangeStructure E f)
        (Chow.baseChangeStructure E f) (Chow.galoisMap E f σ⁻¹)
        (Chow.galoisMap_structure E f σ⁻¹) i z).1 x =
        z.1 ((Chow.galoisMap E f σ).base x) := fun σ => by
    have := properPushforward_apply_of_isIso (fieldChowSituation k)
      (Chow.baseChangeStructure E f) (Chow.baseChangeStructure E f) (Chow.galoisMap E f σ⁻¹)
      (Chow.galoisMap_structure E f σ⁻¹) i z ((Chow.galoisMap E f σ).base x)
    rwa [galoisMap_inv_apply_galoisMap] at this
  calc _ = (flatPullback (fieldChowSituation k) _ f (Chow.baseChangeProj E f) rfl 0 hrd i
        (properPushforward (fieldChowSituation k) (Chow.baseChangeStructure E f) f
          (Chow.baseChangeProj E f) rfl i z)).1 x := congrArg (fun c => c x) hlift
    _ = _ := congrArg (fun c => c.1 x) key
    _ = ∑ σ : E ≃ₐ[k] E, z.1 ((Chow.galoisMap E f σ⁻¹).base x) := by
      rw [coeff_properPushforward_snd]
      exact Finset.sum_congr rfl fun σ _ => coeff_flatPullback_fst_theta
        (AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback _ _).flip hrd)
        z σ _
    _ = ∑ σ : E ≃ₐ[k] E, z.1 ((Chow.galoisMap E f σ).base x) :=
      Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => rfl
    _ = _ := by
      simp only [AddSubgroup.val_finsetSum, Function.locallyFinsuppWithin.coe_sum,
        Finset.sum_apply, hterm]

/-- **The Mackey formula** `π^* π_* a = ∑_{σ ∈ Gal(E/k)} σ • a` on the Stacks Chow groups
`A_i(X_E)`, for a finite Galois extension `E/k`. -/
theorem mackeyFormula : MackeyFormula E f i := by
  intro a
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences (fieldChowSituation k) (Chow.baseChangeStructure E f) i) a
  have h2 : ∀ w : CycleGroup (fieldChowSituation k) f i,
      piStar E f i (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f i) w) =
        QuotientAddGroup.mk' _ (CycleDescent.cycleLift k E f i
          (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k E) rfl f
            (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g) i w)) :=
    fun w => by
      unfold piStar
      change CycleDescent.chowLift k E f i (CycleDescent.baseChangeMap k E f i _) = _
      rw [CycleDescent.baseChangeMap, baseChangeChowPullbackOfIsPullback_mk]
      rfl
  have h1 : Chow.baseChangePushforward E f i
      (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k)
        (Chow.baseChangeStructure E f) i) z) =
      QuotientAddGroup.mk' _ (properPushforward (fieldChowSituation k)
        (Chow.baseChangeStructure E f) f (Chow.baseChangeProj E f) rfl i z) := rfl
  rw [h1, h2, cycleLift_baseChange_pushforward_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun σ _ => rfl

end Cycles

variable {E f i}

/-- Under the Mackey formula, a Galois-invariant class `a` of `A_i(X_E)` satisfies
`π^* π_* a = #Aut(E/k) • a`. -/
theorem piStar_baseChangePushforward_of_invariant (hM : MackeyFormula E f i)
    {a : Chow.galoisChowGroup E f i}
    (ha : ∀ σ : E ≃ₐ[k] E, Chow.galoisPushforward E f σ i a = a) :
    piStar E f i (Chow.baseChangePushforward E f i a) =
      Fintype.card (E ≃ₐ[k] E) • a := by
  rw [hM a]
  unfold Chow.galoisNorm
  simp [ha]

/-- **Descent with rational coefficients.** For a finite Galois extension `E/k` satisfying the
Mackey formula, a Galois-invariant class `a` of `A_i(X_E)` has `[E : k] • a` in the image of
`π^* : A_i(X) → A_i(X_E)`: namely `[E : k] • a = π^*(π_* a)`. -/
theorem exists_piStar_eq_smul_of_invariant [IsGalois k E] (hM : MackeyFormula E f i)
    {a : Chow.galoisChowGroup E f i}
    (ha : ∀ σ : E ≃ₐ[k] E, Chow.galoisPushforward E f σ i a = a) :
    ∃ α : chowGroup (fieldChowSituation k) f i, piStar E f i α = (Module.finrank k E : ℕ) • a := by
  refine ⟨Chow.baseChangePushforward E f i a, ?_⟩
  rw [piStar_baseChangePushforward_of_invariant hM ha, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank]

omit [Fintype (E ≃ₐ[k] E)] in
/-- **Descent with rational coefficients for a finite Galois extension** (the last sentence of the
proof of Corollary 6.6, at the level of Chow classes): a Galois-invariant class `a` of `A_i(X_E)`
satisfies `[E : k] • a = π^* (π_* a)`, so `[E : k] • a` comes from `A_i(X)`. -/
theorem exists_piStar_eq_smul_of_invariant_galois [IsGalois k E]
    {a : Chow.galoisChowGroup E f i}
    (ha : ∀ σ : E ≃ₐ[k] E, Chow.galoisPushforward E f σ i a = a) :
    ∃ α : chowGroup (fieldChowSituation k) f i,
      piStar E f i α = (Module.finrank k E : ℕ) • a := by
  let _ : Fintype (E ≃ₐ[k] E) := Fintype.ofFinite _
  exact exists_piStar_eq_smul_of_invariant (mackeyFormula E f i) ha

end ChowGaloisDescent

end ArithmeticOfJacobiPolynomials
