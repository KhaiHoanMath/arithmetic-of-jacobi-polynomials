/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Chow.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.ClassGroup

/-!
# `A_{n-1}(X) ≅ Cl(X)` for an integral scheme of delta-dimension `n`

Let `X` be an integral scheme, locally of finite type over the base `C.S` of a Chow situation
`C`, of delta-dimension `n`. The Chow group `A_{n-1}(X) = Stacks.Chow.chowGroup C p (n - 1)` of
the library (Stacks 02RW) is the group of Weil divisors modulo principal divisors: the library's
`AlgebraicGeometry.weilDivisorClassGroup X` (Stacks 0BE4). The comparison is not in the library;
this file proves it, reading the library's own definition of rational equivalence
(`Stacks.Chow.IsRationallyEquivalentToZero`, a locally finite sum of pushforwards of principal
divisors from integral closed subschemes `V` of delta-dimension `n`) and showing that the only
such `V` is `X` itself, so that the pushforward is along an isomorphism.

## Main results

* `ArithmeticOfJacobiPolynomials.Chow.ord_functionFieldMap`: orders of vanishing are invariant
under an
  isomorphism of integral locally Noetherian schemes (the function-field map is the stalk map
  of the isomorphism at the generic point). The library has no such statement; it rests on the
  invariance of `Ring.ord` (a length) under ring isomorphisms (`ord_ringEquiv`).
* `ArithmeticOfJacobiPolynomials.Chow.isIso_subschemeι_of_schemeDeltaDimension_eq`: an integral
closed subscheme
  of `X` of the delta-dimension of `X` is `X`.
* `ArithmeticOfJacobiPolynomials.Chow.mem_rationalEquivalences_sub_one_iff`: an `(n - 1)`-cycle is
rationally
  equivalent to zero iff it is `x ↦ ord_x ψ` for a rational function `ψ`.
* `ArithmeticOfJacobiPolynomials.Chow.chowGroupEquivClassGroup`:
  `A_{n-1}(X) ≃+ Cl(X)`, compatible with `weilDivisorEquivCycleGroup`
  (`chowGroupEquivClassGroup_mk`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Stacks.Chow
  ArithmeticOfJacobiPolynomials.Divisors

universe u

namespace Chow

section ClosedImmersion

variable {W Y : Scheme.{u}} (f : W ⟶ Y) [IsClosedImmersion f]

/-- A closed immersion is an order embedding for the specialization order. -/
theorem le_iff_of_isClosedImmersion (a b : W) : f a ≤ f b ↔ a ≤ b := by
  rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact (IsClosedImmersion.isClosedEmbedding f).isInducing.specializes_iff

theorem lt_iff_of_isClosedImmersion (a b : W) : f a < f b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, le_iff_of_isClosedImmersion, le_iff_of_isClosedImmersion]

end ClosedImmersion

/-! ### Invariance of `Ring.ord` under ring isomorphisms -/

section RingOrd

/-- The order of vanishing `Ring.ord R a = length_R (R ⧸ (a))` is invariant under ring
isomorphisms. -/
theorem ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (σ : R ≃+* S) (a : R) :
    Ring.ord S (σ a) = Ring.ord R a := by
  have hIJ : Ideal.span {σ a} = (Ideal.span {a}).map (σ : R →+* S) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  let q := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {σ a}) σ hIJ
  let e : (R ⧸ Ideal.span {a}) ≃ₛₗ[(σ : R →+* S)] (S ⧸ Ideal.span {σ a}) :=
    { q with
      map_smul' := fun r m => by
        obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
        have hq : ∀ x, q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (σ x) := fun _ =>
          Ideal.quotientEquiv_mk ..
        change q (Ideal.Quotient.mk _ (r * m)) =
          Ideal.Quotient.mk _ (σ r) * q (Ideal.Quotient.mk _ m)
        rw [hq, hq, map_mul, map_mul] }
  have h := Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)
  apply WithBot.coe_injective
  rw [Ring.ord, Ring.ord, Module.coe_length, Module.coe_length, h]

theorem ordMonoidWithZeroHom_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] (σ : R ≃+* S) {a : R} (ha : a ≠ 0) :
    Ring.ordMonoidWithZeroHom S (σ a) = Ring.ordMonoidWithZeroHom R a := by
  have hσ : σ a ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr ha
  rw [Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha),
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero hσ), ord_ringEquiv]

end RingOrd

/-- `ord_y (A / B) = ord_y A - ord_y B`. -/
theorem ord_div {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] {A B : Y.functionField}
    (hA : A ≠ 0) (hB : B ≠ 0) (y : Y) :
    Scheme.ord (A / B) y = Scheme.ord A y - Scheme.ord B y := by
  have h := Scheme.ord_mul (x := y) (div_ne_zero hA hB) hB
  rw [div_mul_cancel₀ _ hB] at h
  omega

/-! ### Isomorphisms of integral schemes -/

section Transport

variable {W X : Scheme.{u}} (f : W ⟶ X) [IsIso f] [IsIntegral W] [IsIntegral X]

theorem specializes_genericPoint_image : f (genericPoint W) ⤳ genericPoint X :=
  (genericPoint_eq_of_isOpenImmersion f) ▸ specializes_refl _

omit [IsIso f] in
theorem genericPoint_specializes_image : genericPoint X ⤳ f (genericPoint W) :=
  (genericPoint_spec X).specializes (Set.mem_univ _)

/-- The map of function fields `K(X) → K(W)` induced by an isomorphism `f : W ⟶ X` of integral
schemes: the stalk map of `f` at the generic point. -/
@[expose] noncomputable def functionFieldMap : X.functionField →+* W.functionField :=
  (X.presheaf.stalkSpecializes (specializes_genericPoint_image f) ≫
    f.stalkMap (genericPoint W)).hom

theorem algebraMap_stalk_functionField_eq {Y : Scheme.{u}} [IsIntegral Y] (y : Y) :
    algebraMap (Y.presheaf.stalk y) Y.functionField =
      (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ y))).hom :=
  rfl

/-- Compatibility of `functionFieldMap f` with the stalk maps. -/
theorem functionFieldMap_comp_algebraMap (w : W) :
    (functionFieldMap f).comp (algebraMap (X.presheaf.stalk (f w)) X.functionField) =
      (algebraMap (W.presheaf.stalk w) W.functionField).comp (f.stalkMap w).hom := by
  have h : X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ (f w))) ≫
      X.presheaf.stalkSpecializes (specializes_genericPoint_image f) ≫
        f.stalkMap (genericPoint W) =
      f.stalkMap w ≫
        W.presheaf.stalkSpecializes ((genericPoint_spec W).specializes (Set.mem_univ w)) := by
    rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp,
      ← Scheme.Hom.stalkSpecializes_stalkMap]
  have h' := congrArg CommRingCat.Hom.hom h
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_comp] at h'
  rw [algebraMap_stalk_functionField_eq, algebraMap_stalk_functionField_eq, functionFieldMap,
    CommRingCat.hom_comp]
  exact h'

theorem functionFieldMap_algebraMap (w : W) (a : X.presheaf.stalk (f w)) :
    functionFieldMap f (algebraMap (X.presheaf.stalk (f w)) X.functionField a) =
      algebraMap (W.presheaf.stalk w) W.functionField (f.stalkMap w a) :=
  RingHom.congr_fun (functionFieldMap_comp_algebraMap f w) a

theorem functionFieldMap_surjective : Function.Surjective (functionFieldMap f) := by
  have hcomp : X.presheaf.stalkSpecializes (genericPoint_specializes_image f) ≫
      X.presheaf.stalkSpecializes (specializes_genericPoint_image f) = 𝟙 _ := by
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact TopCat.Presheaf.stalkSpecializes_refl _ _
  have h' := congrArg CommRingCat.Hom.hom hcomp
  rw [CommRingCat.hom_comp, CommRingCat.hom_id] at h'
  intro φ
  obtain ⟨t, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective f (genericPoint W) φ
  refine ⟨(X.presheaf.stalkSpecializes (genericPoint_specializes_image f)).hom t, ?_⟩
  exact congrArg (f.stalkMap (genericPoint W)).hom (RingHom.congr_fun h' t)

theorem functionFieldMap_injective : Function.Injective (functionFieldMap f) :=
  (functionFieldMap f).injective

variable [IsClosedImmersion f]

omit [IsIntegral W] [IsIntegral X] in
/-- An isomorphism (which is a closed immersion) preserves codimension. -/
theorem coheight_apply_of_isIso (w : W) : Order.coheight (f w) = Order.coheight w := by
  have hlt : ∀ a b : W, f a < f b ↔ a < b := lt_iff_of_isClosedImmersion f
  have hsurj : Function.Surjective f := (surjective_iff f).mp inferInstance
  refine le_antisymm ?_
    (Order.coheight_le_coheight_apply_of_strictMono _ (fun a b h => (hlt a b).mpr h) w)
  rw [Order.coheight_le_iff']
  intro p hp
  choose g hg using fun i => hsurj (p i)
  have hmono : StrictMono g := by
    intro i j hij
    rw [← hlt, hg, hg]
    exact p.strictMono hij
  have hhead : g 0 = w := by
    apply (IsClosedImmersion.isClosedEmbedding f).injective
    rw [hg]
    exact hp
  exact Order.length_le_coheight (p := LTSeries.mk p.length g hmono) (x := w)
    (le_of_eq hhead.symm)

variable [IsLocallyNoetherian W] [IsLocallyNoetherian X]

theorem ord_algebraMap_stalkMap {w : W} (hw : Order.coheight w = 1)
    {a : X.presheaf.stalk (f w)} (ha : a ≠ 0) :
    Scheme.ord (algebraMap (W.presheaf.stalk w) W.functionField (f.stalkMap w a)) w =
      Scheme.ord (algebraMap (X.presheaf.stalk (f w)) X.functionField a) (f w) := by
  have hfw : Order.coheight (f w) = 1 := by rw [coheight_apply_of_isIso f]; exact hw
  have : IsIso (f.stalkMap w) := ((isIso_iff_isIso_stalkMap f).mp inferInstance).2 w
  let σ : X.presheaf.stalk (f w) ≃+* W.presheaf.stalk w :=
    (asIso (f.stalkMap w)).commRingCatIsoToRingEquiv
  have hσ : ∀ b, σ b = f.stalkMap w b := fun _ => rfl
  have hσa : f.stalkMap w a ≠ 0 := by
    rw [← hσ]
    exact (map_ne_zero_iff σ σ.injective).mpr ha
  have : Ring.KrullDimLE 1 (W.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (f w)) := krullDimLE_of_coheight_le hfw.le
  have h : W.ordHom w hw (algebraMap (W.presheaf.stalk w) W.functionField (f.stalkMap w a)) =
      X.ordHom (f w) hfw (algebraMap (X.presheaf.stalk (f w)) X.functionField a) := by
    simp only [Scheme.ordHom]
    rw [Ring.ordFrac_eq_ord (hx := hσa), Ring.ordFrac_eq_ord (hx := ha), ← hσ]
    exact ordMonoidWithZeroHom_ringEquiv σ ha
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hw, Scheme.ord_eq_ordHom_of_coheight_eq_one hfw, h]

/-- **Invariance of the order of vanishing** under an isomorphism of integral schemes. -/
theorem ord_functionFieldMap (ψ : X.functionField) (w : W) :
    Scheme.ord (functionFieldMap f ψ) w = Scheme.ord ψ (f w) := by
  by_cases hw : Order.coheight w = 1
  swap
  · have hfw : Order.coheight (f w) ≠ 1 := by rwa [coheight_apply_of_isIso f]
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hw, Scheme.ord_eq_zero_of_coheight_neq_one hfw]
  by_cases hψ : ψ = 0
  · subst hψ
    simp only [map_zero, Scheme.ord_zero, Pi.zero_apply]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (f w)) ψ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hψ
    rw [map_zero, zero_div]
  have hA : algebraMap (X.presheaf.stalk (f w)) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
  have hB : algebraMap (X.presheaf.stalk (f w)) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have hA' := (map_ne_zero (functionFieldMap f)).mpr hA
  have hB' := (map_ne_zero (functionFieldMap f)).mpr hB
  rw [map_div₀, ord_div hA' hB', ord_div hA hB,
    functionFieldMap_algebraMap, functionFieldMap_algebraMap,
    ord_algebraMap_stalkMap f hw ha0, ord_algebraMap_stalkMap f hw hb0]

end Transport

/-! ### The generic point and integral closed subschemes of full dimension -/

section FullDimension

/-- On an integral scheme, the only point of coheight zero is the generic point. -/
theorem eq_genericPoint_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X] {z : X}
    (hz : Order.coheight z = 0) : z = genericPoint X := by
  have h1 : genericPoint X ⤳ z := (genericPoint_spec X).specializes (Set.mem_univ z)
  have h2 : genericPoint X ≤ z :=
    Order.coheight_eq_zero.mp hz (Scheme.le_iff_specializes.mpr h1)
  exact ((Scheme.le_iff_specializes.mp h2).antisymm h1).eq

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] {n : ℤ}

/-- **An integral closed subscheme of `X` of the delta-dimension of `X` is `X`.** Its generic
point maps to a point of `X` of delta-dimension `n`, which has coheight zero (the dimension
bridge `coheight_eq_zero_iff_relativeDimension`) and so is the generic point of `X`; hence the
closed immersion is surjective, and it is an isomorphism because `X` is reduced. -/
theorem isIso_subschemeι_of_schemeDeltaDimension_eq (hn : schemeDeltaDimension C p = (n : EInt))
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hVn : schemeDeltaDimension C (V.subschemeι ≫ p) = (n : EInt)) : IsIso V.subschemeι := by
  rw [schemeDeltaDimension_eq_genericPoint] at hVn
  have hδ : relativeDimension C.dimensionFunction (V.subschemeι ≫ p)
      (genericPoint V.subscheme) = n := WithBotTop.coe_injective hVn
  rw [relativeDimension_comp_closedImmersion] at hδ
  have hη : V.subschemeι (genericPoint V.subscheme) = genericPoint X :=
    eq_genericPoint_of_coheight_eq_zero
      ((coheight_eq_zero_iff_relativeDimension C p hn _).mpr hδ)
  have hsurj : Function.Surjective V.subschemeι := fun x =>
    ((genericPoint_spec X).specializes (Set.mem_univ x) |>.mem_closed
      (IsClosedImmersion.isClosedEmbedding V.subschemeι).isClosed_range
      ⟨genericPoint V.subscheme, hη⟩)
  have : Surjective V.subschemeι := (surjective_iff V.subschemeι).mpr hsurj
  exact isIso_of_isClosedImmersion_of_surjective V.subschemeι

/-- The delta-dimension of the closed subscheme `⊥`, which is `X`, is that of `X`. -/
theorem schemeDeltaDimension_bot_subschemeι (hn : schemeDeltaDimension C p = (n : EInt))
    (hV : IsIntegral (⊥ : X.IdealSheafData).subscheme) :
    schemeDeltaDimension C ((⊥ : X.IdealSheafData).subschemeι ≫ p) = (n : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion,
    genericPoint_eq_of_isOpenImmersion (⊥ : X.IdealSheafData).subschemeι,
    relativeDimension_genericPoint_eq C p hn]

end FullDimension

/-! ### Pushforward of principal divisors along an isomorphism -/

section Pushforward

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] [IsLocallyNoetherian X]

/-- **Pushforward of a principal divisor along the isomorphism `V ≅ X`.** If the closed
immersion `V.subschemeι` is an isomorphism (so `V = ⊥`) and `g` is the rational function of `V`
corresponding to `ψ` of `X`, the library's pushforward of `div g` is `x ↦ ord_x ψ`. -/
theorem principalDivisorPushforward_eq_ord_of_functionFieldMap (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) [IsIso V.subschemeι] (g : (rationalFunctions V.subscheme)ˣ)
    (ψ : X.functionField)
    (hψ : functionFieldMap V.subschemeι ψ =
      (rationalFunctionsEquivFunctionField V.subscheme).1 (g : rationalFunctions V.subscheme))
    (x : X) : principalDivisorPushforward C p V hV g x = X.ord ψ x := by
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ p)
  set f := V.subschemeι with hf
  have hsurj : Function.Surjective f := (surjective_iff f).mp inferInstance
  obtain ⟨w, rfl⟩ := hsurj x
  have hpre : f ⁻¹' {f w} = {w} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (IsClosedImmersion.isClosedEmbedding f).injective.eq_iff
  have hcoeff : AlgebraicCycle.mapCoeff f (relativeDimension C.dimensionFunction (f ≫ p))
      (relativeDimension C.dimensionFunction p) w = 1 := by
    simp only [AlgebraicCycle.mapCoeff,
      relativeDimension_comp_closedImmersion C.dimensionFunction f p w, ↓reduceIte]
    have : IsClosedImmersion (𝟙 V.subscheme ≫ f) := by
      rw [Category.id_comp]
      infer_instance
    exact residueDegree_eq_one_of_isClosedImmersion_comp (𝟙 V.subscheme) f w
  unfold principalDivisorPushforward
  rw [AlgebraicCycle.map, Function.locallyFinsupp.map_apply, hpre, finsum_mem_singleton, hcoeff,
    Nat.cast_one, mul_one, ← ord_functionFieldMap f ψ w, hψ]
  rfl

/-- Every rational function `g` on `V ≅ X` has the form `functionFieldMap ψ`, and then the
pushforward of `div g` is `x ↦ ord_x ψ`. -/
theorem exists_principalDivisorPushforward_eq_ord (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) [IsIso V.subschemeι] (g : (rationalFunctions V.subscheme)ˣ) :
    ∃ ψ : X.functionFieldˣ, ∀ x : X,
      principalDivisorPushforward C p V hV g x = X.ord (ψ : X.functionField) x := by
  set φ : V.subscheme.functionField :=
    (rationalFunctionsEquivFunctionField V.subscheme).1 (g : rationalFunctions V.subscheme)
    with hφ
  have hφ0 : φ ≠ 0 := fun h => g.ne_zero
    ((rationalFunctionsEquivFunctionField V.subscheme).1.injective (h.trans (map_zero _).symm))
  obtain ⟨ψ, hψ⟩ := functionFieldMap_surjective V.subschemeι φ
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    exact hφ0 (hψ.symm.trans (map_zero _))
  exact ⟨Units.mk0 ψ hψ0, principalDivisorPushforward_eq_ord_of_functionFieldMap C p V hV g ψ hψ⟩

/-- Conversely, every rational function `ψ` of `X` is the one of a rational function `g` on
`V ≅ X`. -/
theorem exists_unit_principalDivisorPushforward_eq_ord (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) [IsIso V.subschemeι] (ψ : X.functionFieldˣ) :
    ∃ g : (rationalFunctions V.subscheme)ˣ, ∀ x : X,
      principalDivisorPushforward C p V hV g x = X.ord (ψ : X.functionField) x := by
  set e := (rationalFunctionsEquivFunctionField V.subscheme).1 with he
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom
    (Units.map (functionFieldMap V.subschemeι).toMonoidHom ψ), fun x => ?_⟩
  refine principalDivisorPushforward_eq_ord_of_functionFieldMap C p V hV _ (ψ : X.functionField)
    ?_ x
  simp [he]

end Pushforward

/-! ### Rational equivalence in dimension `n - 1` -/

section RationalEquivalence

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] [IsLocallyNoetherian X] {n : ℤ}

/-- A finite sum of orders of vanishing is an order of vanishing. -/
theorem exists_sum_ord_eq {ι : Type*} (s : Finset ι) (ψ : ι → X.functionFieldˣ) :
    ∃ φ : X.functionFieldˣ, ∀ x : X,
      ∑ i ∈ s, X.ord (ψ i : X.functionField) x = X.ord (φ : X.functionField) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, fun x => ?_⟩
    have h := X.ord_mul (x := x) (one_ne_zero (α := X.functionField))
      (one_ne_zero (α := X.functionField))
    rw [one_mul] at h
    simp only [Finset.sum_empty, Units.val_one]
    omega
  | insert a s ha ih =>
    obtain ⟨φ, hφ⟩ := ih
    refine ⟨ψ a * φ, fun x => ?_⟩
    rw [Finset.sum_insert ha, hφ x, Units.val_mul]
    exact (X.ord_mul (ψ a).ne_zero φ.ne_zero).symm

/-- **Rational equivalence in dimension `n - 1` is principal-divisor equivalence.** On an integral
scheme of delta-dimension `n`, an `(n - 1)`-cycle is rationally equivalent to zero (Stacks 02RW)
iff it is `x ↦ ord_x ψ` for a rational function `ψ`. -/
theorem mem_rationalEquivalences_sub_one_iff (hn : schemeDeltaDimension C p = (n : EInt))
    (α : CycleGroup C p (n - 1)) :
    α ∈ rationalEquivalences C p (n - 1) ↔
      ∃ ψ : X.functionFieldˣ, ∀ x : X,
        (α : AlgebraicCycle X ℤ) x = X.ord (ψ : X.functionField) x := by
  constructor
  · rintro ⟨J, W, hW, hdim, hloc, g, hg⟩
    have hdim' : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = (n : EInt) := fun j => by
      simpa using hdim j
    have : ∀ j, IsIso (W j).subschemeι := fun j =>
      isIso_subschemeι_of_schemeDeltaDimension_eq C p hn (W j) (hW j) (hdim' j)
    choose ψ hψ using fun j => exists_principalDivisorPushforward_eq_ord C p (W j) (hW j) (g j)
    -- every support is everything, so a locally finite family is finite
    have hsupp : ∀ j, ((W j).support : Set X) = Set.univ := fun j => by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.range_eq_univ.mpr ((surjective_iff (W j).subschemeι).mp inferInstance)
    have : Finite J := by
      obtain ⟨U, hU, hfin⟩ := hloc (genericPoint X)
      have hne : (U ∩ Set.univ).Nonempty := ⟨genericPoint X, mem_of_mem_nhds hU, trivial⟩
      refine Set.finite_univ_iff.mp (hfin.subset fun j _ => ?_)
      simpa [hsupp j] using hne
    have := Fintype.ofFinite J
    obtain ⟨φ, hφ⟩ := exists_sum_ord_eq (X := X) Finset.univ ψ
    refine ⟨φ, fun x => ?_⟩
    rw [hg x, ← hφ x]
    unfold principalDivisorFamilyCoefficient
    rw [finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun j _ => hψ j x
  · rintro ⟨ψ, hψ⟩
    have : IsIso (⊥ : X.IdealSheafData).subschemeι := inferInstance
    have : Nonempty (⊥ : X.IdealSheafData).subscheme :=
      ⟨(inv (⊥ : X.IdealSheafData).subschemeι).base (genericPoint X)⟩
    have hV : IsIntegral (⊥ : X.IdealSheafData).subscheme :=
      isIntegral_of_isOpenImmersion (⊥ : X.IdealSheafData).subschemeι
    obtain ⟨g, hg⟩ := exists_unit_principalDivisorPushforward_eq_ord C p
      (⊥ : X.IdealSheafData) hV ψ
    refine ⟨PUnit.{u + 1}, fun _ => ⊥, fun _ => hV,
      fun _ => by simpa using schemeDeltaDimension_bot_subschemeι C p hn hV,
      locallyFinite_of_finite _, fun _ => g, fun x => ?_⟩
    unfold principalDivisorFamilyCoefficient
    rw [finsum_unique, hg x, hψ x]

/-- A Weil divisor has principal class iff its cycle is rationally equivalent to zero. -/
theorem weilDivisorEquivCycleGroup_mem_rationalEquivalences_iff
    (hn : schemeDeltaDimension C p = (n : EInt)) (D : WeilDivisor X) :
    weilDivisorEquivCycleGroup C p hn D ∈ rationalEquivalences C p (n - 1) ↔
      D ∈ principalWeilDivisors X := by
  set e := (rationalFunctionsEquivFunctionField X).1 with he
  rw [mem_rationalEquivalences_sub_one_iff C p hn, mem_principalWeilDivisors_iff]
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨Units.map e.symm.toRingHom.toMonoidHom ψ, cycleOfWeilDivisor_injective
      (Function.locallyFinsuppWithin.ext fun x => ?_)⟩
    rw [cycleOfWeilDivisor_principalDivisor]
    have h1 : e (e.symm (ψ : X.functionField)) = ψ := e.apply_symm_apply _
    exact (congrArg (fun y => X.ord y x) h1).trans (hψ x).symm
  · rintro ⟨f, rfl⟩
    refine ⟨Units.map e.toRingHom.toMonoidHom f, fun x => ?_⟩
    exact cycleOfWeilDivisor_principalDivisor f x

/-- **`A_{n-1}(X) ≅ Cl(X)`.** For an integral scheme `X` of delta-dimension `n`, locally of finite
type over the base of a Chow situation, the Chow group `A_{n-1}(X)` of the library (Stacks 02RW)
is the Weil divisor class group `Cl(X)` (Stacks 0BE4), by `weilDivisorEquivCycleGroup`. -/
@[expose] noncomputable def chowGroupEquivClassGroup (hn : schemeDeltaDimension C p = (n : EInt)) :
    chowGroup C p (n - 1) ≃+ weilDivisorClassGroup X :=
  (QuotientAddGroup.congr (principalWeilDivisors X) (rationalEquivalences C p (n - 1))
    (weilDivisorEquivCycleGroup C p hn) (by
      ext z
      obtain ⟨D, rfl⟩ := (weilDivisorEquivCycleGroup C p hn).surjective z
      rw [weilDivisorEquivCycleGroup_mem_rationalEquivalences_iff C p hn D,
        AddSubgroup.mem_map]
      constructor
      · rintro ⟨D', hD', h⟩
        obtain rfl := (weilDivisorEquivCycleGroup C p hn).injective h
        exact hD'
      · intro h
        exact ⟨D, h, rfl⟩)).symm

/-- The class of the cycle of `D` in `A_{n-1}(X)` corresponds to the class of `D` in `Cl(X)`. -/
theorem chowGroupEquivClassGroup_mk (hn : schemeDeltaDimension C p = (n : EInt))
    (D : WeilDivisor X) :
    chowGroupEquivClassGroup C p hn
      (QuotientAddGroup.mk (weilDivisorEquivCycleGroup C p hn D)) =
        (QuotientAddGroup.mk D : weilDivisorClassGroup X) := by
  rw [chowGroupEquivClassGroup, AddEquiv.symm_apply_eq]
  rfl

end RationalEquivalence

section Curve

/-- **`A_0(X) ≅ Cl(X)` for an integral curve over a field**: an integral scheme `X` of
topological dimension one, locally of finite type over `k`, has delta-dimension one over
`fieldChowSituation k`, and `1 - 1 = 0`. -/
@[expose] noncomputable def chowGroupZeroEquivClassGroup (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [IsIntegral X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X = 1) :
    chowGroup (fieldChowSituation k) p 0 ≃+ weilDivisorClassGroup X :=
  chowGroupEquivClassGroup (fieldChowSituation k) p (n := 1)
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq (n := 1) p
      (by rw [hdim]; rfl))

end Curve

end Chow

end ArithmeticOfJacobiPolynomials
