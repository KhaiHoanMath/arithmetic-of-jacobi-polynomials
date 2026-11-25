/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.InertiaCyclePadic

/-!
# Lemma 5.1, local form: the other roots lie in an unramified extension of `ℚ_p`

Let `K` be a finite Galois extension of `ℚ_[p]`,
`𝒪_K = integralClosure ℤ_[p] K`, `P` a height one prime of `𝒪_K` over the maximal ideal of
`ℤ_[p]`, `I = I_P ≤ Gal(K/ℚ_[p])` its inertia group and `T = K^I` the inertia field
(`inertiaField P`). For an intermediate field `E` we write `𝒪_E = integralClosure ℤ_[p] E`; it
is a Dedekind domain, `𝒪_K` is a finite flat `𝒪_E`-algebra, and `Gal(K/E)` is a Galois group
of `𝒪_K/𝒪_E` (instances below).

## Results

* `ramificationIdx_under_eq_one_of_le_inertiaField`: for every intermediate field `E ≤ T`, the
  contraction `P ∩ 𝒪_E` has ramification index `1` over `p`. The proof follows the global
  `UnequalParameters.ramificationIdx_under_inertiaField`: `|I| = e(P/p)`,
  `|I_P(K/E)| = e(P/P ∩ 𝒪_E)`, `I ≤ I_P(K/E)` (as `I` fixes `E`), and
  `e(P/p) = e(P ∩ 𝒪_E/p) · e(P/P ∩ 𝒪_E)`.
* `ramificationIdx_under_inertiaField`: the case `E = T` (`T/ℚ_p` is unramified at
  `P ∩ 𝒪_T`).
* `mem_inertiaField_of_valuation_le_one`: for `f` as in Lemma 5.1 (`LocalHyp p d f`), every root
  `y` of `f` in `K` with `v_P y ≤ 1` lies in `T` (it is fixed by inertia,
  `apply_eq_of_mem_inertia`).
* `unramifiedRootsField P f = ℚ_p(y : f(y) = 0, v_P y ≤ 1)`:
  `unramifiedRootsField_le_inertiaField` and `ramificationIdx_under_unramifiedRootsField`, i.e.
  the `N - d` "other" roots generate an extension of `ℚ_p` in which `p` is unramified (stated
  at the prime below `P`).
* Splitting-field forms: `rootSet_mem_inertiaField`,
  `ramificationIdx_under_unramifiedRootsField_splittingField`.

We state "unramified" as `ramificationIdx = 1` of the contracted prime (the form of the global
analogue); the residue field extensions are finite, hence separable.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace InertiaCyclePadic

open Polynomial IsDedekindDomain LocalRootResidues

/-- An elementary step: `a * b ≤ b` and `0 < a * b` force `a = 1`. -/
theorem eq_one_of_mul_le_of_pos {a b : ℕ} (h : a * b ≤ b) (hpos : 0 < a * b) : a = 1 := by
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have : a ≤ 1 := by nlinarith
  omega

section Tower

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [Algebra ℚ_[p] K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] (E : IntermediateField ℚ_[p] K)

instance isScalarTower_padicInt_intermediateField : IsScalarTower ℤ_[p] E K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The ring of integers `𝒪_E` of an intermediate field maps into `𝒪_K`. -/
noncomputable instance algebraIntegralClosureIntermediateField :
    Algebra (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) :=
  (IsScalarTower.toAlgHom ℤ_[p] E K).mapIntegralClosure.toRingHom.toAlgebra

theorem coe_algebraMap_integralClosure (a : integralClosure ℤ_[p] E) :
    ((algebraMap (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) a :
      integralClosure ℤ_[p] K) : K) = ((a : E) : K) := rfl

instance isScalarTower_integralClosure_intermediateField :
    IsScalarTower ℤ_[p] (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    Subtype.ext (IsScalarTower.algebraMap_apply ℤ_[p] E K r)

instance isScalarTower_integralClosure_intermediateField_field :
    IsScalarTower (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_integralClosure_intermediateField_mid :
    IsScalarTower (integralClosure ℤ_[p] E) E K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_integralClosure_intermediateField_injective :
    Function.Injective (algebraMap (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K)) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

instance isTorsionFree_integralClosure_intermediateField :
    Module.IsTorsionFree (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact algebraMap_integralClosure_intermediateField_injective E

instance smulCommClass_integralClosure_intermediateField :
    SMulCommClass Gal(K/E) (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) :=
  ⟨fun σ a b => by
    apply Subtype.ext
    change σ (((a : E) : K) * (b : K)) = ((a : E) : K) * σ (b : K)
    rw [map_mul]
    congr 1
    exact σ.commutes (a : E)⟩

variable [FiniteDimensional ℚ_[p] K]

instance finite_integralClosure_intermediateField :
    Module.Finite (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) :=
  Module.Finite.of_restrictScalars_finite ℤ_[p] _ _

instance flat_integralClosure_intermediateField :
    Module.Flat (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) :=
  Module.Flat.instOfIsDedekindDomainOfIsTorsionFree

instance isGaloisGroup_integralClosure_intermediateField [IsGalois ℚ_[p] K] :
    IsGaloisGroup Gal(K/E) (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] K) :=
  IsGaloisGroup.of_isFractionRing _ _ _ E K

end Tower

section Inertia

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [Algebra ℚ_[p] K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
  (P : HeightOneSpectrum (integralClosure ℤ_[p] K))

/-- The inertia field `T = K^{I_P}` of `P` over `ℚ_[p]`. -/
noncomputable abbrev inertiaField : IntermediateField ℚ_[p] K :=
  IntermediateField.fixedField (P.asIdeal.inertia Gal(K/ℚ_[p]))

variable [FiniteDimensional ℚ_[p] K]

/-- The subfield `ℚ_p(y : f(y) = 0, v_P y ≤ 1)` generated by the roots of `f` with
`v_P y ≤ 1` (the "other" roots of Lemma 5.1). -/
@[expose] noncomputable def unramifiedRootsField (f : ℤ_[p][X]) : IntermediateField ℚ_[p] K :=
  IntermediateField.adjoin ℚ_[p]
    {y : K | (f.map (algebraMap ℤ_[p] K)).eval y = 0 ∧ P.valuation K y ≤ 1}

variable [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

omit [FiniteDimensional ℚ_[p] K] in
theorem liesOver_under_intermediateField (E : IntermediateField ℚ_[p] K) :
    (P.asIdeal.under (integralClosure ℤ_[p] E)).LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) :=
  ⟨by rw [Ideal.under_under]; exact Ideal.over_def P.asIdeal _⟩

variable {d : ℕ} {f : ℤ_[p][X]}

/-- **Lemma 5.1, the other roots lie in the inertia field.** Every root `y` of `f` in `K` with
`v_P y ≤ 1` lies in `T = K^{I_P}`. -/
theorem mem_inertiaField_of_valuation_le_one (hf : LocalHyp p d f) {y : K}
    (hy : (f.map (algebraMap ℤ_[p] K)).eval y = 0) (hy1 : P.valuation K y ≤ 1) :
    y ∈ inertiaField P :=
  (IntermediateField.mem_fixedField_iff _ _).mpr fun _ hσ =>
    apply_eq_of_mem_inertia P hf hσ hy hy1

/-- The field generated by the other roots lies in the inertia field. -/
theorem unramifiedRootsField_le_inertiaField (hf : LocalHyp p d f) :
    unramifiedRootsField P f ≤ inertiaField P :=
  IntermediateField.adjoin_le_iff.mpr fun _ hy =>
    mem_inertiaField_of_valuation_le_one P hf hy.1 hy.2

variable [IsGalois ℚ_[p] K]

/-- `|I_P(K/E)| = e(P / P ∩ 𝒪_E)`. -/
theorem card_inertia_intermediateField (E : IntermediateField ℚ_[p] K) :
    Nat.card (P.asIdeal.inertia Gal(K/E)) =
      P.asIdeal.ramificationIdx (integralClosure ℤ_[p] E) := by
  have hQm := liesOver_under_intermediateField P E
  have hPQ : P.asIdeal.LiesOver (P.asIdeal.under (integralClosure ℤ_[p] E)) := ⟨rfl⟩
  have hfin0 : Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
    Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  have hfinQ :
      Finite (integralClosure ℤ_[p] E ⧸ P.asIdeal.under (integralClosure ℤ_[p] E)) := by
    let _ : Algebra (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
        (integralClosure ℤ_[p] E ⧸ P.asIdeal.under (integralClosure ℤ_[p] E)) :=
      Ideal.Quotient.algebraOfLiesOver _ _
    let _ : Module (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
        (integralClosure ℤ_[p] E ⧸ P.asIdeal.under (integralClosure ℤ_[p] E)) :=
      Algebra.toModule
    have : Module.Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
        (integralClosure ℤ_[p] E ⧸ P.asIdeal.under (integralClosure ℤ_[p] E)) :=
      module_finite_of_liesOver _ _
    exact Module.finite_of_finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
  rw [Ideal.card_inertia_eq_ramificationIdxIn (P.asIdeal.under (integralClosure ℤ_[p] E))
    P.asIdeal]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx _ P.asIdeal Gal(K/E)

/-- **Subfields of the inertia field are unramified.** For an intermediate field `E ≤ K^{I_P}`,
the contraction `P ∩ 𝒪_E` has ramification index `1` over `p`. -/
theorem ramificationIdx_under_eq_one_of_le_inertiaField (E : IntermediateField ℚ_[p] K)
    (hE : E ≤ inertiaField P) :
    (P.asIdeal.under (integralClosure ℤ_[p] E)).ramificationIdx ℤ_[p] = 1 := by
  have hQm := liesOver_under_intermediateField P E
  have hPQ : P.asIdeal.LiesOver (P.asIdeal.under (integralClosure ℤ_[p] E)) := ⟨rfl⟩
  have hle : P.asIdeal.inertia Gal(K/ℚ_[p]) ≤ E.fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).mp hE
  let φ : P.asIdeal.inertia Gal(K/ℚ_[p]) → P.asIdeal.inertia Gal(K/E) := fun σ =>
    ⟨IntermediateField.fixingSubgroupEquiv E ⟨σ.1, hle σ.2⟩,
      Ideal.mem_inertia.mpr fun b => Ideal.mem_inertia.mp σ.2 b⟩
  have hφ : Function.Injective φ := by
    intro σ τ h
    have h1 := (IntermediateField.fixingSubgroupEquiv E).injective (congrArg Subtype.val h)
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hcard : Nat.card (P.asIdeal.inertia Gal(K/ℚ_[p])) ≤
      Nat.card (P.asIdeal.inertia Gal(K/E)) :=
    Nat.card_le_card_of_injective φ hφ
  have hpos : 0 < Nat.card (P.asIdeal.inertia Gal(K/ℚ_[p])) := Nat.card_pos
  rw [card_inertia P] at hcard hpos
  rw [card_inertia_intermediateField P E] at hcard
  have h3 := Ideal.ramificationIdx_tower (R := ℤ_[p])
    (q := P.asIdeal.under (integralClosure ℤ_[p] E)) (r := P.asIdeal)
  rw [h3] at hcard hpos
  exact eq_one_of_mul_le_of_pos hcard hpos

/-- **The inertia field is unramified** (local form of `ramificationIdx_under_inertiaField`):
`P ∩ 𝒪_T` has ramification index `1` over `p`, `T = K^{I_P}`. -/
theorem ramificationIdx_under_inertiaField :
    (P.asIdeal.under (integralClosure ℤ_[p] (inertiaField P))).ramificationIdx ℤ_[p] = 1 :=
  ramificationIdx_under_eq_one_of_le_inertiaField P _ le_rfl

/-- **Lemma 5.1, the other roots lie in an unramified extension of `ℚ_p`.** The contraction of
`P` to the ring of integers of `ℚ_p(y : f(y) = 0, v_P y ≤ 1)` has ramification index `1`. -/
theorem ramificationIdx_under_unramifiedRootsField (hf : LocalHyp p d f) :
    (P.asIdeal.under (integralClosure ℤ_[p] (unramifiedRootsField P f))).ramificationIdx
      ℤ_[p] = 1 :=
  ramificationIdx_under_eq_one_of_le_inertiaField P _ (unramifiedRootsField_le_inertiaField P hf)

end Inertia

section SplittingField

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} {f : ℤ_[p][X]}

/-- **Lemma 5.1, splitting-field form.** Every root `x` of `f` in its splitting field `K` over
`ℚ_[p]` with `v_P x ≤ 1` lies in the inertia field `K^{I_P}`. -/
theorem rootSet_mem_inertiaField (hf : LocalHyp p d f)
    (P : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic f).SplittingField))
    [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (x : (toPadic f).rootSet (toPadic f).SplittingField)
    (hx : P.valuation (toPadic f).SplittingField (x : (toPadic f).SplittingField) ≤ 1) :
    (x : (toPadic f).SplittingField) ∈ inertiaField P := by
  have : IsGalois ℚ_[p] (toPadic f).SplittingField := IsGalois.mk
  exact mem_inertiaField_of_valuation_le_one P hf ((mem_rootSet_toPadic_iff hf x).mp x.2) hx

/-- **Lemma 5.1, splitting-field form.** With `K` the splitting field of `f` over `ℚ_[p]`, the
roots `y` of `f` with `v_P y ≤ 1` generate an extension of `ℚ_p` contained in the inertia field,
in which the prime below `P` has ramification index `1` over `p`. -/
theorem ramificationIdx_under_unramifiedRootsField_splittingField (hf : LocalHyp p d f)
    (P : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic f).SplittingField))
    [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    unramifiedRootsField P f ≤ inertiaField P ∧
      (P.asIdeal.under (integralClosure ℤ_[p] (unramifiedRootsField P f))).ramificationIdx
        ℤ_[p] = 1 := by
  have : IsGalois ℚ_[p] (toPadic f).SplittingField := IsGalois.mk
  exact ⟨unramifiedRootsField_le_inertiaField P hf,
    ramificationIdx_under_unramifiedRootsField P hf⟩

end SplittingField

end InertiaCyclePadic

end ArithmeticOfJacobiPolynomials
