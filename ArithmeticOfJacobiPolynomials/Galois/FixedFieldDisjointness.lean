/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.Transitivity
public import Mathlib

/-!
# Inertia at unramified primes and linear disjointness (the fixed-field step)

This file formalizes the argument of Corollary 5.14 (and of the fixed-field assertion of
Theorem 1.3) that turns inertia elements into linear disjointness from a fixed number field.

Let `K/ℚ` be a finite Galois extension and `E` a number field with Galois closure `E'`.

* If `F ⊆ K` is Galois over `ℚ` and `p` is unramified in `F`, then every inertia subgroup at a
  prime of `𝓞 K` above `p` acts trivially on `F` (`inertia_le_fixingSubgroup`): restriction maps
  it into an inertia group of `F`, whose order is the ramification index `1`.
* Hence, if the inertia subgroups at a set of such primes normally generate `Gal(K/ℚ)`, then
  `F = ℚ` (`eq_bot_of_inertia_normal_generation`).
* Applied to `F = K ∩ E'` inside an algebraic closure of `ℚ`, with every prime `p` above the
  bound `R = |disc E'|` unramified in `F` (as `disc F ∣ disc E'`), this gives `K ∩ E = ℚ`, so
  `K` and `E` are linearly disjoint over `ℚ` and `K ⊗[ℚ] E` is a field
  (`exists_bound_isField_tensorProduct`, `exists_bound_isField_splittingField_tensorProduct`).
* If `K = f.SplittingField` and `K ⊗[ℚ] E` is a field, restriction `Gal(f/E) → Gal(f/ℚ)` is
  bijective and compatible with the actions on the roots (`exists_restrict_bijective`), so
  irreducibility, `Gal = S_n` and `Gal = W_m` pass from `ℚ` to `E`
  (`irreducible_map_of_isField_tensorProduct`,
  `galoisGroupIsSymmetric_map_of_isField_tensorProduct`,
  `galoisGroupIsWreath_map_of_isField_tensorProduct`; all packaged in
  `exists_bound_fixedField`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial NumberField TensorProduct

namespace FixedFieldDisjointness

universe u

theorem isPrime_span_natCast {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsPrime := by
  have : Fact p.Prime := ⟨hp⟩
  exact (Int.ideal_span_isMaximal_of_prime p).isPrime

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in
/-- **Inertia acts trivially on an unramified Galois subextension.** Let `K/ℚ` be a finite
extension, `F ⊆ K` an intermediate field Galois over `ℚ` and `p` a prime unramified in
`F`. Then the inertia group of every prime of `𝓞 K` above `p` fixes `F` pointwise. -/
theorem inertia_le_fixingSubgroup (F : IntermediateField ℚ K) [IsGalois ℚ F] {p : ℕ}
    (hp : p.Prime) (hF : Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)}))
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.inertia Gal(K/ℚ) ≤ F.fixingSubgroup := by
  intro σ hσ
  have := isPrime_span_natCast hp
  rw [Ideal.mem_inertia] at hσ
  have hQp : (P.comap (RingOfIntegers.mapRingHom (algebraMap F K))).IsPrime :=
    Ideal.comap_isPrime _ P
  have hQl : (P.comap (RingOfIntegers.mapRingHom (algebraMap F K))).LiesOver
      (Ideal.span {(p : ℤ)}) :=
    inferInstanceAs ((P.comap (RingOfIntegers.mapRingHom (algebraMap F K)).toIntAlgHom).LiesOver
      (Ideal.span {(p : ℤ)}))
  have hτ : (σ.restrictNormal F : Gal(F/ℚ)) ∈
      (P.comap (RingOfIntegers.mapRingHom (algebraMap F K))).inertia Gal(F/ℚ) := by
    refine Ideal.mem_inertia.mpr fun x => ?_
    rw [Ideal.mem_comap, map_sub]
    have e : RingOfIntegers.mapRingHom (algebraMap F K) ((σ.restrictNormal F : Gal(F/ℚ)) • x) =
        σ • RingOfIntegers.mapRingHom (algebraMap F K) x := by
      apply RingOfIntegers.ext
      rw [RingOfIntegers.mapRingHom_apply]
      exact AlgEquiv.restrictNormal_commutes σ F (x : F)
    rw [e]
    exact hσ _
  have hcard : Nat.card
      ((P.comap (RingOfIntegers.mapRingHom (algebraMap F K))).inertia Gal(F/ℚ)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(p : ℤ)})
      (P.comap (RingOfIntegers.mapRingHom (algebraMap F K))),
      Ideal.ramificationIdxIn_eq_ramificationIdx _
        (P.comap (RingOfIntegers.mapRingHom (algebraMap F K))) Gal(F/ℚ)]
    exact Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mp hF _ hQl
  have h1 : (σ.restrictNormal F : Gal(F/ℚ)) = 1 := by
    have : Subsingleton
        ((P.comap (RingOfIntegers.mapRingHom (algebraMap F K))).inertia Gal(F/ℚ)) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨_, hτ⟩ :
      (P.comap (RingOfIntegers.mapRingHom (algebraMap F K))).inertia Gal(F/ℚ)) 1)
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h := AlgEquiv.restrictNormal_commutes σ F ⟨x, hx⟩
  rw [h1] at h
  simpa using h.symm

/-- **Normal generation by inertia forces `F = ℚ`.** Let `F ⊆ K` be Galois over `ℚ` and `S` a
set of primes unramified in `F`. If every normal subgroup of `Gal(K/ℚ)` containing all inertia
groups at primes of `𝓞 K` above the primes of `S` is the whole group, then `F = ℚ`. -/
theorem eq_bot_of_inertia_normal_generation (F : IntermediateField ℚ K) [hF : IsGalois ℚ F]
    (S : Set ℕ) (hS : ∀ p ∈ S, p.Prime ∧ Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)}))
    (hgen : ∀ N : Subgroup Gal(K/ℚ), N.Normal →
      (∀ p ∈ S, ∀ (P : Ideal (𝓞 K)) [P.IsPrime], P.LiesOver (Ideal.span {(p : ℤ)}) →
        P.inertia Gal(K/ℚ) ≤ N) → N = ⊤) :
    F = ⊥ := by
  have htop : F.fixingSubgroup = ⊤ := hgen _ inferInstance fun p hp P _ hP => by
    have := hP
    exact inertia_le_fixingSubgroup F (hS p hp).1 (hS p hp).2 P
  rw [← IsGalois.fixedField_fixingSubgroup F, htop, ← IntermediateField.fixingSubgroup_bot,
    IsGalois.fixedField_fixingSubgroup]

theorem not_dvd_of_natAbs_lt {d : ℤ} (hd : d ≠ 0) {p : ℕ} (hp : d.natAbs < p) :
    ¬ (p : ℤ) ∣ d := by
  intro h
  have h' : p ∣ d.natAbs := Int.ofNat_dvd_left.mp h
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) h'
  omega

/-- **Linear disjointness from a fixed number field.** For a number field `E` there is a bound
`R` (namely `|disc E'|` for a Galois closure `E'` of `E`) such that for every finite Galois
extension `K/ℚ` whose Galois group is normally generated by the inertia groups at primes
`p > R`, the algebra `K ⊗[ℚ] E` is a field, i.e. `K` and `E` are linearly disjoint over `ℚ`. -/
theorem exists_bound_isField_tensorProduct (E : Type*) [Field E] [NumberField E] :
    ∃ R : ℕ, ∀ (K : Type u) [Field K] [NumberField K] [IsGalois ℚ K],
      (∀ N : Subgroup Gal(K/ℚ), N.Normal →
        (∀ p : ℕ, p.Prime → R < p → ∀ (P : Ideal (𝓞 K)) [P.IsPrime],
          P.LiesOver (Ideal.span {(p : ℤ)}) → P.inertia Gal(K/ℚ) ≤ N) → N = ⊤) →
      IsField (K ⊗[ℚ] E) := by
  -- a Galois closure `E'` of `E`: the splitting field of the minimal polynomial of a primitive
  -- element
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ E
  let E' := (minpoly ℚ pb.gen).SplittingField
  have : NumberField E' := ⟨⟩
  have : IsGalois ℚ E' := IsGalois.mk
  have hint : IsIntegral ℚ pb.gen := Algebra.IsIntegral.isIntegral _
  obtain ⟨y, hy⟩ := (SplittingField.splits (minpoly ℚ pb.gen)).exists_eval_eq_zero
    (by rw [degree_map]; exact (minpoly.degree_pos hint).ne')
  rw [eval_map_algebraMap] at hy
  let ιE : E →ₐ[ℚ] E' := pb.lift y hy
  let fe : E' →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let fb : E →ₐ[ℚ] AlgebraicClosure ℚ := fe.comp ιE
  refine ⟨(discr E').natAbs, ?_⟩
  intro K _ _ _ hgen
  let fa : K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  have hfaG := IsGalois.of_algEquiv fa.equivFieldRange
  have hfeG := IsGalois.of_algEquiv fe.equivFieldRange
  have hfaF := LinearEquiv.finiteDimensional fa.equivFieldRange.toLinearEquiv
  have hfbF := LinearEquiv.finiteDimensional fb.equivFieldRange.toLinearEquiv
  have hAG := FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMin
    fa.fieldRange fe.fieldRange
  have hAle : fa.fieldRange ⊓ fe.fieldRange ≤ fa.fieldRange := inf_le_left
  let F : IntermediateField ℚ K := (fa.fieldRange ⊓ fe.fieldRange).comap fa
  have hmap : F.map fa = fa.fieldRange ⊓ fe.fieldRange := by
    ext z
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      obtain ⟨x, rfl⟩ := (AlgHom.mem_fieldRange).mp (hAle hz)
      exact ⟨x, hz, rfl⟩
  let eF : F ≃ₐ[ℚ] ↥(fa.fieldRange ⊓ fe.fieldRange) :=
    (IntermediateField.equivMap F fa).trans (IntermediateField.equivOfEq hmap)
  have hFG := IsGalois.of_algEquiv eF.symm
  let _ : Algebra F E' :=
    ((fe.equivFieldRange.symm.toRingHom.comp
      (IntermediateField.inclusion
        (inf_le_right : fa.fieldRange ⊓ fe.fieldRange ≤ fe.fieldRange)).toRingHom).comp
      eF.toRingHom).toAlgebra
  have hunr : ∀ p : ℕ, p.Prime → (discr E').natAbs < p →
      Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)}) := by
    intro p hp hR
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hnd : ¬ (p : ℤ) ∣ discr F := fun h =>
      not_dvd_of_natAbs_lt (discr_ne_zero E') hR (h.trans (discr_dvd_discr F E'))
    exact (not_dvd_discr_iff_isUnramifiedIn F (𝓞 F) hpZ).mp hnd
  have hFbot : F = ⊥ :=
    eq_bot_of_inertia_normal_generation (hF := hFG) F {p | p.Prime ∧ (discr E').natAbs < p}
      (fun p hp => ⟨hp.1, hunr p hp.1 hp.2⟩)
      (fun N hN h => hgen N hN fun p hp hR P _ hP => h p ⟨hp, hR⟩ P hP)
  have hAbot : fa.fieldRange ⊓ fe.fieldRange = ⊥ := by
    rw [← hmap, hFbot, IntermediateField.map_bot]
  have hinf : fa.fieldRange ⊓ fb.fieldRange = ⊥ := by
    rw [eq_bot_iff, ← hAbot]
    refine inf_le_inf_left _ fun x hx => ?_
    obtain ⟨z, rfl⟩ := (AlgHom.mem_fieldRange).mp hx
    exact (AlgHom.mem_fieldRange).mpr ⟨ιE z, rfl⟩
  have hld : fa.fieldRange.LinearDisjoint fb.fieldRange :=
    IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  exact hld.isField_of_isAlgebraic' (Or.inl inferInstance)

/-- `exists_bound_isField_tensorProduct` for the splitting field of `f ∈ ℚ[X]`, with its Galois
group written as `Gal(f/ℚ)`. -/
theorem exists_bound_isField_splittingField_tensorProduct (E : Type*) [Field E]
    [NumberField E] :
    ∃ R : ℕ, ∀ f : ℚ[X],
      (∀ N : Subgroup f.Gal, N.Normal →
        (∀ p : ℕ, p.Prime → R < p → ∀ (P : Ideal (𝓞 f.SplittingField)) [P.IsPrime],
          P.LiesOver (Ideal.span {(p : ℤ)}) → P.inertia Gal(f.SplittingField/ℚ) ≤ N) →
        N = ⊤) →
      IsField (f.SplittingField ⊗[ℚ] E) := by
  obtain ⟨R, hR⟩ := exists_bound_isField_tensorProduct.{0} E
  refine ⟨R, fun f hgen => ?_⟩
  have : NumberField f.SplittingField := ⟨⟩
  have : IsGalois ℚ f.SplittingField := IsGalois.mk
  exact hR f.SplittingField hgen

section Transfer

variable {E : Type*} [Field E] [NumberField E]

theorem splits_map_splittingField_map (f : ℚ[X]) (E : Type*) [Field E] [CharZero E] :
    (f.map (algebraMap ℚ (f.map (algebraMap ℚ E)).SplittingField)).Splits := by
  rw [IsScalarTower.algebraMap_eq ℚ E (f.map (algebraMap ℚ E)).SplittingField,
    ← Polynomial.map_map]
  exact SplittingField.splits _

/-- **Base change of the Galois group to a linearly disjoint field.** If `K ⊗[ℚ] E` is a field,
`K` the splitting field of `f ∈ ℚ[X]`, then restriction `Gal(f/E) → Gal(f/ℚ)` is bijective, and
it intertwines the actions on the roots through a bijection `β` of the root sets which commutes
with negation. -/
theorem exists_restrict_bijective {f : ℚ[X]} (h : IsField (f.SplittingField ⊗[ℚ] E)) :
    ∃ (r : (f.map (algebraMap ℚ E)).Gal →* f.Gal)
      (β : f.rootSet f.SplittingField ≃
        (f.map (algebraMap ℚ E)).rootSet (f.map (algebraMap ℚ E)).SplittingField),
      Function.Bijective r ∧
      (∀ σ, galPerm (f.map (algebraMap ℚ E)) σ = β.permCongr (galPerm f (r σ))) ∧
      ∀ a b : f.rootSet f.SplittingField,
        (((β b : _) : (f.map (algebraMap ℚ E)).SplittingField) = -((β a : _) : _) ↔
          (b : f.SplittingField) = -(a : f.SplittingField)) := by
  classical
  have hroot : (f.map (algebraMap ℚ E)).rootSet (f.map (algebraMap ℚ E)).SplittingField =
      f.rootSet (f.map (algebraMap ℚ E)).SplittingField := by
    rw [Polynomial.rootSet_map]
  have hfact : Fact ((f.map (algebraMap ℚ (f.map (algebraMap ℚ E)).SplittingField)).Splits) :=
    ⟨splits_map_splittingField_map f E⟩
  set g := f.map (algebraMap ℚ E) with hg
  set K := f.SplittingField with hK
  set L := g.SplittingField with hL
  let ψ := Gal.rootsEquivRootsAux f L
  let χ : f.rootSet L ≃ g.rootSet L := Equiv.subtypeEquivRight (fun x => by rw [hroot])
  let β : f.rootSet K ≃ g.rootSet L := ψ.trans χ
  let rs : g.Gal →* Gal(L/ℚ) :=
    MonoidHom.mk' (fun σ : g.Gal => (σ.restrictScalars ℚ : Gal(L/ℚ)))
      (fun _ _ => AlgEquiv.ext fun _ => rfl)
  let r : g.Gal →* f.Gal := (Gal.restrict f L).comp rs
  have hperm : ∀ σ, galPerm g σ = β.permCongr (galPerm f (r σ)) := by
    intro σ
    ext1 y
    apply Subtype.ext
    rw [Equiv.permCongr_apply]
    have h1 : ((β (galPerm f (r σ) (β.symm y)) : g.rootSet L) : L) =
        ((r σ • χ.symm y : f.rootSet L) : L) := by
      rw [Gal.smul_def, galPerm_apply]
      rfl
    rw [h1]
    exact (Gal.restrict_smul (p := f) (E := L) (σ.restrictScalars ℚ) (χ.symm y)).symm
  have hinj : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply galPerm_injective g
    rw [hperm σ, hσ, map_one (galPerm f), map_one (galPerm g)]
    ext1 y
    simp
  have : IsGalois E L := IsGalois.mk
  have : IsGalois ℚ K := IsGalois.mk
  have : FiniteDimensional ℚ L := Module.Finite.trans E L
  have hcardL : Nat.card g.Gal = Module.finrank E L := IsGalois.card_aut_eq_finrank E L
  have hcardK : Nat.card f.Gal = Module.finrank ℚ K := IsGalois.card_aut_eq_finrank ℚ K
  let ι : K →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ K L
  let j : E →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ E L
  have hle : Module.finrank ℚ K * Module.finrank ℚ E ≤
      Module.finrank ℚ E * Module.finrank E L := by
    rw [← Module.finrank_tensorProduct, Module.finrank_mul_finrank]
    let := h.toField
    exact LinearMap.finrank_le_finrank_of_injective
      (f := (Algebra.TensorProduct.productMap ι j).toLinearMap)
      (Algebra.TensorProduct.productMap ι j).toRingHom.injective
  have hEpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hKL : Module.finrank ℚ K ≤ Module.finrank E L := by
    rw [mul_comm] at hle
    exact Nat.le_of_mul_le_mul_left hle hEpos
  have hbij : Function.Bijective r :=
    hinj.bijective_of_nat_card_le (by rw [hcardK, hcardL]; exact hKL)
  refine ⟨r, β, hbij, hperm, fun a b => ?_⟩
  have hβ : ∀ x, ((β x : g.rootSet L) : L) = ι (x : K) := fun x => rfl
  rw [hβ, hβ, ← map_neg]
  exact ι.injective.eq_iff

/-- Over a field `E` linearly disjoint from the splitting field of `f`, `Gal(f/E)` is still the
full symmetric group on the roots when `Gal(f/ℚ)` is. -/
theorem galoisGroupIsSymmetric_map_of_isField_tensorProduct {f : ℚ[X]}
    (hS : GaloisGroupIsSymmetric f) (h : IsField (f.SplittingField ⊗[ℚ] E)) :
    GaloisGroupIsSymmetric (f.map (algebraMap ℚ E)) := by
  obtain ⟨r, β, hr, hperm, -⟩ := exists_restrict_bijective h
  rw [galoisGroupIsSymmetric_iff] at hS ⊢
  have heq : ⇑(galPerm (f.map (algebraMap ℚ E))) = β.permCongr ∘ ⇑(galPerm f) ∘ ⇑r :=
    funext hperm
  rw [heq]
  exact β.permCongr.bijective.comp (hS.comp hr)

/-- Over a field `E` linearly disjoint from the splitting field of `f`, `Gal(f/E)` is still the
group of permutations of the roots commuting with negation when `Gal(f/ℚ)` is. -/
theorem galoisGroupIsWreath_map_of_isField_tensorProduct {f : ℚ[X]}
    (hW : GaloisGroupIsWreath f) (h : IsField (f.SplittingField ⊗[ℚ] E)) :
    GaloisGroupIsWreath (f.map (algebraMap ℚ E)) := by
  obtain ⟨r, β, hr, hperm, hneg⟩ := exists_restrict_bijective h
  rw [galoisGroupIsWreath_iff] at hW ⊢
  ext π
  rw [MonoidHom.mem_range, mem_negCommPerm_iff]
  have key : (∃ σ, galPerm (f.map (algebraMap ℚ E)) σ = π) ↔
      β.symm.permCongr π ∈ (galPerm f).range := by
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨r σ, ?_⟩
      rw [hperm σ]
      ext1 x
      simp [Equiv.permCongr_apply]
    · rintro ⟨τ, hτ⟩
      obtain ⟨σ, rfl⟩ := hr.2 τ
      refine ⟨σ, ?_⟩
      rw [hperm σ, hτ]
      ext1 x
      simp [Equiv.permCongr_apply]
  rw [key, hW, mem_negCommPerm_iff]
  constructor
  · intro H x y
    obtain ⟨a, rfl⟩ := β.surjective x
    obtain ⟨b, rfl⟩ := β.surjective y
    rw [hneg a b, H a b, ← hneg]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  · intro H a b
    rw [← hneg a b, H (β a) (β b), ← hneg]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- An irreducible `f ∈ ℚ[X]` stays irreducible over a field `E` linearly disjoint from its
splitting field. -/
theorem irreducible_map_of_isField_tensorProduct {f : ℚ[X]} (hf : Irreducible f)
    (h : IsField (f.SplittingField ⊗[ℚ] E)) : Irreducible (f.map (algebraMap ℚ E)) := by
  obtain ⟨r, β, hr, hperm, -⟩ := exists_restrict_bijective h
  have htrans := isPretransitive_range_galPerm hf
  refine irreducible_of_isPretransitive hf.separable.map
    (by rw [natDegree_map]; exact hf.natDegree_pos) ⟨fun x y => ?_⟩
  obtain ⟨⟨π, hπ⟩, hτ⟩ := MulAction.exists_smul_eq (galPerm f).range (β.symm x) (β.symm y)
  obtain ⟨τ, rfl⟩ := MonoidHom.mem_range.mp hπ
  obtain ⟨σ, rfl⟩ := hr.2 τ
  refine ⟨⟨galPerm _ σ, σ, rfl⟩, ?_⟩
  change galPerm _ σ x = y
  have h2 : galPerm f (r σ) (β.symm x) = β.symm y := hτ
  rw [hperm σ, Equiv.permCongr_apply, h2, Equiv.apply_symm_apply]

/-- **The fixed-field step, packaged.** For a number field `E` there is a bound `R` such that
for every `f ∈ ℚ[X]` whose Galois group is normally generated by the inertia groups at primes
`p > R`, the splitting field of `f` is linearly disjoint from `E` (`K ⊗[ℚ] E` is a field), and
irreducibility of `f`, `Gal(f) = S_n` and `Gal(f) = W_m` all persist over `E`. -/
theorem exists_bound_fixedField (E : Type*) [Field E] [NumberField E] :
    ∃ R : ℕ, ∀ f : ℚ[X],
      (∀ N : Subgroup f.Gal, N.Normal →
        (∀ p : ℕ, p.Prime → R < p → ∀ (P : Ideal (𝓞 f.SplittingField)) [P.IsPrime],
          P.LiesOver (Ideal.span {(p : ℤ)}) → P.inertia Gal(f.SplittingField/ℚ) ≤ N) →
        N = ⊤) →
      IsField (f.SplittingField ⊗[ℚ] E) ∧
      (Irreducible f → Irreducible (f.map (algebraMap ℚ E))) ∧
      (GaloisGroupIsSymmetric f → GaloisGroupIsSymmetric (f.map (algebraMap ℚ E))) ∧
      (GaloisGroupIsWreath f → GaloisGroupIsWreath (f.map (algebraMap ℚ E))) := by
  obtain ⟨R, hR⟩ := exists_bound_isField_splittingField_tensorProduct E
  refine ⟨R, fun f hgen => ?_⟩
  have h := hR f hgen
  exact ⟨h, fun hf => irreducible_map_of_isField_tensorProduct hf h,
    fun hS => galoisGroupIsSymmetric_map_of_isField_tensorProduct hS h,
    fun hW => galoisGroupIsWreath_map_of_isField_tensorProduct hW h⟩

end Transfer

end FixedFieldDisjointness

end ArithmeticOfJacobiPolynomials
