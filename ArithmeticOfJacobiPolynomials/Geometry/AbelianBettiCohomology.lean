/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.ComplexRealizationFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dual.Lemmas
import all ArithmeticOfJacobiPolynomials.Algebra.ComplexRealization
import all ArithmeticOfJacobiPolynomials.Algebra.ComplexRealizationFunctor

/-!
# Rational singular cohomology and the universal coefficient bridge

This file proves rational vector-space duality for every short complex, using Mathlib's
cycles, homology and quotient comparisons. The equivalence
`dualHomologyEquiv` identifies homology of the dual short complex with the rational
linear dual of its homology; `dualHomologyEquiv_apply` proves that it is the evaluation
pairing on cycles.

The generic linear-algebra proof uses extension of functionals from a subspace and
`range g* = (ker g)ᵒ`. The dual cochain complex and the natural universal coefficient
equivalence are constructed in every degree. Singular cohomology is the cohomology of the dual of
Mathlib's singular chain complex, with contravariant continuous-map and
scheme-morphism functors and the evaluation pairing. Hodge classes and the first Chern class
are treated in `AbelianHodgeClasses` and `AbelianBettiChernClass`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ArithmeticOfJacobiPolynomials.AbelianBettiCohomology

section LinearAlgebra

variable {A B C : Type} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
  [AddCommGroup C] [Module ℚ C] (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] C)

/-- The map induced by the dual complex on `ker f^* / range g^*`. -/
theorem dualZero (h : ∀ a, g (f a) = 0) (φ : Module.Dual ℚ C) : f.dualMap (g.dualMap φ) = 0 := by
  ext a
  simp [h a]

/-- The evaluation pairing of a functional killing `range f` with cycles, as a functional on the
homology `ker g / range f`. -/
def pairLift (h : ∀ a, g (f a) = 0) (φ : LinearMap.ker f.dualMap) :
    Module.Dual ℚ (LinearMap.ker g ⧸ LinearMap.range (f.codRestrict (LinearMap.ker g) h)) :=
  (LinearMap.range (f.codRestrict (LinearMap.ker g) h)).liftQ
    (φ.1.comp (LinearMap.ker g).subtype) (by
      rintro _ ⟨a, rfl⟩
      exact LinearMap.congr_fun (LinearMap.mem_ker.1 φ.2) a)

@[simp] theorem pairLift_mk (h : ∀ a, g (f a) = 0) (φ : LinearMap.ker f.dualMap)
    (z : LinearMap.ker g) :
    pairLift f g h φ (Submodule.Quotient.mk z) = φ.1 z := rfl

/-- The pairing `ker f^* → (ker g / range f)^*`. -/
def pairing (h : ∀ a, g (f a) = 0) : LinearMap.ker f.dualMap →ₗ[ℚ]
    Module.Dual ℚ (LinearMap.ker g ⧸ LinearMap.range (f.codRestrict (LinearMap.ker g) h)) where
  toFun := pairLift f g h
  map_add' φ ψ := by
    refine Submodule.linearMap_qext _ ?_
    ext z
    simp
  map_smul' c φ := by
    refine Submodule.linearMap_qext _ ?_
    ext z
    simp

@[simp] theorem pairing_mk (h : ∀ a, g (f a) = 0) (φ : LinearMap.ker f.dualMap)
    (z : LinearMap.ker g) :
    pairing f g h φ (Submodule.Quotient.mk z) = φ.1 z := rfl

theorem pairing_surjective (h : ∀ a, g (f a) = 0) : Function.Surjective (pairing f g h) := by
  intro l
  obtain ⟨φ, hφ⟩ := Subspace.dualRestrict_surjective (W := LinearMap.ker g)
    (l.comp (LinearMap.range (f.codRestrict (LinearMap.ker g) h)).mkQ)
  have hφ' : ∀ z : LinearMap.ker g,
      φ z = l (Submodule.Quotient.mk z) := fun z => by
    have := LinearMap.congr_fun hφ z
    simpa using this
  refine ⟨⟨φ, ?_⟩, ?_⟩
  · refine LinearMap.mem_ker.2 ?_
    ext a
    have hmem : f a ∈ LinearMap.ker g := LinearMap.mem_ker.2 (h a)
    have h1 : φ (f a) = l (Submodule.Quotient.mk ⟨f a, hmem⟩) := hφ' ⟨f a, hmem⟩
    have h2 : (Submodule.Quotient.mk (⟨f a, hmem⟩ : LinearMap.ker g) :
        LinearMap.ker g ⧸ LinearMap.range (f.codRestrict (LinearMap.ker g) h)) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨a, rfl⟩
    simp [h1, h2]
  · refine Submodule.linearMap_qext _ ?_
    ext z
    simpa using hφ' z

/-- The kernel of the pairing is the image of `g^*`. -/
theorem pairing_ker (h : ∀ a, g (f a) = 0) (φ : LinearMap.ker f.dualMap) :
    pairing f g h φ = 0 ↔ ∃ ψ : Module.Dual ℚ C, g.dualMap ψ = φ.1 := by
  constructor
  · intro hφ
    have : φ.1 ∈ (LinearMap.ker g).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      have := LinearMap.congr_fun hφ (Submodule.Quotient.mk ⟨w, hw⟩)
      simpa using this
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at this
    obtain ⟨ψ, hψ⟩ := this
    exact ⟨ψ, hψ⟩
  · rintro ⟨ψ, hψ⟩
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
      have hz : g z.1 = 0 := LinearMap.mem_ker.1 z.2
      have := LinearMap.congr_fun hψ z.1
      simp only [pairing_mk, LinearMap.zero_apply]
      rw [← this]
      simp [hz]

/-- The concrete duality equivalence: the homology of the dual sequence
`C^∨ → B^∨ → A^∨` is the dual of the homology `ker g / range f` of `A → B → C`. -/
def dualEquiv (h : ∀ a, g (f a) = 0) :
    (LinearMap.ker f.dualMap ⧸ LinearMap.range
        (g.dualMap.codRestrict (LinearMap.ker f.dualMap) (dualZero f g h))) ≃ₗ[ℚ]
      Module.Dual ℚ (LinearMap.ker g ⧸ LinearMap.range (f.codRestrict (LinearMap.ker g) h)) :=
  LinearEquiv.ofBijective
    ((LinearMap.range (g.dualMap.codRestrict (LinearMap.ker f.dualMap) (dualZero f g h))).liftQ
      (pairing f g h) (by
        rintro _ ⟨ψ, rfl⟩
        rw [LinearMap.mem_ker, pairing_ker]
        exact ⟨ψ, rfl⟩))
    ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot]
      intro φ hφ
      obtain ⟨ψ, hψ⟩ := (pairing_ker f g h φ).1 (LinearMap.mem_ker.1 hφ)
      exact ⟨ψ, Subtype.ext hψ⟩,
    by
      intro l
      obtain ⟨φ, hφ⟩ := pairing_surjective f g h l
      exact ⟨Submodule.Quotient.mk φ, hφ⟩⟩

@[simp] theorem dualEquiv_mk (h : ∀ a, g (f a) = 0) (φ : LinearMap.ker f.dualMap)
    (z : LinearMap.ker g) :
    dualEquiv f g h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk z) = φ.1 z := rfl

end LinearAlgebra

section ModuleCatGlue

/-- The linear dual of an object of `ModuleCat ℚ`. -/
abbrev dualObj (M : ModuleCat ℚ) : ModuleCat ℚ := ModuleCat.of ℚ (Module.Dual ℚ M)

/-- The transpose of a morphism of `ℚ`-vector spaces. -/
def dualMap {M N : ModuleCat ℚ} (f : M ⟶ N) : dualObj N ⟶ dualObj M :=
  ModuleCat.ofHom f.hom.dualMap

@[simp] theorem dualMap_apply {M N : ModuleCat ℚ} (f : M ⟶ N) (φ : Module.Dual ℚ N) (x : M) :
    (dualMap f).hom φ x = φ (f.hom x) := rfl

theorem dualMap_comp {M N P : ModuleCat ℚ} (f : M ⟶ N) (g : N ⟶ P) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)

@[simp] theorem dualMap_id (M : ModuleCat ℚ) : dualMap (𝟙 M) = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)

@[simp] theorem dualMap_zero {M N : ModuleCat ℚ} : dualMap (0 : M ⟶ N) = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun φ => LinearMap.ext fun x => by
    change φ ((0 : M ⟶ N).hom x) = 0
    simp)

/-- The dual of a short complex `X₁ → X₂ → X₃`: the short complex `X₃^∨ → X₂^∨ → X₁^∨`. -/
def dualSC (S : ShortComplex (ModuleCat ℚ)) : ShortComplex (ModuleCat ℚ) :=
  ShortComplex.mk (dualMap S.g) (dualMap S.f)
    (ModuleCat.hom_ext (LinearMap.ext fun φ => LinearMap.ext fun a => by
      change φ (S.g.hom (S.f.hom a)) = 0
      simp))

/-- The map of dual short complexes induced by a morphism of short complexes. -/
def dualSCMap {S T : ShortComplex (ModuleCat ℚ)} (ψ : S ⟶ T) : dualSC T ⟶ dualSC S where
  τ₁ := dualMap ψ.τ₃
  τ₂ := dualMap ψ.τ₂
  τ₃ := dualMap ψ.τ₁
  comm₁₂ := ModuleCat.hom_ext (LinearMap.ext fun (φ : Module.Dual ℚ T.X₃) =>
    LinearMap.ext fun (a : S.X₂) => by
    have h : T.g.hom (ψ.τ₂.hom a) = ψ.τ₃.hom (S.g.hom a) := by
      simpa using LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 ψ.comm₂₃) a
    change φ (ψ.τ₃.hom (S.g.hom a)) = φ (T.g.hom (ψ.τ₂.hom a))
    rw [h])
  comm₂₃ := ModuleCat.hom_ext (LinearMap.ext fun (φ : Module.Dual ℚ T.X₂) =>
    LinearMap.ext fun (a : S.X₁) => by
    have h : T.f.hom (ψ.τ₁.hom a) = ψ.τ₂.hom (S.f.hom a) := by
      simpa using LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 ψ.comm₁₂) a
    change φ (ψ.τ₂.hom (S.f.hom a)) = φ (T.f.hom (ψ.τ₁.hom a))
    rw [h])

/-- **Exactness of vector-space duality**: the homology of the dual short complex is the dual of
the homology. -/
def dualHomologyEquiv (S : ShortComplex (ModuleCat ℚ)) :
    (dualSC S).homology ≃ₗ[ℚ] Module.Dual ℚ S.homology :=
  ((dualSC S).moduleCatHomologyIso.toLinearEquiv).trans
    ((dualEquiv S.f.hom S.g.hom S.moduleCat_zero_apply).trans
      (S.moduleCatHomologyIso.toLinearEquiv.dualMap))

/-- Evaluation of a functional on the middle term of `S` (the middle term of `dualSC S`). -/
def dualEval (S : ShortComplex (ModuleCat ℚ)) (φ : Module.Dual ℚ S.X₂) (x : S.X₂) : ℚ := φ x

theorem dualHomologyEquiv_apply (S : ShortComplex (ModuleCat ℚ))
    (zd : (dualSC S).cycles) (zs : S.cycles) :
    dualHomologyEquiv S ((dualSC S).homologyπ.hom zd) (S.homologyπ.hom zs) =
      dualEval S ((dualSC S).iCycles.hom zd) (S.iCycles.hom zs) := by
  have h1 := ShortComplex.π_moduleCatCyclesIso_hom_apply (dualSC S) zd
  have h2 := ShortComplex.π_moduleCatCyclesIso_hom_apply S zs
  have h3 := ShortComplex.moduleCatCyclesIso_hom_i_apply (dualSC S) zd
  have h4 := ShortComplex.moduleCatCyclesIso_hom_i_apply S zs
  change dualEquiv S.f.hom S.g.hom S.moduleCat_zero_apply
    ((dualSC S).moduleCatHomologyIso.hom ((dualSC S).homologyπ.hom zd))
    (S.moduleCatHomologyIso.hom (S.homologyπ.hom zs)) = _
  rw [h1, h2, ← h3, ← h4]
  rfl

/-- **Naturality of the duality**: the pairing of the homology of the dual complex with the
homology is natural in morphisms of short complexes. -/
theorem dualHomologyEquiv_naturality {S T : ShortComplex (ModuleCat ℚ)} (ψ : S ⟶ T)
    (ξ : (dualSC T).homology) (c : S.homology) :
    dualHomologyEquiv S ((ShortComplex.homologyMap (dualSCMap ψ)).hom ξ) c =
      dualHomologyEquiv T ξ ((ShortComplex.homologyMap ψ).hom c) := by
  obtain ⟨zd, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (dualSC T).homologyπ) ξ
  obtain ⟨zs, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi S.homologyπ) c
  have e1 : (ShortComplex.homologyMap (dualSCMap ψ)).hom ((dualSC T).homologyπ.hom zd) =
      (dualSC S).homologyπ.hom ((ShortComplex.cyclesMap (dualSCMap ψ)).hom zd) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      (ShortComplex.homologyπ_naturality (dualSCMap ψ))) zd
  have e2 : (ShortComplex.homologyMap ψ).hom (S.homologyπ.hom zs) =
      T.homologyπ.hom ((ShortComplex.cyclesMap ψ).hom zs) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (ShortComplex.homologyπ_naturality ψ)) zs
  have a1 : (dualSC S).iCycles.hom ((ShortComplex.cyclesMap (dualSCMap ψ)).hom zd) =
      (dualMap ψ.τ₂).hom ((dualSC T).iCycles.hom zd) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (ShortComplex.cyclesMap_i (dualSCMap ψ))) zd
  have a2 : T.iCycles.hom ((ShortComplex.cyclesMap ψ).hom zs) = ψ.τ₂.hom (S.iCycles.hom zs) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (ShortComplex.cyclesMap_i ψ)) zs
  rw [e1, dualHomologyEquiv_apply, a1, e2, dualHomologyEquiv_apply, a2]
  rfl

end ModuleCatGlue

section DualComplex

/-- The dual cochain complex `Cⁿ = Hom_ℚ(Kₙ, ℚ)` of a chain complex `K` of `ℚ`-vector spaces. -/
def dualComplex (K : ChainComplex (ModuleCat ℚ) ℕ) : CochainComplex (ModuleCat ℚ) ℕ :=
  CochainComplex.of (fun n => dualObj (K.X n)) (fun n => dualMap (K.d (n + 1) n)) (fun n => by
    rw [← dualMap_comp, K.d_comp_d, dualMap_zero])

variable (K : ChainComplex (ModuleCat ℚ) ℕ)

theorem dualComplex_d (i j : ℕ) : (dualComplex K).d i j = dualMap (K.d j i) := by
  by_cases h : i + 1 = j
  · subst h
    simp [dualComplex]
  · rw [HomologicalComplex.shape _ _ _ (by simpa using h),
      K.shape j i (by simpa using h), dualMap_zero]
    rfl

/-- A chain map induces a map of dual cochain complexes, in the opposite direction. -/
def dualComplexMap {K L : ChainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) :
    dualComplex L ⟶ dualComplex K where
  f n := dualMap (φ.f n)
  comm' i j _ := by
    rw [dualComplex_d, dualComplex_d]
    change dualMap (φ.f i) ≫ dualMap (K.d j i) = dualMap (L.d j i) ≫ dualMap (φ.f j)
    rw [← dualMap_comp, ← dualMap_comp, φ.comm]

@[simp] theorem dualComplexMap_f {K L : ChainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n : ℕ) :
    (dualComplexMap φ).f n = dualMap (φ.f n) := rfl

theorem dualComplexMap_id : dualComplexMap (𝟙 K) = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n => by simp; rfl

theorem dualComplexMap_comp {K L M : ChainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (ψ : L ⟶ M) :
    dualComplexMap (φ ≫ ψ) = dualComplexMap ψ ≫ dualComplexMap φ :=
  HomologicalComplex.hom_ext _ _ fun n => by simp [dualMap_comp]; rfl

/-- The dual cochain complex as a contravariant functor. -/
def dualComplexFunctor : (ChainComplex (ModuleCat ℚ) ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat ℚ) ℕ where
  obj K := dualComplex K.unop
  map φ := dualComplexMap φ.unop
  map_id K := dualComplexMap_id K.unop
  map_comp φ ψ := dualComplexMap_comp ψ.unop φ.unop

end DualComplex

section UniversalCoefficients

theorem down_next (n : ℕ) : (ComplexShape.down ℕ).next n = Nat.pred n := by
  cases n
  · exact ChainComplex.next_nat_zero
  · exact ChainComplex.next_nat_succ _

theorem up_prev (n : ℕ) : (ComplexShape.up ℕ).prev n = Nat.pred n := by
  cases n
  · exact CochainComplex.prev_nat_zero
  · exact CochainComplex.prev_nat_succ _

variable (K : ChainComplex (ModuleCat ℚ) ℕ)

/-- The dual of the short complex `K.sc' k j i` is the short complex `(dualComplex K).sc' i j k`. -/
def dualSc'Iso (i j k : ℕ) : (dualComplex K).sc' i j k ≅ dualSC (K.sc' k j i) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [HomologicalComplex.shortComplexFunctor'_obj_X₁, Iso.refl_hom,
        HomologicalComplex.shortComplexFunctor'_obj_X₂,
        HomologicalComplex.shortComplexFunctor'_obj_f, dualSC, dualComplex_d]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by
      simp only [HomologicalComplex.shortComplexFunctor'_obj_X₂, Iso.refl_hom,
        HomologicalComplex.shortComplexFunctor'_obj_X₃,
        HomologicalComplex.shortComplexFunctor'_obj_g, dualSC, dualComplex_d]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- **Rational universal coefficient theorem** for a chain complex of `ℚ`-vector spaces: the
cohomology of the dual cochain complex is the linear dual of the homology. -/
def ucEquiv (n : ℕ) : (dualComplex K).homology n ≃ₗ[ℚ] Module.Dual ℚ (K.homology n) :=
  (((dualComplex K).homologyIsoSc' (Nat.pred n) n (n + 1) (up_prev n) (CochainComplex.next ℕ
      n)).trans
      (ShortComplex.homologyMapIso (dualSc'Iso K (Nat.pred n) n (n + 1)))).toLinearEquiv.trans
    ((dualHomologyEquiv (K.sc' (n + 1) n (Nat.pred n))).trans
      (K.homologyIsoSc' (n + 1) n (Nat.pred n) (ChainComplex.prev ℕ n) (down_next
          n)).toLinearEquiv.dualMap)

/-- Evaluation of a functional on the `n`-th term of `K`. -/
def cochainEval (n : ℕ) (φ : Module.Dual ℚ (K.X n)) (x : K.X n) : ℚ := φ x

/-- **The universal coefficient pairing on classes**: the class of a cocycle `zd` of the dual
complex evaluated on the class of a cycle `zs` of `K` is the value of the cochain on the chain. -/
theorem ucEquiv_apply (n : ℕ) (zd : (dualComplex K).cycles n) (zs : K.cycles n) :
    ucEquiv K n (((dualComplex K).homologyπ n).hom zd) ((K.homologyπ n).hom zs) =
      cochainEval K n (((dualComplex K).iCycles n).hom zd) ((K.iCycles n).hom zs) := by
  have h1 : ((dualComplex K).homologyIsoSc' (Nat.pred n) n (n + 1) (up_prev n)
      (CochainComplex.next ℕ n)).hom.hom
        (((dualComplex K).homologyπ n).hom zd) =
      ((dualComplex K).sc' (Nat.pred n) n (n + 1)).homologyπ.hom
        (((dualComplex K).cyclesIsoSc' (Nat.pred n) n (n + 1) (up_prev n) (CochainComplex.next
            ℕ n)).hom.hom zd) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      ((dualComplex K).π_homologyIsoSc'_hom (Nat.pred n) n (n + 1) (up_prev n)
          (CochainComplex.next ℕ n))) zd
  have h2 : (K.homologyIsoSc' (n + 1) n (Nat.pred n) (ChainComplex.prev ℕ n) (down_next n)).hom.hom
        ((K.homologyπ n).hom zs) =
      (K.sc' (n + 1) n (Nat.pred n)).homologyπ.hom
        ((K.cyclesIsoSc' (n + 1) n (Nat.pred n) (ChainComplex.prev ℕ n) (down_next n)).hom.hom
            zs) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      (K.π_homologyIsoSc'_hom (n + 1) n (Nat.pred n) (ChainComplex.prev ℕ n) (down_next n))) zs
  set w := ((dualComplex K).cyclesIsoSc' (Nat.pred n) n (n + 1) (up_prev n)
      (CochainComplex.next ℕ n)).hom.hom zd
    with hw
  have h3 : (ShortComplex.homologyMap (dualSc'Iso K (Nat.pred n) n (n + 1)).hom).hom
        (((dualComplex K).sc' (Nat.pred n) n (n + 1)).homologyπ.hom w) =
      (dualSC (K.sc' (n + 1) n (Nat.pred n))).homologyπ.hom
        ((ShortComplex.cyclesMap (dualSc'Iso K (Nat.pred n) n (n + 1)).hom).hom w) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      (ShortComplex.homologyπ_naturality (dualSc'Iso K (Nat.pred n) n (n + 1)).hom)) w
  have h4 : (dualSC (K.sc' (n + 1) n (Nat.pred n))).iCycles.hom
        ((ShortComplex.cyclesMap (dualSc'Iso K (Nat.pred n) n (n + 1)).hom).hom w) =
      ((dualComplex K).sc' (Nat.pred n) n (n + 1)).iCycles.hom w :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      (ShortComplex.cyclesMap_i (dualSc'Iso K (Nat.pred n) n (n + 1)).hom)) w
  have h5 : ((dualComplex K).sc' (Nat.pred n) n (n + 1)).iCycles.hom w =
      ((dualComplex K).iCycles n).hom zd :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      ((dualComplex K).cyclesIsoSc'_hom_iCycles (Nat.pred n) n (n + 1) (up_prev n)
          (CochainComplex.next ℕ n))) zd
  have h6 : (K.sc' (n + 1) n (Nat.pred n)).iCycles.hom
        ((K.cyclesIsoSc' (n + 1) n (Nat.pred n) (ChainComplex.prev ℕ n) (down_next n)).hom.hom zs) =
      (K.iCycles n).hom zs :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      (K.cyclesIsoSc'_hom_iCycles (n + 1) n (Nat.pred n) (ChainComplex.prev ℕ n) (down_next n))) zs
  change dualHomologyEquiv (K.sc' (n + 1) n (Nat.pred n))
      ((ShortComplex.homologyMap (dualSc'Iso K (Nat.pred n) n (n + 1)).hom).hom
        (((dualComplex K).homologyIsoSc' (Nat.pred n) n (n + 1) (up_prev n)
            (CochainComplex.next ℕ n)).hom.hom
          (((dualComplex K).homologyπ n).hom zd)))
      ((K.homologyIsoSc' (n + 1) n (Nat.pred n) (ChainComplex.prev ℕ n) (down_next n)).hom.hom
        ((K.homologyπ n).hom zs)) = _
  rw [h1, h2, h3, dualHomologyEquiv_apply, h4, h5, h6]
  rfl

/-- **Naturality of the universal coefficient pairing** in chain maps `φ : K ⟶ L`. -/
theorem ucEquiv_natural {K L : ChainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n : ℕ)
    (ξ : (dualComplex L).homology n) (c : K.homology n) :
    ucEquiv K n ((HomologicalComplex.homologyMap (dualComplexMap φ) n).hom ξ) c =
      ucEquiv L n ξ ((HomologicalComplex.homologyMap φ n).hom c) := by
  obtain ⟨zd, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((dualComplex L).homologyπ n)) ξ
  obtain ⟨zs, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (K.homologyπ n)) c
  have e1 : (HomologicalComplex.homologyMap (dualComplexMap φ) n).hom
        (((dualComplex L).homologyπ n).hom zd) =
      ((dualComplex K).homologyπ n).hom
        ((HomologicalComplex.cyclesMap (dualComplexMap φ) n).hom zd) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      (HomologicalComplex.homologyπ_naturality (dualComplexMap φ) n)) zd
  have e2 : (HomologicalComplex.homologyMap φ n).hom ((K.homologyπ n).hom zs) =
      (L.homologyπ n).hom ((HomologicalComplex.cyclesMap φ n).hom zs) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (HomologicalComplex.homologyπ_naturality φ n)) zs
  have a1 : ((dualComplex K).iCycles n).hom
        ((HomologicalComplex.cyclesMap (dualComplexMap φ) n).hom zd) =
      (dualMap (φ.f n)).hom (((dualComplex L).iCycles n).hom zd) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      (HomologicalComplex.cyclesMap_i (dualComplexMap φ) n)) zd
  have a2 : (L.iCycles n).hom ((HomologicalComplex.cyclesMap φ n).hom zs) =
      (φ.f n).hom ((K.iCycles n).hom zs) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (HomologicalComplex.cyclesMap_i φ n)) zs
  rw [e1, ucEquiv_apply, a1, e2, ucEquiv_apply, a2]
  rfl

end UniversalCoefficients

section Singular

open AlgebraicTopology

/-- The singular chain complex with `ℚ` coefficients, as a functor of the space. -/
abbrev singularChain : TopCat.{0} ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
  (singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- **Singular cohomology** `Hⁿ(-; ℚ)`: the cohomology of the dual of the Mathlib singular chain
complex (which has `ℚ`-valued singular cochains `Hom(Cₙ(T; ℚ), ℚ)` in degree `n`). -/
def singularCohomologyFunctor (n : ℕ) : TopCat.{0}ᵒᵖ ⥤ ModuleCat ℚ :=
  singularChain.op ⋙ dualComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- `Hⁿ(T; ℚ)`. -/
abbrev singularCohomology (T : TopCat.{0}) (n : ℕ) : ModuleCat ℚ :=
  (singularCohomologyFunctor n).obj (Opposite.op T)

/-- Mathlib's singular homology `Hₙ(T; ℚ)`. -/
abbrev singularHomology (T : TopCat.{0}) (n : ℕ) : ModuleCat ℚ :=
  ((singularHomologyFunctor (ModuleCat ℚ) n).obj (ModuleCat.of ℚ ℚ)).obj T

/-- The pullback `Hⁿ(T'; ℚ) → Hⁿ(T; ℚ)` along a continuous map `f : T ⟶ T'`. -/
abbrev singularCohomologyMap {T T' : TopCat.{0}} (f : T ⟶ T') (n : ℕ) :
    singularCohomology T' n ⟶ singularCohomology T n :=
  (singularCohomologyFunctor n).map f.op

/-- The pushforward `Hₙ(T; ℚ) → Hₙ(T'; ℚ)` along a continuous map. -/
abbrev singularHomologyMap {T T' : TopCat.{0}} (f : T ⟶ T') (n : ℕ) :
    singularHomology T n ⟶ singularHomology T' n :=
  ((singularHomologyFunctor (ModuleCat ℚ) n).obj (ModuleCat.of ℚ ℚ)).map f

/-- **The rational universal coefficient theorem for singular cohomology**: `Hⁿ(T; ℚ)` is the
linear dual of the singular homology `Hₙ(T; ℚ)`. -/
def singularUC (T : TopCat.{0}) (n : ℕ) :
    singularCohomology T n ≃ₗ[ℚ] Module.Dual ℚ (singularHomology T n) :=
  ucEquiv (singularChain.obj T) n

/-- Naturality of the universal coefficient equivalence in continuous maps. -/
theorem singularUC_natural {T T' : TopCat.{0}} (f : T ⟶ T') (n : ℕ)
    (ξ : singularCohomology T' n) (c : singularHomology T n) :
    singularUC T n ((singularCohomologyMap f n).hom ξ) c =
      singularUC T' n ξ ((singularHomologyMap f n).hom c) :=
  ucEquiv_natural (singularChain.map f) n ξ c

end Singular

section ComplexPoints

open AlgebraicGeometry ArithmeticOfJacobiPolynomials.ComplexRealization

/-- **Betti cohomology** `Hⁿ(X(ℂ), ℚ)` of a scheme over `ℂ`: the singular cohomology of the
analytic space of complex points `ArithmeticOfJacobiPolynomials.ComplexRealization.space X`. -/
abbrev bettiCohomology (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ) : ModuleCat ℚ :=
  singularCohomology (space X) n

/-- The pullback `Hⁿ(Y(ℂ), ℚ) → Hⁿ(X(ℂ), ℚ)` along a morphism `f : X ⟶ Y` of schemes over `ℂ`. -/
abbrev bettiCohomologyMap {X Y : Over (Spec (CommRingCat.of ℂ))} (f : X ⟶ Y) (n : ℕ) :
    bettiCohomology Y n ⟶ bettiCohomology X n :=
  singularCohomologyMap (spaceMap f) n

theorem homology_eq (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ) :
    ComplexRealization.homology X n = singularHomology (space X) n := by
  unfold ComplexRealization.homology
  rfl

/-- The identification `Hₙ(X(ℂ), ℚ) = Hₙ(space X; ℚ)` as an isomorphism. -/
def homologyIso (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ) :
    ComplexRealization.homology X n ≅ singularHomology (space X) n :=
  eqToIso (homology_eq X n)

/-- **The universal coefficient identification** of the Betti cohomology with the dual of
the Betti homology `ComplexRealization.homology X n`. -/
def bettiUC (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ) :
    bettiCohomology X n ≃ₗ[ℚ] Module.Dual ℚ (ComplexRealization.homology X n) :=
  (singularUC (space X) n).trans (homologyIso X n).toLinearEquiv.dualMap

/-- Naturality of `bettiUC` in morphisms of schemes over `ℂ`. -/
theorem bettiUC_natural {X Y : Over (Spec (CommRingCat.of ℂ))} (f : X ⟶ Y) (n : ℕ)
    (ξ : bettiCohomology Y n) (c : ComplexRealization.homology X n) :
    bettiUC X n ((bettiCohomologyMap f n).hom ξ) c =
      bettiUC Y n ξ ((bettiMap n f).hom c) :=
  singularUC_natural (spaceMap f) n ξ c

end ComplexPoints

section Telescope

open Finset

/-- The edge pattern of a simplex face. -/
def yy (a b : ℕ → ℚ) (j i : ℕ) : ℚ :=
  if i + 2 ≤ j then a i else if j = i + 1 then a i + b i else b i

theorem yy_a {a b : ℕ → ℚ} {j i : ℕ} (h : i + 2 ≤ j) : yy a b j i = a i := by
  simp [yy, h]

theorem yy_ab {a b : ℕ → ℚ} {j i : ℕ} (h : j = i + 1) : yy a b j i = a i + b i := by
  unfold yy
  split_ifs <;> first | rfl | omega

theorem yy_b {a b : ℕ → ℚ} {j i : ℕ} (h : j ≤ i) : yy a b j i = b i := by
  unfold yy
  split_ifs <;> first | rfl | omega

theorem telescope (a b : ℕ → ℚ) (r : ℕ) :
    ∑ j ∈ range (r + 2), (-1 : ℚ) ^ j * ∏ i ∈ range r, yy a b j i = 0 := by
  induction r with
  | zero => simp [sum_range_succ]
  | succ r ih =>
    have hA : ∀ j ∈ range (r + 1), ∏ i ∈ range (r + 1), yy a b j i =
        (∏ i ∈ range r, yy a b j i) * b r := by
      intro j hj
      rw [prod_range_succ]
      have := mem_range.1 hj
      rw [yy_b (by omega)]
    have hB : ∏ i ∈ range (r + 1), yy a b (r + 1) i =
        (∏ i ∈ range r, a i) * (a r + b r) := by
      rw [prod_range_succ]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        have := mem_range.1 hi
        exact yy_a (by omega)
      · exact yy_ab rfl
    have hC : ∏ i ∈ range (r + 1), yy a b (r + 2) i = (∏ i ∈ range r, a i) * a r := by
      rw [prod_range_succ]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        have := mem_range.1 hi
        exact yy_a (by omega)
      · exact yy_a (by omega)
    have hD : ∏ i ∈ range r, yy a b (r + 1) i = ∏ i ∈ range r, a i := by
      refine prod_congr rfl fun i hi => ?_
      have := mem_range.1 hi
      exact yy_a (by omega)
    rw [sum_range_succ, sum_range_succ, hB, hC,
      sum_congr rfl fun j hj => congrArg ((-1 : ℚ) ^ j * ·) (hA j (by simpa using hj))]
    rw [sum_range_succ, hD] at ih
    have : ∑ j ∈ range (r + 1), (-1 : ℚ) ^ j * ((∏ i ∈ range r, yy a b j i) * b r) =
        (∑ j ∈ range (r + 1), (-1 : ℚ) ^ j * ∏ i ∈ range r, yy a b j i) * b r := by
      rw [sum_mul]
      exact sum_congr rfl fun j _ => by ring
    rw [this]
    have e : ∑ j ∈ range (r + 1), (-1 : ℚ) ^ j * ∏ i ∈ range r, yy a b j i =
        -((-1 : ℚ) ^ (r + 1) * ∏ i ∈ range r, a i) := by linarith
    rw [e]
    ring

end Telescope

section CochainFunctions

open SSet Limits
open scoped Simplicial

/-- The coefficient object `ℚ` of the chain complexes. -/
abbrev coeff : ModuleCat ℚ := ModuleCat.of ℚ ℚ

variable (X : SSet.{0})

/-- The value of an `n`-cochain on an `n`-simplex. -/
def cochainVal {n : ℕ} (φ : Module.Dual ℚ ((X.chainComplex coeff).X n)) (x : X _⦋n⦌) : ℚ :=
  φ ((X.ιChainComplex (R := coeff) x).hom 1)

/-- The cochain with prescribed values on the simplices. -/
def cochainOfFun {n : ℕ} (g : X _⦋n⦌ → ℚ) : Module.Dual ℚ ((X.chainComplex coeff).X n) :=
  ((X.isColimitChainComplexXCofan coeff n).desc
    (Cofan.mk coeff fun x => ModuleCat.ofHom (g x • LinearMap.id : ℚ →ₗ[ℚ] ℚ))).hom

theorem cochainVal_ofFun {n : ℕ} (g : X _⦋n⦌ → ℚ) (x : X _⦋n⦌) :
    cochainVal X (cochainOfFun X g) x = g x := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan coeff n)
    (fun x => ModuleCat.ofHom (g x • LinearMap.id : ℚ →ₗ[ℚ] ℚ)) x
  have h1 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 h) 1
  change ((X.isColimitChainComplexXCofan coeff n).desc
      (Cofan.mk coeff fun x => ModuleCat.ofHom (g x • LinearMap.id : ℚ →ₗ[ℚ] ℚ))).hom
      ((X.ιChainComplex (R := coeff) x).hom 1) =
    (ModuleCat.ofHom (g x • LinearMap.id : ℚ →ₗ[ℚ] ℚ)).hom 1 at h1
  exact h1.trans (by simp)

theorem cochain_ext {n : ℕ} {φ ψ : Module.Dual ℚ ((X.chainComplex coeff).X n)}
    (h : ∀ x, cochainVal X φ x = cochainVal X ψ x) : φ = ψ := by
  have : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    refine SSet.chainComplex_hom_ext (X := X) (R := coeff) (fun x => ?_)
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    have e : (X.ιChainComplex (R := coeff) x).hom t =
        t • (X.ιChainComplex (R := coeff) x).hom 1 := by
      rw [← map_smul]
      simp
    change φ ((X.ιChainComplex (R := coeff) x).hom t) = ψ ((X.ιChainComplex (R := coeff) x).hom t)
    rw [e, map_smul, map_smul]
    exact congrArg _ (h x)
  exact ModuleCat.hom_ext_iff.1 this

theorem cochainVal_dualMap_d {n : ℕ}
    (φ : Module.Dual ℚ ((X.chainComplex coeff).X n)) (τ : X _⦋n + 1⦌) :
    cochainVal X ((dualMap ((X.chainComplex coeff).d (n + 1) n)).hom φ) τ =
      ∑ i : Fin (n + 2), (-1 : ℚ) ^ i.val * cochainVal X φ (X.δ i τ) := by
  simp only [cochainVal]
  have h2 : ((X.chainComplex coeff).d (n + 1) n).hom
        ((X.ιChainComplex (R := coeff) τ).hom 1) =
      (X.ιChainComplex (R := coeff) τ ≫ (X.chainComplex coeff).d (n + 1) n).hom 1 := rfl
  change φ (((X.chainComplex coeff).d (n + 1) n).hom ((X.ιChainComplex (R := coeff) τ).hom 1)) = _
  rw [h2, X.ιChainComplex_d]
  simp

end CochainFunctions

section Edges

open SSet SimplexCategory
open scoped Simplicial

variable (X : SSet.{0})

/-- The edge from vertex `a` to vertex `b ≥ a` of a simplex. -/
def edge {m : ℕ} (σ : X _⦋m⦌) (a b : Fin (m + 1)) (h : a ≤ b) : X _⦋1⦌ :=
  X.map (mkOfLe a b h).op σ

/-- The edge of a face of a simplex is an edge of the simplex. -/
theorem edge_δ {m : ℕ} (τ : X _⦋m + 1⦌) (j : Fin (m + 2)) (a b : Fin (m + 1)) (h : a ≤ b) :
    edge X (X.δ j τ) a b h =
      edge X τ (j.succAbove a) (j.succAbove b) ((Fin.strictMono_succAbove j).monotone h) := by
  have e : mkOfLe a b h ≫ SimplexCategory.δ j =
      mkOfLe (j.succAbove a) (j.succAbove b) ((Fin.strictMono_succAbove j).monotone h) :=
    Hom.ext_one_left _ _
  unfold edge
  rw [SimplicialObject.δ_def]
  change X.map (mkOfLe a b h).op (X.map (SimplexCategory.δ j).op τ) = _
  rw [← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp, e]

/-- **Edges of a triangle**: a closed `1`-cochain is additive on the edges of a simplex. -/
theorem closed_edge {m : ℕ} (φ : X _⦋1⦌ → ℚ)
    (hφ : ∀ ρ : X _⦋2⦌, φ (X.δ 0 ρ) - φ (X.δ 1 ρ) + φ (X.δ 2 ρ) = 0) (τ : X _⦋m⦌)
    (a b c : Fin (m + 1)) (h₁ : a ≤ b) (h₂ : b ≤ c) :
    φ (edge X τ a c (h₁.trans h₂)) = φ (edge X τ a b h₁) + φ (edge X τ b c h₂) := by
  have := hφ (X.map (mkOfLeComp a b c h₁ h₂).op τ)
  have e0 : X.δ 0 (X.map (mkOfLeComp a b c h₁ h₂).op τ) = edge X τ b c h₂ := by
    rw [SimplicialObject.δ_def]
    rw [← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp]
    have e : SimplexCategory.δ 0 ≫ mkOfLeComp a b c h₁ h₂ = mkOfLe b c h₂ :=
      Hom.ext_one_left _ _
    rw [e]
    rfl
  have e1 : X.δ 1 (X.map (mkOfLeComp a b c h₁ h₂).op τ) = edge X τ a c (h₁.trans h₂) := by
    rw [SimplicialObject.δ_def]
    rw [← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp]
    have e : SimplexCategory.δ 1 ≫ mkOfLeComp a b c h₁ h₂ = mkOfLe a c (h₁.trans h₂) :=
      Hom.ext_one_left _ _
    rw [e]
    rfl
  have e2 : X.δ 2 (X.map (mkOfLeComp a b c h₁ h₂).op τ) = edge X τ a b h₁ := by
    rw [SimplicialObject.δ_def]
    rw [← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp]
    have e : SimplexCategory.δ 2 ≫ mkOfLeComp a b c h₁ h₂ = mkOfLe a b h₁ :=
      Hom.ext_one_left _ _
    rw [e]
    rfl
  rw [e0, e1, e2] at this
  linarith

end Edges

section Cup

open SSet SimplexCategory
open scoped Simplicial

variable (X : SSet.{0})

/-- The edges of a simplex only depend on the values of their endpoints. -/
theorem edge_congr {m : ℕ} (τ : X _⦋m⦌) {a b a' b' : Fin (m + 1)} (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : a.val = a'.val) (hb : b.val = b'.val) : edge X τ a b hab = edge X τ a' b' hab' := by
  obtain rfl : a = a' := Fin.ext ha
  obtain rfl : b = b' := Fin.ext hb
  rfl

/-- The `r`-fold (Alexander–Whitney) cup product of `1`-cochains, given by their values on the
edges `(i, i+1)`: on an `r`-simplex `σ` it is `∏ᵢ φᵢ(edge i (i+1) of σ)`. -/
def cupFun {r : ℕ} (φ : Fin r → X _⦋1⦌ → ℚ) (σ : X _⦋r⦌) : ℚ :=
  ∏ i : Fin r, φ i (edge X σ i.castSucc i.succ (Fin.castSucc_lt_succ).le)

/-- **The cup product of closed `1`-cochains is closed.** -/
theorem cupFun_closed {r : ℕ} (φ : Fin r → X _⦋1⦌ → ℚ)
    (hφ : ∀ i, ∀ ρ : X _⦋2⦌, φ i (X.δ 0 ρ) - φ i (X.δ 1 ρ) + φ i (X.δ 2 ρ) = 0)
    (τ : X _⦋r + 1⦌) :
    ∑ j : Fin (r + 2), (-1 : ℚ) ^ j.val * cupFun X φ (X.δ j τ) = 0 := by
  let aF : Fin r → ℚ := fun i => φ i (edge X τ ⟨i.val, by have := i.2; omega⟩
    ⟨i.val + 1, by have := i.2; omega⟩ (Fin.mk_le_mk.2 (by omega)))
  let bF : Fin r → ℚ := fun i => φ i (edge X τ ⟨i.val + 1, by have := i.2; omega⟩
    ⟨i.val + 2, by have := i.2; omega⟩ (Fin.mk_le_mk.2 (by omega)))
  let a : ℕ → ℚ := fun n => if h : n < r then aF ⟨n, h⟩ else 0
  let b : ℕ → ℚ := fun n => if h : n < r then bF ⟨n, h⟩ else 0
  have ha : ∀ i : Fin r, a i.val = aF i := fun i => by simp [a, i.2]
  have hb : ∀ i : Fin r, b i.val = bF i := fun i => by simp [b, i.2]
  have key : ∀ j : Fin (r + 2), cupFun X φ (X.δ j τ) = ∏ i ∈ Finset.range r, yy a b j.val i := by
    intro j
    unfold cupFun
    rw [← Fin.prod_univ_eq_prod_range (fun i => yy a b j.val i) r]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi := i.2
    rw [edge_δ]
    have s1 : (j.succAbove i.castSucc).val = if i.val < j.val then i.val else i.val + 1 := by
      unfold Fin.succAbove
      split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]
    have s2 : (j.succAbove i.succ).val = if i.val + 1 < j.val then i.val + 1 else i.val + 2 := by
      unfold Fin.succAbove
      split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]
    by_cases c1 : i.val + 2 ≤ j.val
    · rw [yy_a c1, ha]
      exact congrArg (φ i) (edge_congr X τ _ _ (by simp [s1]; omega) (by simp [s2]; omega))
    · by_cases c2 : j.val = i.val + 1
      · rw [yy_ab c2, ha, hb]
        have := closed_edge X (φ i) (hφ i) τ ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩
          ⟨i.val + 2, by omega⟩ (Fin.mk_le_mk.2 (by omega)) (Fin.mk_le_mk.2 (by omega))
        rw [← this]
        exact congrArg (φ i) (edge_congr X τ _ _ (by simp [s1]; omega) (by simp [s2]; omega))
      · rw [yy_b (by omega), hb]
        exact congrArg (φ i) (edge_congr X τ _ _ (by simp [s1]; omega) (by simp [s2]; omega))
  simp_rw [key]
  rw [Fin.sum_univ_eq_sum_range (fun j => (-1 : ℚ) ^ j * ∏ i ∈ Finset.range r, yy a b j i) (r + 2)]
  exact telescope a b r

end Cup

section CocycleClasses

variable (K : ChainComplex (ModuleCat ℚ) ℕ)

/-- A closed cochain as a cycle of the dual complex. -/
def cocycleLift (n : ℕ) (φ : Module.Dual ℚ (K.X n)) (h : (dualMap (K.d (n + 1) n)).hom φ = 0) :
    (dualComplex K).cycles n :=
  ((dualComplex K).cyclesIsoSc' (Nat.pred n) n (n + 1) (up_prev n)
      (CochainComplex.next ℕ n)).inv.hom
    (((dualComplex K).sc' (Nat.pred n) n (n + 1)).moduleCatCyclesIso.inv.hom
      ⟨φ, LinearMap.mem_ker.2 (by
        change ((dualComplex K).d n (n + 1)).hom φ = 0
        rw [dualComplex_d]
        exact h)⟩)

theorem iCycles_cocycleLift (n : ℕ) (φ : Module.Dual ℚ (K.X n))
    (h : (dualMap (K.d (n + 1) n)).hom φ = 0) :
    ((dualComplex K).iCycles n).hom (cocycleLift K n φ h) = φ := by
  have h1 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    ((dualComplex K).cyclesIsoSc'_inv_iCycles (Nat.pred n) n (n + 1) (up_prev n)
      (CochainComplex.next ℕ n)))
    (((dualComplex K).sc' (Nat.pred n) n (n + 1)).moduleCatCyclesIso.inv.hom
      ⟨φ, LinearMap.mem_ker.2 (by
        change ((dualComplex K).d n (n + 1)).hom φ = 0
        rw [dualComplex_d]
        exact h)⟩)
  have h2 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    (((dualComplex K).sc' (Nat.pred n) n (n + 1)).moduleCatCyclesIso_inv_iCycles))
    ⟨φ, LinearMap.mem_ker.2 (by
        change ((dualComplex K).d n (n + 1)).hom φ = 0
        rw [dualComplex_d]
        exact h)⟩
  exact h1.trans h2

/-- The cohomology class of a closed `n`-cochain. -/
def cocycleClass (n : ℕ) (φ : Module.Dual ℚ (K.X n)) (h : (dualMap (K.d (n + 1) n)).hom φ = 0) :
    (dualComplex K).homology n :=
  ((dualComplex K).homologyπ n).hom (cocycleLift K n φ h)

/-- The universal coefficient pairing of the class of a closed cochain with a cycle is the
evaluation of the cochain on the cycle. -/
theorem ucEquiv_cocycleClass (n : ℕ) (φ : Module.Dual ℚ (K.X n))
    (h : (dualMap (K.d (n + 1) n)).hom φ = 0) (zs : K.cycles n) :
    ucEquiv K n (cocycleClass K n φ h) ((K.homologyπ n).hom zs) =
      cochainEval K n φ ((K.iCycles n).hom zs) := by
  unfold cocycleClass
  rw [ucEquiv_apply, iCycles_cocycleLift]

/-- The class of a closed cochain only depends on the cochain. -/
theorem cocycleClass_congr (n : ℕ) {φ φ' : Module.Dual ℚ (K.X n)} (e : φ = φ')
    (h : (dualMap (K.d (n + 1) n)).hom φ = 0) (h' : (dualMap (K.d (n + 1) n)).hom φ' = 0) :
    cocycleClass K n φ h = cocycleClass K n φ' h' := by
  subst e
  rfl

/-- Every cohomology class is the class of a closed cochain. -/
theorem exists_cocycleClass (n : ℕ) (ξ : (dualComplex K).homology n) :
    ∃ (φ : Module.Dual ℚ (K.X n)) (h : (dualMap (K.d (n + 1) n)).hom φ = 0),
      ξ = cocycleClass K n φ h := by
  obtain ⟨zd, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((dualComplex K).homologyπ n)) ξ
  have hd : ((dualMap (K.d (n + 1) n)).hom (((dualComplex K).iCycles n).hom zd)) = 0 := by
    have := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      ((dualComplex K).iCycles_d n (n + 1))) zd
    rw [dualComplex_d] at this
    exact this
  refine ⟨_, hd, ?_⟩
  unfold cocycleClass
  congr 1
  refine ((ModuleCat.mono_iff_injective ((dualComplex K).iCycles n)).1 inferInstance) ?_
  exact (iCycles_cocycleLift K n _ hd).symm

/-- A chain map pulls closed cochains back to closed cochains. -/
theorem cocycle_comap {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (n : ℕ)
    {ψ : Module.Dual ℚ (L.X n)} (h : (dualMap (L.d (n + 1) n)).hom ψ = 0) :
    (dualMap (K.d (n + 1) n)).hom ((dualMap (φ.f n)).hom ψ) = 0 := by
  have e : dualMap (L.d (n + 1) n) ≫ dualMap (φ.f (n + 1)) =
      dualMap (φ.f n) ≫ dualMap (K.d (n + 1) n) := by
    rw [← dualMap_comp, ← dualMap_comp, φ.comm]
  have := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 e) ψ
  change (dualMap (φ.f (n + 1))).hom ((dualMap (L.d (n + 1) n)).hom ψ) =
    (dualMap (K.d (n + 1) n)).hom ((dualMap (φ.f n)).hom ψ) at this
  rw [← this, h, map_zero]

/-- **Naturality of the class of a closed cochain** in chain maps. -/
theorem cocycleClass_natural {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (n : ℕ)
    (ψ : Module.Dual ℚ (L.X n)) (h : (dualMap (L.d (n + 1) n)).hom ψ = 0)
    (h' : (dualMap (K.d (n + 1) n)).hom ((dualMap (φ.f n)).hom ψ) = 0) :
    (HomologicalComplex.homologyMap (dualComplexMap φ) n).hom (cocycleClass L n ψ h) =
      cocycleClass K n ((dualMap (φ.f n)).hom ψ) h' := by
  apply (ucEquiv K n).injective
  refine LinearMap.ext fun c => ?_
  obtain ⟨zs, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (K.homologyπ n)) c
  have e2 : (HomologicalComplex.homologyMap φ n).hom ((K.homologyπ n).hom zs) =
      (L.homologyπ n).hom ((HomologicalComplex.cyclesMap φ n).hom zs) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (HomologicalComplex.homologyπ_naturality φ n)) zs
  have a2 : (L.iCycles n).hom ((HomologicalComplex.cyclesMap φ n).hom zs) =
      (φ.f n).hom ((K.iCycles n).hom zs) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (HomologicalComplex.cyclesMap_i φ n)) zs
  rw [ucEquiv_natural, e2, ucEquiv_cocycleClass, ucEquiv_cocycleClass, a2]
  rfl

end CocycleClasses

section CupClass

open SSet
open scoped Simplicial

variable (X : SSet.{0})

/-- A cochain is closed iff its coboundary vanishes on every simplex. -/
theorem cocycle_iff {n : ℕ} (φ : Module.Dual ℚ ((X.chainComplex coeff).X n)) :
    (dualMap ((X.chainComplex coeff).d (n + 1) n)).hom φ = 0 ↔
      ∀ τ : X _⦋n + 1⦌, ∑ i : Fin (n + 2), (-1 : ℚ) ^ i.val * cochainVal X φ (X.δ i τ) = 0 := by
  constructor
  · intro h τ
    rw [← cochainVal_dualMap_d, h]
    simp [cochainVal]
  · intro h
    refine cochain_ext X fun τ => ?_
    rw [cochainVal_dualMap_d, h τ]
    simp [cochainVal]

/-- A closed `1`-cochain is additive on the boundary of a `2`-simplex. -/
theorem closed_one {ψ : Module.Dual ℚ ((X.chainComplex coeff).X 1)}
    (h : (dualMap ((X.chainComplex coeff).d (1 + 1) 1)).hom ψ = 0) (ρ : X _⦋2⦌) :
    cochainVal X ψ (X.δ 0 ρ) - cochainVal X ψ (X.δ 1 ρ) + cochainVal X ψ (X.δ 2 ρ) = 0 := by
  have := (cocycle_iff X ψ).1 h ρ
  simp [Fin.sum_univ_three] at this
  linarith

/-- The `r`-fold cup product cochain of `1`-cochains. -/
def cupCochain (r : ℕ) (ψ : Fin r → Module.Dual ℚ ((X.chainComplex coeff).X 1)) :
    Module.Dual ℚ ((X.chainComplex coeff).X r) :=
  cochainOfFun X (cupFun X fun i => cochainVal X (ψ i))

/-- The value of the cup product cochain on a simplex: the product of the values of the factors on
the consecutive edges. -/
theorem cupCochain_val (r : ℕ) (ψ : Fin r → Module.Dual ℚ ((X.chainComplex coeff).X 1))
    (σ : X _⦋r⦌) :
    cochainVal X (cupCochain X r ψ) σ =
      ∏ i : Fin r, cochainVal X (ψ i) (edge X σ i.castSucc i.succ (Fin.castSucc_lt_succ).le) := by
  unfold cupCochain
  rw [cochainVal_ofFun]
  rfl

/-- **The cup product of closed `1`-cochains is a closed cochain.** -/
theorem cupCochain_closed (r : ℕ) (ψ : Fin r → Module.Dual ℚ ((X.chainComplex coeff).X 1))
    (h : ∀ i, (dualMap ((X.chainComplex coeff).d (1 + 1) 1)).hom (ψ i) = 0) :
    (dualMap ((X.chainComplex coeff).d (r + 1) r)).hom (cupCochain X r ψ) = 0 := by
  rw [cocycle_iff]
  intro τ
  simp only [cupCochain, cochainVal_ofFun]
  exact cupFun_closed X _ (fun i ρ => closed_one X (h i) ρ) τ

/-- The edge `(0, 1)` of a `1`-simplex is the simplex itself. -/
theorem edge_zero_one (σ : X _⦋1⦌) : edge X σ 0 1 (by decide) = σ := by
  have e : SimplexCategory.mkOfLe (0 : Fin 2) 1 (by decide) = 𝟙 _ :=
    SimplexCategory.Hom.ext_one_left _ _
  unfold edge
  rw [e]
  simp

/-- The cup product of a single `1`-cochain is that cochain. -/
theorem cupCochain_one (ψ : Fin 1 → Module.Dual ℚ ((X.chainComplex coeff).X 1)) :
    cupCochain X 1 ψ = ψ 0 := by
  refine cochain_ext X fun σ => ?_
  rw [cupCochain_val, Fin.prod_univ_one]
  have : edge X σ (Fin.castSucc 0) (Fin.succ 0) (Fin.castSucc_lt_succ).le = σ :=
    (edge_congr X σ _ (by decide) (by simp) (by simp)).trans (edge_zero_one X σ)
  rw [this]

/-- The value of a pulled-back cochain is the value of the cochain on the image simplex. -/
theorem cochainVal_comap {Y : SSet.{0}} (f : X ⟶ Y) {n : ℕ}
    (φ : Module.Dual ℚ ((Y.chainComplex coeff).X n)) (x : X _⦋n⦌) :
    cochainVal X ((dualMap ((chainComplexMap f coeff).f n)).hom φ) x =
      cochainVal Y φ (f.app _ x) := by
  change φ (((chainComplexMap f coeff).f n).hom ((X.ιChainComplex (R := coeff) x).hom 1)) = _
  have := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    (SSet.ι_chainComplexMap_f X Y f coeff x)) 1
  exact congrArg φ this

/-- **Naturality of the cup product cochain** in maps of simplicial sets. -/
theorem cupCochain_comap {Y : SSet.{0}} (f : X ⟶ Y) (r : ℕ)
    (ψ : Fin r → Module.Dual ℚ ((Y.chainComplex coeff).X 1)) :
    (dualMap ((chainComplexMap f coeff).f r)).hom (cupCochain Y r ψ) =
      cupCochain X r fun i => (dualMap ((chainComplexMap f coeff).f 1)).hom (ψ i) := by
  refine cochain_ext X fun σ => ?_
  rw [cochainVal_comap, cupCochain_val, cupCochain_val]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [cochainVal_comap]
  congr 1
  exact (NatTrans.naturality_apply f _ σ).symm

end CupClass

section SingularCup

open AlgebraicTopology

/-- The singular simplicial set of a space. -/
abbrev singSSet (T : TopCat.{0}) : SSet.{0} := TopCat.toSSet.obj T

theorem singularChain_obj (T : TopCat.{0}) :
    singularChain.obj T = (singSSet T).chainComplex coeff := rfl

/-- **The cup product class** `[ψ₁ ∪ ⋯ ∪ ψᵣ] ∈ Hʳ(T; ℚ)` of closed singular `1`-cochains
`ψ₁, …, ψᵣ`: the class of the Alexander–Whitney `r`-fold cup product cochain
(`cupCochain`), whose value on a singular `r`-simplex `σ` is `∏ᵢ ψᵢ(σ|[i, i+1])`. -/
def singularCupClass (T : TopCat.{0}) (r : ℕ)
    (ψ : Fin r → Module.Dual ℚ ((singularChain.obj T).X 1))
    (h : ∀ i, (dualMap ((singularChain.obj T).d (1 + 1) 1)).hom (ψ i) = 0) :
    singularCohomology T r :=
  cocycleClass (singularChain.obj T) r (cupCochain (singSSet T) r ψ)
    (cupCochain_closed (singSSet T) r ψ h)

/-- The pairing of a cup product class with a singular cycle is the value of the cup product
cochain on it. -/
theorem ucEquiv_singularCupClass (T : TopCat.{0}) (r : ℕ)
    (ψ : Fin r → Module.Dual ℚ ((singularChain.obj T).X 1))
    (h : ∀ i, (dualMap ((singularChain.obj T).d (1 + 1) 1)).hom (ψ i) = 0)
    (z : (singularChain.obj T).cycles r) :
    singularUC T r (singularCupClass T r ψ h) (((singularChain.obj T).homologyπ r).hom z) =
      cochainEval (singularChain.obj T) r (cupCochain (singSSet T) r ψ)
        (((singularChain.obj T).iCycles r).hom z) :=
  ucEquiv_cocycleClass (singularChain.obj T) r _ _ z

/-- **Naturality of the cup product class** in continuous maps. -/
theorem singularCupClass_natural {T T' : TopCat.{0}} (g : T ⟶ T') (r : ℕ)
    (ψ : Fin r → Module.Dual ℚ ((singularChain.obj T').X 1))
    (h : ∀ i, (dualMap ((singularChain.obj T').d (1 + 1) 1)).hom (ψ i) = 0)
    (h' : ∀ i, (dualMap ((singularChain.obj T).d (1 + 1) 1)).hom
      ((dualMap ((singularChain.map g).f 1)).hom (ψ i)) = 0) :
    (singularCohomologyMap g r).hom (singularCupClass T' r ψ h) =
      singularCupClass T r (fun i => (dualMap ((singularChain.map g).f 1)).hom (ψ i)) h' := by
  unfold singularCupClass
  refine (cocycleClass_natural (singularChain.map g) r _ (cupCochain_closed (singSSet T') r ψ h)
    (cocycle_comap (singularChain.map g) r (cupCochain_closed (singSSet T') r ψ h))).trans ?_
  exact cocycleClass_congr (singularChain.obj T) r
    (cupCochain_comap (singSSet T) (TopCat.toSSet.map g) r ψ) _ _

end SingularCup

section BettiCup

open AlgebraicGeometry ArithmeticOfJacobiPolynomials.ComplexRealization

/-- **The cup product class on the complex points of a scheme**: the class in
`Hʳ(X(ℂ), ℚ)` of the `r`-fold Alexander–Whitney cup product of closed singular `1`-cochains of
the analytic space of complex points. -/
def bettiCupClass (X : Over (Spec (CommRingCat.of ℂ))) (r : ℕ)
    (ψ : Fin r → Module.Dual ℚ ((singularChain.obj (space X)).X 1))
    (h : ∀ i, (dualMap ((singularChain.obj (space X)).d (1 + 1) 1)).hom (ψ i) = 0) :
    bettiCohomology X r :=
  singularCupClass (space X) r ψ h

end BettiCup

end ArithmeticOfJacobiPolynomials.AbelianBettiCohomology
