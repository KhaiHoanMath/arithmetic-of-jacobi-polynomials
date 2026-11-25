/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# The dual abelian variety and its Poincaré class

The definition uses the Picard groups of products of schemes. A normalized
family is trivial on the zero section, and every geometric fibre is invariant under
translations. Representability by an abelian variety is characterized by pullback of
one Poincaré class. This file supplies definitions and elementary group properties;
existence and the Weil pairing require separate cited propositions in `External.lean`.

The characterization is Milne, *Abelian Varieties*, §9, conditions (a) and (b), with
translation invariance as in Proposition 9.2.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials.AbelianDuality

variable {k : Type u} [Field k]

/-- Translation by a rational point, using the library group law on scheme morphisms. -/
def translate (A : Over (Spec (.of k))) [GrpObj A] (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    A ⟶ A :=
  (toUnit A ≫ a) * 𝟙 A

@[simp]
theorem translate_one (A : Over (Spec (.of k))) [GrpObj A] :
    translate A (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) = 𝟙 A := by
  simp only [translate, MonObj.comp_one, one_mul]

/-- A Picard class fixed by every rational translation. -/
def IsTranslationInvariant (A : Over (Spec (.of k))) [GrpObj A]
    (M : Stacks.Picard.ofScheme A.left) : Prop :=
  ∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ A,
    Stacks.Picard.schemePullbackClass (translate A a).left M = M

/-- Translation-invariant classes form a subgroup of the Picard group. -/
def translationInvariantClasses (A : Over (Spec (.of k))) [GrpObj A] :
    AddSubgroup (Stacks.Picard.ofScheme A.left) where
  carrier := {M | IsTranslationInvariant A M}
  zero_mem' a := (Stacks.Picard.schemePullbackClassHom (translate A a).left).map_zero
  add_mem' {M N} hM hN a := by
    rw [Stacks.Picard.schemePullbackClass_add, hM a, hN a]
  neg_mem' {M} hM a := by
    change (Stacks.Picard.schemePullbackClassHom (translate A a).left) (-M) = -M
    rw [map_neg]
    change -Stacks.Picard.schemePullbackClass (translate A a).left M = -M
    rw [hM a]

variable (A : Over (Spec (.of k))) [GrpObj A] (T : Over (Spec (.of k)))

/-- The zero section of the product `A × T → T`. -/
def zeroSection : T ⟶ A ⊗ T := lift (1 : T ⟶ A) (𝟙 T)

/-- Restriction of a family to a geometric point of its parameter scheme.
The source is the base change `A_Ω`. -/
def familyFibreMap (Ω : Type u) [Field Ω] [Algebra k Ω]
    (t : GroupScheme.specOver k Ω ⟶ T) :
    (GroupScheme.baseChange Ω A).left ⟶ (A ⊗ T).left :=
  let B := GroupScheme.baseChange Ω A
  let mapped := (Over.map (GroupScheme.specMapAlgebra Ω)).obj B
  let q : mapped ⟶ GroupScheme.specOver k Ω := Over.homMk B.hom rfl
  let ε : mapped ⟶ A := (Over.mapPullbackAdj (GroupScheme.specMapAlgebra Ω)).counit.app A
  (lift ε (q ≫ t)).left

/-- A family of algebraically trivial line bundles, normalized on the zero section.
Translation invariance is tested on every algebraically closed geometric fibre. -/
def IsNormalizedFamily (M : Stacks.Picard.ofScheme (A ⊗ T).left) : Prop :=
  Stacks.Picard.schemePullbackClass (zeroSection A T).left M = 0 ∧
    ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (t : GroupScheme.specOver k Ω ⟶ T),
      IsTranslationInvariant (GroupScheme.baseChange Ω A)
        (Stacks.Picard.schemePullbackClass (familyFibreMap A T Ω t) M)

/-- The subgroup of normalized families in `Pic(A × T)`. -/
def normalizedFamilies : AddSubgroup (Stacks.Picard.ofScheme (A ⊗ T).left) where
  carrier := {M | IsNormalizedFamily A T M}
  zero_mem' := by
    constructor
    · exact (Stacks.Picard.schemePullbackClassHom (zeroSection A T).left).map_zero
    · intro Ω _ _ _ t
      have hzero : Stacks.Picard.schemePullbackClass (familyFibreMap A T Ω t) 0 = 0 :=
        (Stacks.Picard.schemePullbackClassHom (familyFibreMap A T Ω t)).map_zero
      rw [hzero]
      exact (translationInvariantClasses (GroupScheme.baseChange Ω A)).zero_mem
  add_mem' {M N} hM hN := by
    constructor
    · rw [Stacks.Picard.schemePullbackClass_add, hM.1, hN.1, add_zero]
    · intro Ω _ _ _ t
      rw [Stacks.Picard.schemePullbackClass_add]
      exact (translationInvariantClasses (GroupScheme.baseChange Ω A)).add_mem
        (hM.2 Ω t) (hN.2 Ω t)
  neg_mem' {M} hM := by
    constructor
    · change (Stacks.Picard.schemePullbackClassHom (zeroSection A T).left) (-M) = 0
      rw [map_neg]
      change -Stacks.Picard.schemePullbackClass (zeroSection A T).left M = 0
      rw [hM.1, neg_zero]
    · intro Ω _ _ _ t
      change IsTranslationInvariant (GroupScheme.baseChange Ω A)
        ((Stacks.Picard.schemePullbackClassHom (familyFibreMap A T Ω t)) (-M))
      rw [map_neg]
      exact (translationInvariantClasses (GroupScheme.baseChange Ω A)).neg_mem (hM.2 Ω t)

/-- `D` is the dual abelian variety of `A`, and `P` its normalized Poincaré class.
The universal property quantifies over all parameter schemes and Picard classes.
It is expressed on isomorphism classes, so equality means an isomorphism of line bundles. -/
structure IsPoincarePair (D : Over (Spec (.of k))) [GrpObj D]
    (P : Stacks.Picard.ofScheme (A ⊗ D).left) where
  isAbelianVariety : IsAbelianVariety k D
  normalized : IsNormalizedFamily A D P
  homMulEquiv (T : Over (Spec (.of k))) :
    (T ⟶ D) ≃* Multiplicative (normalizedFamilies A T)
  homMulEquiv_class (T : Over (Spec (.of k))) (a : T ⟶ D) :
    (Multiplicative.toAdd (homMulEquiv T a)).1 =
      Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ a).left P

/-- The Poincaré group representation implies the usual line-bundle universal property. -/
theorem IsPoincarePair.universal {D : Over (Spec (.of k))} [GrpObj D]
    {P : Stacks.Picard.ofScheme (A ⊗ D).left} (hP : IsPoincarePair A D P)
    (T : Over (Spec (.of k))) (M : Stacks.Picard.ofScheme (A ⊗ T).left)
    (hM : IsNormalizedFamily A T M) :
    ∃! a : T ⟶ D, Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ a).left P = M := by
  let ξ : Multiplicative (normalizedFamilies A T) := Multiplicative.ofAdd ⟨M, hM⟩
  refine ⟨(hP.homMulEquiv T).symm ξ, ?_, ?_⟩
  · change Stacks.Picard.schemePullbackClass
      ((𝟙 A) ⊗ₘ (hP.homMulEquiv T).symm ξ).left P = M
    rw [← hP.homMulEquiv_class, MulEquiv.apply_symm_apply]
    rfl
  · intro a ha
    apply (hP.homMulEquiv T).injective
    rw [MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact (hP.homMulEquiv_class T a).trans ha

/-- The Poincaré pullback determines the morphism to the dual uniquely. -/
theorem IsPoincarePair.pullback_injective {D : Over (Spec (.of k))} [GrpObj D]
    {P : Stacks.Picard.ofScheme (A ⊗ D).left} (hP : IsPoincarePair A D P)
    {a b : T ⟶ D}
    (h : Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ a).left P =
      Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ b).left P) : a = b := by
  apply (hP.homMulEquiv T).injective
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact (hP.homMulEquiv_class T a).trans (h.trans (hP.homMulEquiv_class T b).symm)

/-- Multiplication of morphisms corresponds to tensor product of their Poincaré classes. -/
theorem IsPoincarePair.pullback_mul {D : Over (Spec (.of k))} [GrpObj D]
    {P : Stacks.Picard.ofScheme (A ⊗ D).left} (hP : IsPoincarePair A D P)
    (a b : T ⟶ D) :
    Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ (a * b)).left P =
      Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ a).left P +
        Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ b).left P := by
  rw [← hP.homMulEquiv_class T (a * b), ← hP.homMulEquiv_class T a,
    ← hP.homMulEquiv_class T b, map_mul]
  rfl

/-- Two Poincaré representatives are uniquely isomorphic as schemes over the base field. -/
theorem IsPoincarePair.exists_iso {D E : Over (Spec (.of k))} [GrpObj D] [GrpObj E]
    {P : Stacks.Picard.ofScheme (A ⊗ D).left}
    {Q : Stacks.Picard.ofScheme (A ⊗ E).left}
    (hP : IsPoincarePair A D P) (hQ : IsPoincarePair A E Q) :
    ∃ e : D ≅ E, Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ e.hom).left Q = P := by
  obtain ⟨f, hf, _⟩ := hQ.universal A D P hP.normalized
  obtain ⟨g, hg, _⟩ := hP.universal A E Q hQ.normalized
  have hcomp (T U V : Over (Spec (.of k))) (a : T ⟶ U) (b : U ⟶ V)
      (R : Stacks.Picard.ofScheme (A ⊗ V).left) :
      Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ (a ≫ b)).left R =
        Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ a).left
          (Stacks.Picard.schemePullbackClass ((𝟙 A) ⊗ₘ b).left R) := by
    rw [Stacks.Picard.schemePullbackClass_comp]
    congr 1
    simpa only [← Over.comp_left] using
      congrArg Over.Hom.left (id_tensor_comp (Z := A) a b)
  have hfg : f ≫ g = 𝟙 D := by
    apply hP.pullback_injective A D
    rw [hcomp D E D f g P, hg, hf]
    simp
  have hgf : g ≫ f = 𝟙 E := by
    apply hQ.pullback_injective A E
    rw [hcomp E D E g f Q, hf, hg]
    simp
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end ArithmeticOfJacobiPolynomials.AbelianDuality
