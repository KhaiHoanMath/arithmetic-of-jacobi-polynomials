/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.HodgeStructure
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiCohomology
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiHodge
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Hodge classes in the Betti cohomology of an abelian variety

Manuscript, Corollary 6.6: a Hodge class is a class
in `H^{2c}(A(ℂ), ℚ)`, the singular cohomology of the analytic space of complex points
(`ArithmeticOfJacobiPolynomials.AbelianBettiCohomology.bettiCohomology`).

## The comparison with exterior powers of `H¹` is pinned by the cup product

`H^r(A(ℂ), ℚ)` is **not** defined here as an exterior power. The (cited, general) theorem that for
a complex torus the cup product induces an isomorphism `⋀^r H¹ ≃ H^r` is recorded as a *datum*
`CupComparison X r`: a linear equivalence `e : ⋀^r_ℚ H¹(X(ℂ),ℚ) ≃ H^r(X(ℂ),ℚ)` which is
**normalized by the cup product of singular cochains**:

`e (ψ₁ ∧ ⋯ ∧ ψᵣ) = [ψ₁ ∪ ⋯ ∪ ψᵣ]`

for all closed singular `1`-cochains `ψᵢ`, where `[ψ₁ ∪ ⋯ ∪ ψᵣ]` is the class of the
Alexander–Whitney `r`-fold cup product cochain `σ ↦ ∏ᵢ ψᵢ(σ|[i,i+1])`
(`AbelianBettiCohomology.bettiCupClass`, proved closed in `cupCochain_closed`). A zero or arbitrary
linear map does not satisfy this normalization (whenever some cup product class is nonzero), and the
datum is **unique** (`CupComparison.toEquiv_unique`): the decomposable wedges span `⋀^r`.
The existence of the datum for every complex abelian variety is the cited theorem of
Milne, *Abelian Varieties* (course notes v2.00, 2008), Chapter I, §2, Theorem 2.3 (the full
real-torus input is recorded in `External.lean`).

## Hodge classes

For a `ℚ`-Hodge structure `H` of type `{(-1,0),(0,-1)}` on `V = H₁(A(ℂ), ℚ)` (in applications the
canonical one `D.canonicalHodge` transported from the complex structure of `Lie A`), the Hodge
classes of degree `r` in `⋀^r V^∨` are the elements whose antisymmetrization in
`TensorSpace ℚ V 0 r = (V^∨)^{⊗r}` is fixed by the circle `U(1) ⊂ ℂˣ` acting through `h`
(`HodgeStructureNegOne.hodgeClasses`, i.e. type `(r/2, r/2)`). Transported by the universal
coefficient identification `H¹ = V^∨` (`bettiUC`) and the comparison `e`, this defines
`hodgeClassesBetti H e ⊆ H^r(A(ℂ), ℚ)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open ArithmeticOfJacobiPolynomials.AbelianBettiCohomology
  ArithmeticOfJacobiPolynomials.AbelianBettiHodge
open ArithmeticOfJacobiPolynomials.ComplexRealization

namespace ArithmeticOfJacobiPolynomials.AbelianHodgeClasses

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- **Antisymmetrization is natural**: `Mathlib`'s `exteriorPower.toTensorPower`
(`ω ↦ Σ_σ sgn σ · (ω∘σ)` on decomposables) commutes with the maps induced by a linear map. -/
theorem toTensorPower_map {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N]
    [Module ℚ N] (g : M →ₗ[ℚ] N) (r : ℕ) (ω : ⋀[ℚ]^r M) :
    exteriorPower.toTensorPower ℚ N r (exteriorPower.map r g ω) =
      PiTensorProduct.map (fun _ : Fin r => g) (exteriorPower.toTensorPower ℚ M r ω) := by
  have h : exteriorPower.toTensorPower ℚ N r ∘ₗ exteriorPower.map r g =
      PiTensorProduct.map (fun _ : Fin r => g) ∘ₗ exteriorPower.toTensorPower ℚ M r := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span ℚ r M) ?_
    rintro _ ⟨a, rfl⟩
    simp only [LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.toTensorPower_apply_ιMulti, map_sum, Function.comp_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, Units.smul_def, map_zsmul, PiTensorProduct.map_tprod]
  exact LinearMap.congr_fun h ω

/-- **Antisymmetrization is injective over `ℚ`**: the quotient map `M^{⊗r} → ⋀^r M` composed
with it is multiplication by `r!`. -/
theorem toTensorPower_injective (M : Type*) [AddCommGroup M] [Module ℚ M] (r : ℕ) :
    Function.Injective (exteriorPower.toTensorPower ℚ M r) := by
  let π : TensorPower ℚ r M →ₗ[ℚ] ⋀[ℚ]^r M :=
    PiTensorProduct.lift (exteriorPower.ιMulti ℚ r).toMultilinearMap
  have h : π ∘ₗ exteriorPower.toTensorPower ℚ M r = ((r.factorial : ℚ)) • LinearMap.id := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span ℚ r M) ?_
    rintro _ ⟨a, rfl⟩
    simp only [LinearMap.comp_apply, exteriorPower.toTensorPower_apply_ιMulti, map_sum,
      LinearMap.smul_apply, LinearMap.id_apply]
    have hπ : ∀ b : Fin r → M, π (PiTensorProduct.tprod ℚ b) = exteriorPower.ιMulti ℚ r b :=
      fun b => PiTensorProduct.lift.tprod _
    have e : ∀ σ : Equiv.Perm (Fin r), π (Equiv.Perm.sign σ •
        PiTensorProduct.tprod ℚ (fun i => a (σ i))) = exteriorPower.ιMulti ℚ r a := by
      intro σ
      rw [Units.smul_def, map_zsmul, hπ, show (fun i => a (σ i)) = a ∘ σ from rfl,
        AlternatingMap.map_perm, Units.smul_def, smul_smul]
      have : ((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ)) = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [this, one_smul]
    simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul]
  intro x y hxy
  have := congrArg π hxy
  have h2 := LinearMap.congr_fun h x
  have h3 := LinearMap.congr_fun h y
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2 h3
  rw [h2, h3] at this
  exact smul_right_injective _ (Nat.cast_ne_zero.2 r.factorial_ne_zero) this

/-- The embedding of `⋀^r V^∨` into the tensor space `T 0 r = (V^∨)^{⊗r}` (`⊗` the empty
tensor in the covariant factor). -/
def hodgeEmbed (V : Type*) [AddCommGroup V] [Module ℚ V] (r : ℕ) :
    ⋀[ℚ]^r (Module.Dual ℚ V) →ₗ[ℚ] TensorSpace ℚ V 0 r :=
  (TensorProduct.mk ℚ (TensorPower ℚ 0 V) (TensorPower ℚ r (Module.Dual ℚ V))
    (unitTensor ℚ V)) ∘ₗ exteriorPower.toTensorPower ℚ (Module.Dual ℚ V) r

/-- **Hodge classes of degree `r` in `⋀^r V^∨`**: those whose image in `T 0 r` is a Hodge class
(circle-invariant after realification) for the Hodge structure `H`. -/
def hodgeExterior (H : HodgeStructureNegOne V) (r : ℕ) :
    Submodule ℚ (⋀[ℚ]^r (Module.Dual ℚ V)) :=
  (H.hodgeClasses 0 r).comap (hodgeEmbed V r)

theorem mem_hodgeExterior (H : HodgeStructureNegOne V) {r : ℕ} {ω : ⋀[ℚ]^r (Module.Dual ℚ V)} :
    ω ∈ hodgeExterior H r ↔ hodgeEmbed V r ω ∈ H.hodgeClasses 0 r :=
  Iff.rfl

/-- Hodge classes in `⋀^r V^∨` are the circle-invariant ones. -/
theorem mem_hodgeExterior_iff_circle (H : HodgeStructureNegOne V) {r : ℕ}
    {ω : ⋀[ℚ]^r (Module.Dual ℚ V)} :
    ω ∈ hodgeExterior H r ↔
      ∀ z : Circle, tensorMap 0 r (H.circleRep z) (realify 0 r (hodgeEmbed V r ω)) =
        realify 0 r (hodgeEmbed V r ω) :=
  Iff.rfl

/-- `hodgeEmbed` is injective: the alternating tensors of `V^∨` are faithfully recorded in `T 0 r`,
so the circle-fixed elements of `⋀^r V^∨` are exactly the preimage of the Hodge classes of
`T 0 r` under an embedding. -/
theorem hodgeEmbed_injective (V : Type*) [AddCommGroup V] [Module ℚ V] (r : ℕ) :
    Function.Injective (hodgeEmbed V r) := by
  intro x y hxy
  refine toTensorPower_injective (Module.Dual ℚ V) r ?_
  have h := congrArg (fun t => TensorProduct.lid ℚ (TensorPower ℚ r (Module.Dual ℚ V))
    (TensorProduct.map (PiTensorProduct.isEmptyEquiv (R := ℚ) (s := fun _ : Fin 0 => V)
      (Fin 0)).toLinearMap LinearMap.id t)) hxy
  simpa [hodgeEmbed, unitTensor] using h

/-- The Hodge classes of `⋀^r V^∨` map isomorphically onto the Hodge classes of `T 0 r` that are
alternating. -/
theorem map_hodgeExterior (H : HodgeStructureNegOne V) (r : ℕ) :
    (hodgeExterior H r).map (hodgeEmbed V r) =
      LinearMap.range (hodgeEmbed V r) ⊓ H.hodgeClasses 0 r :=
  Submodule.map_comap_eq _ _

/-- **`hodgeEmbed` is natural**: for `f : V → W`, pushing the antisymmetrized tensor of `W^∨`
along the `V^∨`-side transposes is antisymmetrizing the pullback of the form. -/
theorem tensorPush_hodgeEmbed {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (f : V →ₗ[ℚ] W) (r : ℕ) (ω : ⋀[ℚ]^r (Module.Dual ℚ W)) :
    tensorPush (fun i : Fin 0 => (Fin.elim0 i : W →ₗ[ℚ] V)) (fun _ : Fin r => f)
        (hodgeEmbed W r ω) =
      hodgeEmbed V r (exteriorPower.map r f.dualMap ω) := by
  change tensorPush _ _ (unitTensor ℚ W ⊗ₜ exteriorPower.toTensorPower ℚ _ r ω) = _
  rw [tensorPush_tmul, map_unitTensor]
  change _ = unitTensor ℚ V ⊗ₜ[ℚ]
    exteriorPower.toTensorPower ℚ _ r (exteriorPower.map r f.dualMap ω)
  rw [toTensorPower_map]

/-- **Functoriality of Hodge classes in exterior powers**: if `f : V → W` is compatible with the
complex structures, `f^∨ : W^∨ → V^∨` maps the Hodge classes of `⋀^r W^∨` into those of
`⋀^r V^∨`. -/
theorem map_dualMap_mem_hodgeExterior {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (HV : HodgeStructureNegOne V) (HW : HodgeStructureNegOne W)
    (f : V →ₗ[ℚ] W) (hf : ∀ y, HW.J (f.baseChange ℝ y) = f.baseChange ℝ (HV.J y)) {r : ℕ}
    {ω : ⋀[ℚ]^r (Module.Dual ℚ W)} (hω : ω ∈ hodgeExterior HW r) :
    exteriorPower.map r f.dualMap ω ∈ hodgeExterior HV r := by
  rw [mem_hodgeExterior, ← tensorPush_hodgeEmbed]
  exact HodgeStructureNegOne.tensorPush_mem_hodgeClasses HW HV _ _
    (fun k => k.elim0) (fun k y => hf y) hω

end Algebraic

section Comparison

/-- **The cup-product comparison datum** `⋀^r H¹ ≃ H^r` of the Betti cohomology of a scheme
`X` over `ℂ`: a linear equivalence normalized by the cup product of singular cochains. -/
structure CupComparison (X : Over (Spec (CommRingCat.of ℂ))) (r : ℕ) where
  /-- The comparison isomorphism `⋀^r_ℚ H¹(X(ℂ), ℚ) ≃ H^r(X(ℂ), ℚ)`. -/
  toEquiv : (⋀[ℚ]^r (bettiCohomology X 1)) ≃ₗ[ℚ] bettiCohomology X r
  /-- **Normalization by the cup product**: the wedge of the classes of closed singular
  `1`-cochains is sent to the class of their `r`-fold Alexander–Whitney cup product. -/
  cup_ιMulti : ∀ (ψ : Fin r → Module.Dual ℚ ((singularChain.obj (space X)).X 1))
    (h : ∀ i, (dualMap ((singularChain.obj (space X)).d (1 + 1) 1)).hom (ψ i) = 0),
    toEquiv (exteriorPower.ιMulti ℚ r fun i =>
        cocycleClass (singularChain.obj (space X)) 1 (ψ i) (h i)) = bettiCupClass X r ψ h

/-- **The comparison is unique**: any two cup-normalized comparisons agree. -/
theorem CupComparison.toEquiv_unique {X : Over (Spec (CommRingCat.of ℂ))} {r : ℕ}
    (c c' : CupComparison X r) : c.toEquiv = c'.toEquiv := by
  refine LinearEquiv.ext fun x => ?_
  have h : c.toEquiv.toLinearMap = c'.toEquiv.toLinearMap := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span ℚ r (bettiCohomology X 1)) ?_
    rintro _ ⟨ξ, rfl⟩
    choose ψ hψ hξ using fun i => exists_cocycleClass (singularChain.obj (space X)) 1 (ξ i)
    have hξ' : ξ = fun i => cocycleClass (singularChain.obj (space X)) 1 (ψ i) (hψ i) :=
      funext hξ
    subst hξ'
    exact (c.cup_ιMulti ψ hψ).trans (c'.cup_ιMulti ψ hψ).symm
  exact LinearMap.congr_fun h x

/-- **Consistency of the normalization in degree one**: the cup product of a single `1`-cochain is
the cochain itself, so `⋀¹ H¹ = H¹` satisfies the normalization. (For `r ≥ 2` the existence of
the comparison is the cited theorem on the cohomology of tori.) -/
def CupComparison.one (X : Over (Spec (CommRingCat.of ℂ))) : CupComparison X 1 where
  toEquiv := exteriorPower.oneEquiv ℚ (bettiCohomology X 1)
  cup_ιMulti ψ h :=
    (exteriorPower.oneEquiv_ιMulti (M := bettiCohomology X 1)
      (fun i => cocycleClass (singularChain.obj (space X)) 1 (ψ i) (h i))).trans
      (cocycleClass_congr (singularChain.obj (space X)) 1
        (cupCochain_one (singSSet (space X)) ψ).symm _ _)

/-- **Naturality of the cup-normalized comparison.** For every morphism `f : A ⟶ B` of schemes over
`ℂ`, pulling back `Hʳ(B(ℂ), ℚ) → Hʳ(A(ℂ), ℚ)` intertwines the two cup-normalized comparisons with
`⋀^r` of the pullback on `H¹`. The proof is the spanning argument of uniqueness: on
`[ψ₁] ∧ ⋯ ∧ [ψᵣ]` both sides are the class of the cup product of the pulled-back cochains
(`singularCupClass_natural`, `cocycleClass_natural`). -/
theorem CupComparison.natural {A B : Over (Spec (CommRingCat.of ℂ))} (f : A ⟶ B) {r : ℕ}
    (cA : CupComparison A r) (cB : CupComparison B r) (ξ : ⋀[ℚ]^r (bettiCohomology B 1)) :
    (bettiCohomologyMap f r).hom (cB.toEquiv ξ) =
      cA.toEquiv (exteriorPower.map r (bettiCohomologyMap f 1).hom ξ) := by
  have h : (bettiCohomologyMap f r).hom ∘ₗ cB.toEquiv.toLinearMap =
      cA.toEquiv.toLinearMap ∘ₗ exteriorPower.map r (bettiCohomologyMap f 1).hom := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span ℚ r (bettiCohomology B 1)) ?_
    rintro _ ⟨ξ, rfl⟩
    choose ψ hψ hξ using fun i => exists_cocycleClass (singularChain.obj (space B)) 1 (ξ i)
    have hξ' : ξ = fun i => cocycleClass (singularChain.obj (space B)) 1 (ψ i) (hψ i) :=
      funext hξ
    subst hξ'
    have h' : ∀ i, (dualMap ((singularChain.obj (space A)).d (1 + 1) 1)).hom
        ((dualMap ((singularChain.map (spaceMap f)).f 1)).hom (ψ i)) = 0 := fun i =>
      cocycle_comap (singularChain.map (spaceMap f)) 1 (hψ i)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have e1 : (bettiCohomologyMap f r).hom (bettiCupClass B r ψ hψ) =
        bettiCupClass A r (fun i => (dualMap ((singularChain.map (spaceMap f)).f 1)).hom (ψ i))
          h' := singularCupClass_natural (spaceMap f) r ψ hψ h'
    have e2 : ((bettiCohomologyMap f 1).hom ∘
        fun i => cocycleClass (singularChain.obj (space B)) 1 (ψ i) (hψ i)) =
        fun i => cocycleClass (singularChain.obj (space A)) 1
          ((dualMap ((singularChain.map (spaceMap f)).f 1)).hom (ψ i)) (h' i) :=
      funext fun i => cocycleClass_natural (singularChain.map (spaceMap f)) 1 (ψ i) (hψ i) (h' i)
    refine Eq.trans ?_ (congrArg cA.toEquiv
      (exteriorPower.map_apply_ιMulti (bettiCohomologyMap f 1).hom _).symm)
    rw [cB.cup_ιMulti ψ hψ, e1, e2]
    exact (cA.cup_ιMulti _ h').symm
  exact LinearMap.congr_fun h ξ

end Comparison

section Hodge

variable {A : CSch}

/-- `⋀^r H¹(A(ℂ), ℚ) → ⋀^r (H₁(A(ℂ), ℚ))^∨`, induced by the universal coefficient identification
`H¹ = (H₁)^∨`. -/
def hodgeToDual (A : CSch) (r : ℕ) :
    ⋀[ℚ]^r (bettiCohomology A 1) →ₗ[ℚ] ⋀[ℚ]^r (Module.Dual ℚ (bettiOne A)) :=
  exteriorPower.map r (bettiUC A 1).toLinearMap

/-- **Hodge classes** in `H^r(A(ℂ), ℚ)` for a Hodge structure `H` on `H₁(A(ℂ), ℚ)`,
relative to a cup-normalized comparison `e : ⋀^r H¹ ≃ H^r`: the classes whose exterior preimage in
`⋀^r H¹`, read in `⋀^r (H₁)^∨`, is a Hodge class of `H`. -/
def hodgeClassesBetti (H : HodgeStructureNegOne (bettiOne A)) {r : ℕ} (c : CupComparison A r) :
    Submodule ℚ (bettiCohomology A r) :=
  (hodgeExterior H r).comap (hodgeToDual A r ∘ₗ c.toEquiv.symm.toLinearMap)

theorem mem_hodgeClassesBetti (H : HodgeStructureNegOne (bettiOne A)) {r : ℕ}
    (c : CupComparison A r) {x : bettiCohomology A r} :
    x ∈ hodgeClassesBetti H c ↔ hodgeToDual A r (c.toEquiv.symm x) ∈ hodgeExterior H r :=
  Iff.rfl

/-- The comparison datum is unique, hence so are the Hodge classes. -/
theorem hodgeClassesBetti_eq (H : HodgeStructureNegOne (bettiOne A)) {r : ℕ}
    (c c' : CupComparison A r) : hodgeClassesBetti H c = hodgeClassesBetti H c' := by
  unfold hodgeClassesBetti
  rw [CupComparison.toEquiv_unique c c']

/-- `⋀^r` of the universal coefficient identification is natural in the morphism. -/
theorem hodgeToDual_natural {A B : CSch} (f : A ⟶ B) (r : ℕ) (η : ⋀[ℚ]^r (bettiCohomology B 1)) :
    hodgeToDual A r (exteriorPower.map r (bettiCohomologyMap f 1).hom η) =
      exteriorPower.map r (bettiOneMap f).dualMap (hodgeToDual B r η) := by
  have h : (bettiUC A 1).toLinearMap ∘ₗ (bettiCohomologyMap f 1).hom =
      (bettiOneMap f).dualMap ∘ₗ (bettiUC B 1).toLinearMap :=
    LinearMap.ext fun ξ => LinearMap.ext fun c => bettiUC_natural f 1 ξ c
  unfold hodgeToDual
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, h, exteriorPower.map_comp,
    LinearMap.comp_apply]

/-- **Hodge classes pull back along every morphism compatible with the Hodge structures.** If
`H₁(f)` intertwines the complex structures, the pullback `Hʳ(B(ℂ), ℚ) → Hʳ(A(ℂ), ℚ)` maps the
Hodge classes of `B` into those of `A`, for any cup-normalized comparisons. -/
theorem map_mem_hodgeClassesBetti {A B : CSch} (f : A ⟶ B)
    (HA : HodgeStructureNegOne (bettiOne A)) (HB : HodgeStructureNegOne (bettiOne B))
    (hf : ∀ y, HB.J (bettiMapR f y) = bettiMapR f (HA.J y)) {r : ℕ}
    (cA : CupComparison A r) (cB : CupComparison B r) {x : bettiCohomology B r}
    (hx : x ∈ hodgeClassesBetti HB cB) :
    (bettiCohomologyMap f r).hom x ∈ hodgeClassesBetti HA cA := by
  rw [mem_hodgeClassesBetti] at hx ⊢
  have e : cA.toEquiv.symm ((bettiCohomologyMap f r).hom x) =
      exteriorPower.map r (bettiCohomologyMap f 1).hom (cB.toEquiv.symm x) :=
    cA.toEquiv.symm_apply_eq.2 ((CupComparison.natural f cA cB _).symm ▸
      congrArg (bettiCohomologyMap f r).hom (cB.toEquiv.apply_symm_apply x).symm)
  rw [e, hodgeToDual_natural]
  exact map_dualMap_mem_hodgeExterior HA HB (bettiOneMap f) hf hx

/-- **The cup product of closed `1`-cochains is Hodge iff the wedge of the corresponding
functionals on `H₁` is Hodge.** -/
theorem bettiCupClass_mem_hodgeClassesBetti_iff (H : HodgeStructureNegOne (bettiOne A)) {r : ℕ}
    (c : CupComparison A r) (ψ : Fin r → Module.Dual ℚ ((singularChain.obj (space A)).X 1))
    (h : ∀ i, (dualMap ((singularChain.obj (space A)).d (1 + 1) 1)).hom (ψ i) = 0) :
    bettiCupClass A r ψ h ∈ hodgeClassesBetti H c ↔
      exteriorPower.ιMulti ℚ r (fun i => bettiUC A 1
        (cocycleClass (singularChain.obj (space A)) 1 (ψ i) (h i))) ∈ hodgeExterior H r := by
  have e1 : c.toEquiv.symm (bettiCupClass A r ψ h) = exteriorPower.ιMulti ℚ r (fun i =>
      cocycleClass (singularChain.obj (space A)) 1 (ψ i) (h i)) :=
    c.toEquiv.symm_apply_eq.2 (c.cup_ιMulti ψ h).symm
  have e2 : hodgeToDual A r (exteriorPower.ιMulti ℚ r (fun i =>
      cocycleClass (singularChain.obj (space A)) 1 (ψ i) (h i))) =
      exteriorPower.ιMulti ℚ r (fun i => bettiUC A 1
        (cocycleClass (singularChain.obj (space A)) 1 (ψ i) (h i))) :=
    exteriorPower.map_apply_ιMulti _ _
  refine (mem_hodgeClassesBetti H c).trans ?_
  rw [e1]
  exact Iff.of_eq (congrArg (fun y => y ∈ hodgeExterior H r) e2)

variable [GrpObj A]

/-- **The canonical Hodge classes** of the abelian variety `A`: the Hodge classes of the canonical
Hodge structure `D.canonicalHodge` on `H₁(A(ℂ), ℚ)` (complex structure of `Lie A` transported by
the uniformization). -/
def canonicalHodgeClasses (D : UniformizationData A) {r : ℕ} (c : CupComparison A r) :
    Submodule ℚ (bettiCohomology A r) :=
  hodgeClassesBetti D.canonicalHodge c

/-- The canonical Hodge classes do not depend on the uniformization data. -/
theorem canonicalHodgeClasses_eq (D D' : UniformizationData A) {r : ℕ} (c : CupComparison A r) :
    canonicalHodgeClasses D c = canonicalHodgeClasses D' c := by
  unfold canonicalHodgeClasses
  rw [UniformizationData.canonicalHodge_eq D D']

/-- **Canonical Hodge classes pull back along every homomorphism of abelian varieties.**
For `f : A ⟶ B` with `[IsMonHom f]`, `Hʳ(f)` maps the canonical Hodge classes of `B(ℂ)` into
those of `A(ℂ)`, for arbitrary cup-normalized comparisons: the canonical complex structure is
natural (`UniformizationData.J_map`) and the comparison is natural (`CupComparison.natural`). -/
theorem canonicalHodgeClasses_map {B : CSch} [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (DA : UniformizationData A) (DB : UniformizationData B) {r : ℕ} (cA : CupComparison A r)
    (cB : CupComparison B r) {x : bettiCohomology B r} (hx : x ∈ canonicalHodgeClasses DB cB) :
    (bettiCohomologyMap f r).hom x ∈ canonicalHodgeClasses DA cA :=
  map_mem_hodgeClassesBetti f DA.canonicalHodge DB.canonicalHodge
    (fun y => DA.J_map f DB y |>.symm ▸ rfl) cA cB hx

end Hodge

end ArithmeticOfJacobiPolynomials.AbelianHodgeClasses
