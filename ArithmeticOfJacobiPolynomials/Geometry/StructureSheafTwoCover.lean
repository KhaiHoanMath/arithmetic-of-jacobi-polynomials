/- Assembled by AxiomProver. -/
module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.Basic
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.Fibre

/-!
# `H¹` of a quasi-coherent module on a scheme covered by two affine opens

Let `π : Y ⟶ Spec k` be separated over a field and `Y = U ∪ V` a cover by two affine opens. Stacks
computes `H¹(Y, F)` of a quasi-coherent module as the cokernel of the degree-zero differential of
the alternating Čech complex (`Stacks.TwoAffineCech.cohomologyOneIso`), whose cochains are families
of sections indexed by tuples in `Stacks.TwoAffineCech.Cover = ULift (Fin 2)`. This file identifies
that cokernel with the cokernel of the restriction difference on the sections

`Γ(F, U) × Γ(F, V) ⟶ Γ(F, U ⊓ V)`,  `(a, b) ↦ a|_{U ⊓ V} - b|_{U ⊓ V}`,

by showing that an alternating `1`-cochain is determined by its `(0, 1)` component
(`altOneEquiv`, a `k`-linear equivalence to `Γ(F, U ⊓ V)`) and that, under it, the image of the
differential is the image of the restriction difference (`range_altOneEquiv_comp_cechD`).

## Main results

* `ArithmeticOfJacobiPolynomials.TwoCover.altOneEquiv`: alternating `1`-cochains `≃ₗ[k] Γ(F, U ⊓
V)`.
* `ArithmeticOfJacobiPolynomials.TwoCover.cechRestrictDifference`: the map `(a, b) ↦ a|_{U ⊓ V} -
b|_{U ⊓ V}`.
* `ArithmeticOfJacobiPolynomials.TwoCover.structureSheafCohomologyOneEquiv`: `H¹(Y, 𝒪_Y)`, the
group defining the
  genus (Stacks 0BY7), is `≃ₗ[k]` the cokernel of `cechRestrictDifference`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace TwoCover

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry CechCochains
  Stacks.TwoAffineCech Stacks.Cech

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (U V : Y.Opens)

/-- The cover `(U, V)` indexed by `Stacks.TwoAffineCech.Cover`. -/
@[expose]
def twoCover : Cover.{u} → Y.Opens := fun i => ![U, V] i.down

/-- The tuple `(0, 1)` of indices. -/
@[expose]
def ordPair : Fin 2 → Cover.{u} := fun j => ULift.up j

/-- The structure sheaf as a module over itself. -/
noncomputable abbrev structureModule (Y : Scheme.{u}) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

theorem eq_ordPair {i : Fin 2 → Cover.{u}} (hi : StrictMono i) : i = ordPair := by
  have h01 : (i 0).down < (i 1).down := hi (by decide : (0 : Fin 2) < 1)
  have key : ∀ a b : Fin 2, a < b → a = 0 ∧ b = 1 := by decide
  obtain ⟨h0, h1⟩ := key _ _ h01
  funext j
  fin_cases j
  · exact ULift.ext h0
  · exact ULift.ext h1

theorem strictMono_ordPair : StrictMono (ordPair : Fin 2 → Cover.{u}) := by
  intro a b h
  exact h

theorem inter_ordPair :
    inter (twoCover U V) (ordPair : Fin 2 → Cover.{u}) = U ⊓ V := by
  refine le_antisymm ?_ ?_
  · exact le_inf (iInf_le (fun j => twoCover U V (ordPair j)) 0)
      (iInf_le (fun j => twoCover U V (ordPair j)) 1)
  · exact le_iInf fun j => by
      fin_cases j
      · exact inf_le_left
      · exact inf_le_right

theorem iSup_twoCover : ⨆ i, twoCover U V i = U ⊔ V := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup (twoCover U V) ⟨0⟩)
    (le_iSup (twoCover U V) ⟨1⟩))
  obtain ⟨i⟩ := i
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem isAffineOpen_twoCover (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : Cover.{u}) :
    IsAffineOpen (twoCover U V i) := by
  obtain ⟨i⟩ := i
  fin_cases i
  · exact hU
  · exact hV

section Restriction

variable (F : Y.Modules)

theorem restr_self {W : Y.Opens} (x : Γ(F, W)) :
    restr F.presheaf (le_refl W) x = x := by
  have h : (homOfLE (le_refl W)).op = 𝟙 (op W) := rfl
  unfold restr
  rw [h]
  simp

theorem restr_smul {V' W : Y.Opens} (h : W ≤ V') (a : k) (x : Γ(F, V')) :
    restr F.presheaf h ((baseRingHom π V').hom a • x) =
      (baseRingHom π W).hom a • restr F.presheaf h x := by
  change (F.presheaf.map (homOfLE h).op).hom _ = _
  rw [Scheme.Modules.map_smul, map_baseRingHom_apply]
  try rfl

end Restriction

section Degree1

variable (F : Y.Modules)

/-- An alternating `1`-cochain is determined by its `(0, 1)` component: the map
`s ↦ -s(0, 1)|_{U ⊓ V}` to the sections over `U ⊓ V`. -/
@[expose]
noncomputable def altOneToSections :
    letI := cochainModule π (twoCover U V) F 1
    letI := sectionsModule π F (U ⊓ V)
    alternatingSubmodule π (twoCover U V) F 1 →ₗ[k] Γ(F, U ⊓ V) :=
  letI := cochainModule π (twoCover U V) F 1
  letI := sectionsModule π F (U ⊓ V)
  { toFun := fun s => -(restr F.presheaf (inter_ordPair U V).ge (s.1 ordPair))
    map_add' := fun s t => by
      change -(restr F.presheaf _ ((s.1 + t.1) ordPair)) = _
      rw [Cochain.add_apply, map_add, neg_add]
    map_smul' := fun a s => by
      have h := cochain_smul_apply π (twoCover U V) F 1 a s.1 ordPair
      change -(restr F.presheaf _ ((a • s.1) ordPair)) = a • -(restr F.presheaf _ (s.1 ordPair))
      rw [h, restr_smul, smul_neg]
      try rfl }

theorem altOneToSections_apply (s : alternatingSubmodule π (twoCover U V) F 1) :
    altOneToSections π U V F s =
      -(restr F.presheaf (inter_ordPair U V).ge (s.1 ordPair)) :=
  rfl

theorem altOneToSections_injective :
    letI := cochainModule π (twoCover U V) F 1
    letI := sectionsModule π F (U ⊓ V)
    Function.Injective (altOneToSections π U V F) := by
  let _ := cochainModule π (twoCover U V) F 1
  let _ := sectionsModule π F (U ⊓ V)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  rw [altOneToSections_apply, neg_eq_zero] at hs
  -- `s` is determined by its value at the unique strictly increasing tuple
  have hpi : pi (twoCover U V) F.presheaf 1 s.1 = 0 := by
    funext i
    obtain ⟨i, hi⟩ := i
    have := eq_ordPair hi
    subst this
    change s.1 ordPair = 0
    have h2 := congrArg (restr F.presheaf (inter_ordPair U V).le) hs
    rw [map_zero] at h2
    rw [restr_restr] at h2
    have h3 : restr F.presheaf (le_refl _) (s.1 ordPair) = s.1 ordPair := restr_self F _
    rw [← h3]
    exact h2
  apply Subtype.ext
  rw [← c_pi_of_isAlternating (twoCover U V) F.presheaf 1 s.1 s.2, hpi, map_zero]
  rfl

theorem altOneToSections_surjective :
    letI := cochainModule π (twoCover U V) F 1
    letI := sectionsModule π F (U ⊓ V)
    Function.Surjective (altOneToSections π U V F) := by
  let _ := cochainModule π (twoCover U V) F 1
  let _ := sectionsModule π F (U ⊓ V)
  intro t
  let o : OrdCochain (twoCover U V) F.presheaf 1 := fun i =>
    -(restr F.presheaf (by rw [eq_ordPair i.2]; exact (inter_ordPair U V).le) t)
  refine ⟨⟨c (twoCover U V) F.presheaf 1 o, c_isAlternating _ _ 1 o⟩, ?_⟩
  rw [altOneToSections_apply]
  have h1 : (c (twoCover U V) F.presheaf 1 o) ordPair = o ⟨ordPair, strictMono_ordPair⟩ :=
    congrFun (pi_c (twoCover U V) F.presheaf 1 o) ⟨ordPair, strictMono_ordPair⟩
  change -(restr F.presheaf _ ((c (twoCover U V) F.presheaf 1 o) ordPair)) = t
  rw [h1]
  change -(restr F.presheaf _ (-(restr F.presheaf _ t))) = t
  rw [map_neg, neg_neg, restr_restr]
  exact restr_self F t

/-- **Alternating `1`-cochains of the two-element cover are the sections over `U ⊓ V`.** -/
@[expose]
noncomputable def altOneEquiv :
    letI := cochainModule π (twoCover U V) F 1
    letI := sectionsModule π F (U ⊓ V)
    alternatingSubmodule π (twoCover U V) F 1 ≃ₗ[k] Γ(F, U ⊓ V) :=
  letI := cochainModule π (twoCover U V) F 1
  letI := sectionsModule π F (U ⊓ V)
  LinearEquiv.ofBijective (altOneToSections π U V F)
    ⟨altOneToSections_injective π U V F, altOneToSections_surjective π U V F⟩

/-- Restriction `Γ(F, V') → Γ(F, W)` along `W ≤ V'` as a `k`-linear map. -/
@[expose]
noncomputable def restrLinear {V' W : Y.Opens} (h : W ≤ V') :
    letI := sectionsModule π F V'
    letI := sectionsModule π F W
    Γ(F, V') →ₗ[k] Γ(F, W) :=
  letI := sectionsModule π F V'
  letI := sectionsModule π F W
  { toFun := restr F.presheaf h
    map_add' := map_add _
    map_smul' := fun a x => restr_smul π F h a x }

/-- **The Čech differential of the sections**: `(a, b) ↦ a|_{U ⊓ V} - b|_{U ⊓ V}`. -/
@[expose]
noncomputable def cechRestrictDifference :
    letI := sectionsModule π F U
    letI := sectionsModule π F V
    letI := sectionsModule π F (U ⊓ V)
    (Γ(F, U) × Γ(F, V)) →ₗ[k] Γ(F, U ⊓ V) :=
  letI := sectionsModule π F U
  letI := sectionsModule π F V
  letI := sectionsModule π F (U ⊓ V)
  restrLinear π F (inf_le_left : U ⊓ V ≤ U) ∘ₗ LinearMap.fst k _ _ -
    restrLinear π F (inf_le_right : U ⊓ V ≤ V) ∘ₗ LinearMap.snd k _ _

theorem cechRestrictDifference_apply (a : Γ(F, U)) (b : Γ(F, V)) :
    letI := sectionsModule π F U
    letI := sectionsModule π F V
    letI := sectionsModule π F (U ⊓ V)
    cechRestrictDifference π U V F (a, b) =
      restr F.presheaf (inf_le_left : U ⊓ V ≤ U) a -
        restr F.presheaf (inf_le_right : U ⊓ V ≤ V) b :=
  rfl

/-- The degree-zero differential of the alternating Čech complex, evaluated at the tuple `(0, 1)`
and read in the sections over `U ⊓ V`, is `s(τ₁)|_{U ⊓ V} - s(τ₀)|_{U ⊓ V}` for the two
one-element tuples `τ_j` omitting position `j`. -/
theorem altOneEquiv_cechD
    (s : (alternatingCechModuleComplex π (twoCover U V) F).X 0) :
    altOneEquiv π U V F (cechD π (twoCover U V) F s) =
      restr F.presheaf
        ((inter_ordPair U V).ge.trans (inter_le_omit (twoCover U V) ordPair 1))
        (s.1 (ordPair ∘ Fin.succAbove 1)) -
      restr F.presheaf
        ((inter_ordPair U V).ge.trans (inter_le_omit (twoCover U V) ordPair 0))
        (s.1 (ordPair ∘ Fin.succAbove 0)) := by
  change -(restr F.presheaf _
    ((CechCochains.cechD (twoCover U V) F.presheaf 0 s.1) ordPair)) = _
  have h : (CechCochains.cechD (twoCover U V) F.presheaf 0 s.1) ordPair =
      ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) •
        restr F.presheaf (inter_le_omit (twoCover U V) ordPair j)
          (s.1 (ordPair ∘ j.succAbove)) := rfl
  rw [h, Fin.sum_univ_two, map_add, map_zsmul, map_zsmul, restr_restr, restr_restr]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, neg_add_rev,
    neg_neg]
  abel

/-- The degree-zero cochain with values `a` on `U` and `b` on `V`. -/
@[expose]
noncomputable def pairSec (a : Γ(F, U)) (b : Γ(F, V)) :
    (i : Cover.{u}) → Γ(F, twoCover U V i)
  | ⟨⟨0, _⟩⟩ => a
  | ⟨⟨1, _⟩⟩ => b
  | ⟨⟨n + 2, h⟩⟩ => absurd h (by omega)

/-- The degree-zero cochain `i ↦ pairSec (i 0)|_{U_i}`. -/
@[expose]
noncomputable def pairCochain (a : Γ(F, U)) (b : Γ(F, V)) :
    CechCochains.Cochain (twoCover U V) F.presheaf 0 :=
  fun i => restr F.presheaf (iInf_le (fun j => twoCover U V (i j)) 0) (pairSec U V F a b (i 0))

theorem isAlternating_pairCochain (a : Γ(F, U)) (b : Γ(F, V)) :
    IsAlternating (twoCover U V) F.presheaf (pairCochain U V F a b) :=
  have hsub : ∀ x y : Fin (0 + 1), x = y := fun x y =>
    Fin.ext (by have := x.isLt; have := y.isLt; omega)
  ⟨fun _ hi => absurd (fun x y _ => hsub x y) hi, fun _ x y hxy => absurd (hsub x y) hxy⟩

theorem le_inter_tau1 : U ≤ inter (twoCover U V) (ordPair ∘ Fin.succAbove (1 : Fin 2)) :=
  le_iInf fun j => by
    fin_cases j
    exact le_rfl

theorem le_inter_tau0 : V ≤ inter (twoCover U V) (ordPair ∘ Fin.succAbove (0 : Fin 2)) :=
  le_iInf fun j => by
    fin_cases j
    exact le_rfl

theorem pairCochain_apply_tau1 (a : Γ(F, U)) (b : Γ(F, V)) :
    pairCochain U V F a b (ordPair ∘ Fin.succAbove 1) =
      restr F.presheaf (iInf_le (fun j => twoCover U V ((ordPair ∘ Fin.succAbove 1) j)) 0 :
        inter (twoCover U V) (ordPair ∘ Fin.succAbove 1) ≤ U) a :=
  rfl

theorem pairCochain_apply_tau0 (a : Γ(F, U)) (b : Γ(F, V)) :
    pairCochain U V F a b (ordPair ∘ Fin.succAbove 0) =
      restr F.presheaf (iInf_le (fun j => twoCover U V ((ordPair ∘ Fin.succAbove 0) j)) 0 :
        inter (twoCover U V) (ordPair ∘ Fin.succAbove 0) ≤ V) b :=
  rfl

/-- **The image of the Čech differential is the image of the restriction difference**, under
`altOneEquiv`. -/
theorem range_altOneEquiv_comp_cechD :
    letI := cochainModule π (twoCover U V) F 1
    letI := sectionsModule π F U
    letI := sectionsModule π F V
    letI := sectionsModule π F (U ⊓ V)
    LinearMap.range ((altOneEquiv π U V F).toLinearMap ∘ₗ cechD π (twoCover U V) F) =
      LinearMap.range (cechRestrictDifference π U V F) := by
  let _ := cochainModule π (twoCover U V) F 1
  let _ := sectionsModule π F U
  let _ := sectionsModule π F V
  let _ := sectionsModule π F (U ⊓ V)
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(restr F.presheaf (le_inter_tau1 U V) (s.1 _),
      restr F.presheaf (le_inter_tau0 U V) (s.1 _)), ?_⟩
    rw [cechRestrictDifference_apply, restr_restr, restr_restr]
    exact (altOneEquiv_cechD π U V F s).symm
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨⟨pairCochain U V F a b, isAlternating_pairCochain U V F a b⟩, ?_⟩
    refine (altOneEquiv_cechD π U V F _).trans ?_
    change restr F.presheaf _ (pairCochain U V F a b (ordPair ∘ Fin.succAbove 1)) -
      restr F.presheaf _ (pairCochain U V F a b (ordPair ∘ Fin.succAbove 0)) = _
    rw [pairCochain_apply_tau1, pairCochain_apply_tau0, cechRestrictDifference_apply]
    exact congrArg₂ (· - ·) (restr_restr F.presheaf _ _ a) (restr_restr F.presheaf _ _ b)

/-- The cokernel of the alternating Čech differential is the cokernel of the restriction
difference on sections. -/
@[expose]
noncomputable def cokernelEquiv :
    letI := cochainModule π (twoCover U V) F 1
    letI := sectionsModule π F U
    letI := sectionsModule π F V
    letI := sectionsModule π F (U ⊓ V)
    ((alternatingCechModuleComplex π (twoCover U V) F).X 1 ⧸
        LinearMap.range (cechD π (twoCover U V) F)) ≃ₗ[k]
      (Γ(F, U ⊓ V) ⧸ LinearMap.range (cechRestrictDifference π U V F)) :=
  letI := cochainModule π (twoCover U V) F 1
  letI := sectionsModule π F U
  letI := sectionsModule π F V
  letI := sectionsModule π F (U ⊓ V)
  Submodule.Quotient.equiv _ _ (altOneEquiv π U V F)
    ((LinearMap.range_comp (cechD π (twoCover U V) F) (altOneEquiv π U V F).toLinearMap).symm.trans
      (range_altOneEquiv_comp_cechD π U V F))

end Degree1

section StructureSheaf

open Stacks.Cohomology.TwoAffineCech in
/-- **`H¹(Y, 𝒪_Y)` (the group defining the genus, Stacks 0BY7) is the cokernel of the restriction
difference `Γ(U) × Γ(V) → Γ(U ⊓ V)`** for a cover `Y = U ∪ V` by two affine opens of a scheme
separated over a field, as a `k`-vector space. -/
@[expose]
noncomputable def structureSheafCohomologyOneEquiv [IsSeparated π] (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    letI := sectionsModule π (structureModule Y) U
    letI := sectionsModule π (structureModule Y) V
    letI := sectionsModule π (structureModule Y) (U ⊓ V)
    structureSheafCohomology π 1 ≃ₗ[k]
      (Γ(structureModule Y, U ⊓ V) ⧸
        LinearMap.range (cechRestrictDifference π U V (structureModule Y))) :=
  letI := cochainModule π (twoCover U V) (structureModule Y) 1
  letI := sectionsModule π (structureModule Y) U
  letI := sectionsModule π (structureModule Y) V
  letI := sectionsModule π (structureModule Y) (U ⊓ V)
  ((structureSheafCohomologyIsoCohomologyOverField k π 1 ≪≫
      eqToIso (cohomologyOverField_eq π (structureModule Y) 1) ≪≫
      cohomologyOneIso π (twoCover U V) (structureModule Y) ((iSup_twoCover U V).trans hUV).symm
        (isAffineOpen_twoCover U V hU hV)).toLinearEquiv).trans
    (cokernelEquiv π U V (structureModule Y))

end StructureSheaf

end TwoCover

end ArithmeticOfJacobiPolynomials
