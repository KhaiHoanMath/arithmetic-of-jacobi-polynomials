/- Assembled by AxiomProver. -/
module

public import Mathlib

/-!
# Rational Hodge structures of type `{(-1,0),(0,-1)}`, their tensor spaces and Hodge classes

This file builds the generic linear-algebra layer behind the Hodge and Mumford–Tate groups of a
polarized rational Hodge structure of weight `-1` (for an abelian variety `A`, the structure on
`V = H_1(A(ℂ), ℚ)`). Nothing about complex tori or Jacobians is asserted here.

## Conventions and references

* **Hodge structure** (Deligne, *Hodge cycles on abelian varieties*, LNM 900, §3; Mumford,
  *Abelian varieties*, §1 and §4; Moonen, *Notes on Mumford–Tate groups*, §1). A rational Hodge
  structure of type `{(-1,0),(0,-1)}` on a `ℚ`-vector space `V` is the same as a complex
  structure on `V_ℝ := ℝ ⊗[ℚ] V`, i.e. an `ℝ`-linear `J` with `J ∘ J = -1`
  (`HodgeStructureNegOne`). The Deligne torus acts through
  `h : ℂˣ → GL(V_ℝ)`, `h (a + b i) = a + b J` (`HodgeStructureNegOne.hodgeRep`); its restriction
  to the unit circle is `HodgeStructureNegOne.circleRep`.
* **Polarization** (`HodgeStructureNegOne.Polarization`): an alternating `ℚ`-bilinear form `ψ`
  on `V` whose real extension `ψ_ℝ` satisfies `ψ_ℝ (J x) (J y) = ψ_ℝ x y` and the positivity
  `ψ_ℝ x (J x) > 0` for `x ≠ 0`. This is the convention "`ψ(x, C y)` is symmetric positive
  definite", `C = h(i) = J` the Weil operator; other references use `ψ(J x, x) > 0`, which
  amounts to replacing `J` by `-J` (or `ψ` by `-ψ`). For `H₁` of a complex abelian variety the
  classical Riemann form `E_L` of an ample `L` satisfies `E_L (J x) x > 0` (Milne), so the
  polarization of this convention attached to `L` is `-E_L`
  (`AbelianBettiHodge.PolarizationForm`). The positivity is not used for the
  inclusions of `ArithmeticOfJacobiPolynomials.Algebra.HodgeGroup`, which only use the
  `J`-invariance.
* **Tensor spaces** `TensorSpace R M m n = M^{⊗m} ⊗ (M^*)^{⊗n}` (Mathlib's `TensorPower`), with
  `GL(M)` acting by `g` on the `M` factors and contragrediently, `φ ↦ φ ∘ g⁻¹`, on the dual
  factors (`tensorMap`, `tensorRep`).
* **Hodge classes** (`HodgeStructureNegOne.hodgeClasses`): `t ∈ T m n` whose image
  `realify m n t` in the real tensor space `TensorSpace ℝ V_ℝ m n` is fixed by every `h(z)`,
  `|z| = 1`. Here `realify` sends `v₁ ⊗ ⋯ ⊗ φ₁ ⊗ ⋯` to `(1 ⊗ v₁) ⊗ ⋯ ⊗ φ₁_ℝ ⊗ ⋯`; for
  finite-dimensional `V` it is the canonical map `T m n → ℝ ⊗ T m n ≅ (V_ℝ)^{⊗m} ⊗ (V_ℝ^*)^{⊗n}`
  (the identification itself is not needed and not formalized). Since `V` has weight `-1`,
  `T m n` has weight `n - m`, and a circle-fixed vector has type `(p, p)` with `2 p = n - m`:
  it is a Hodge class of `T m n ⊗ ℚ(p)` in Deligne's sense (type `(0,0)` after the Tate twist),
  which we call a Hodge class *of twist `p`*. (The circle acts trivially on `ℚ(p)`, so the twist
  does not enter the invariance condition.)

## Main results

* `HodgeStructureNegOne.hEnd_mul`: `h(z w) = h(z) h(w)`;
* `HodgeStructureNegOne.Polarization.baseChange_J_left`: `ψ_ℝ (J x) y = - ψ_ℝ x (J y)`;
* `HodgeStructureNegOne.Polarization.baseChange_circleRep`: the circle preserves `ψ_ℝ`;
* `bilinTensor ψ ∈ T 0 2`, the tensor of a bilinear form (`dualSqEval_bilinDualTensor`,
  basis-independent by `bilinDualTensor_eq`), and
  `HodgeStructureNegOne.Polarization.bilinTensor_mem_hodgeClasses`: a polarization is a Hodge
  class (of twist `1`, as `2 - 0 = 2 · 1`);
* `bilin_eq_smul_of_tensorMap_bilinTensor`: if `g • ψ = c • ψ` in `T 0 2` then
  `ψ x y = c * ψ (g x) (g y)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open TensorProduct

section TensorSpace

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The tensor space `T m n = M^{⊗m} ⊗ (M^*)^{⊗n}`. -/
abbrev TensorSpace (m n : ℕ) : Type _ :=
  TensorPower R m M ⊗[R] TensorPower R n (Module.Dual R M)

/-- The empty tensor `1 ∈ M^{⊗0}`. -/
@[expose]
noncomputable def unitTensor : TensorPower R 0 M :=
  PiTensorProduct.tprod R fun i => Fin.elim0 i

variable {R M}

/-- Every pure tensor of an empty family is `unitTensor`. -/
theorem tprod_fin_zero (φ : Fin 0 → M) : PiTensorProduct.tprod R φ = unitTensor R M :=
  congrArg (fun ψ : Fin 0 → M => PiTensorProduct.tprod R ψ) (Subsingleton.elim _ _)

/-- Any induced map on `M^{⊗0}` fixes `unitTensor`. -/
theorem map_unitTensor {N : Type*} [AddCommGroup N] [Module R N] (f : Fin 0 → M →ₗ[R] N) :
    PiTensorProduct.map f (unitTensor R M) = unitTensor R N := by
  rw [unitTensor, PiTensorProduct.map_tprod, tprod_fin_zero]

/-- **The action of `GL(M)` on `T m n`**: `g` acts on the `M` factors and by the contragredient
`φ ↦ φ ∘ g⁻¹` on the dual factors. -/
@[expose]
noncomputable def tensorMap (m n : ℕ) (g : M ≃ₗ[R] M) : Module.End R (TensorSpace R M m n) :=
  TensorProduct.map (PiTensorProduct.map fun _ : Fin m => (g : M →ₗ[R] M))
    (PiTensorProduct.map fun _ : Fin n =>
      (g.symm.dualMap : Module.Dual R M →ₗ[R] Module.Dual R M))

/-- `tensorMap` on pure tensors `a ⊗ b`. -/
theorem tensorMap_tmul (m n : ℕ) (g : M ≃ₗ[R] M) (a : TensorPower R m M)
    (b : TensorPower R n (Module.Dual R M)) :
    tensorMap m n g (a ⊗ₜ b) = PiTensorProduct.map (fun _ : Fin m => (g : M →ₗ[R] M)) a ⊗ₜ
      PiTensorProduct.map (fun _ : Fin n =>
        (g.symm.dualMap : Module.Dual R M →ₗ[R] Module.Dual R M)) b :=
  rfl

/-- The identity acts trivially. -/
theorem tensorMap_one (m n : ℕ) : tensorMap (R := R) (M := M) m n 1 = 1 := by
  have h1 : ((1 : M ≃ₗ[R] M) : M →ₗ[R] M) = 1 := LinearMap.ext fun _ => rfl
  have h2 : (((1 : M ≃ₗ[R] M).symm.dualMap : Module.Dual R M ≃ₗ[R] Module.Dual R M) :
      Module.Dual R M →ₗ[R] Module.Dual R M) = 1 :=
    LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  simp only [tensorMap, h1, h2, PiTensorProduct.map_one, TensorProduct.map_one]

/-- The action is multiplicative. -/
theorem tensorMap_mul (m n : ℕ) (g h : M ≃ₗ[R] M) :
    tensorMap m n (g * h) = tensorMap m n g * tensorMap m n h := by
  have h1 : ((g * h : M ≃ₗ[R] M) : M →ₗ[R] M) = (g : M →ₗ[R] M) * (h : M →ₗ[R] M) :=
    LinearMap.ext fun _ => rfl
  have h2 : (((g * h).symm.dualMap : Module.Dual R M ≃ₗ[R] Module.Dual R M) :
      Module.Dual R M →ₗ[R] Module.Dual R M) =
      (g.symm.dualMap : Module.Dual R M →ₗ[R] Module.Dual R M) *
        (h.symm.dualMap : Module.Dual R M →ₗ[R] Module.Dual R M) :=
    LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  simp only [tensorMap, h1, h2, PiTensorProduct.map_mul, TensorProduct.map_mul]

/-- **The tensor representation** `GL(M) →* End(T m n)`. -/
@[expose]
noncomputable def tensorRep (m n : ℕ) : (M ≃ₗ[R] M) →* Module.End R (TensorSpace R M m n) where
  toFun := tensorMap m n
  map_one' := tensorMap_one m n
  map_mul' := tensorMap_mul m n

/-- `tensorRep` is `tensorMap`. -/
theorem tensorRep_apply (m n : ℕ) (g : M ≃ₗ[R] M) : tensorRep m n g = tensorMap m n g :=
  rfl

/-- `(g h) • t = g • (h • t)`. -/
theorem tensorMap_mul_apply (m n : ℕ) (g h : M ≃ₗ[R] M) (t : TensorSpace R M m n) :
    tensorMap m n (g * h) t = tensorMap m n g (tensorMap m n h t) := by
  rw [tensorMap_mul, Module.End.mul_apply]

/-- `1 • t = t`. -/
theorem tensorMap_one_apply (m n : ℕ) (t : TensorSpace R M m n) :
    tensorMap m n (1 : M ≃ₗ[R] M) t = t := by
  rw [tensorMap_one, Module.End.one_apply]

/-- `g⁻¹ • (g • t) = t`. -/
theorem tensorMap_inv_apply_self (m n : ℕ) (g : M ≃ₗ[R] M) (t : TensorSpace R M m n) :
    tensorMap m n g⁻¹ (tensorMap m n g t) = t := by
  rw [← tensorMap_mul_apply, inv_mul_cancel, tensorMap_one_apply]

/-- The action on `T 0 n` of a tensor `1 ⊗ c`. -/
theorem tensorMap_unit_tmul (n : ℕ) (g : M ≃ₗ[R] M) (c : TensorPower R n (Module.Dual R M)) :
    tensorMap 0 n g (unitTensor R M ⊗ₜ c) = unitTensor R M ⊗ₜ PiTensorProduct.map
      (fun _ : Fin n => (g.symm.dualMap : Module.Dual R M →ₗ[R] Module.Dual R M)) c := by
  rw [tensorMap_tmul, map_unitTensor]

/-- The isomorphism `T 0 n = M^{⊗0} ⊗ (M^*)^{⊗n} → (M^*)^{⊗n}` (as a linear map). -/
@[expose]
noncomputable def dropUnit (n : ℕ) :
    TensorSpace R M 0 n →ₗ[R] TensorPower R n (Module.Dual R M) :=
  (TensorProduct.lid R (TensorPower R n (Module.Dual R M))).toLinearMap ∘ₗ
    TensorProduct.map (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap LinearMap.id

/-- `dropUnit (1 ⊗ c) = c`. -/
theorem dropUnit_tmul (n : ℕ) (c : TensorPower R n (Module.Dual R M)) :
    dropUnit n (unitTensor R M ⊗ₜ c) = c := by
  simp only [dropUnit, unitTensor, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, PiTensorProduct.isEmptyEquiv_apply_tprod, LinearMap.id_apply,
    TensorProduct.lid_tmul, one_smul]

end TensorSpace

section DualSquare

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Evaluation of a tensor in `(M^*)^{⊗2}` at a pair `(x, y)`:
`φ₀ ⊗ φ₁ ↦ φ₀ x * φ₁ y`. -/
@[expose]
noncomputable def dualSqEval (x y : M) : TensorPower K 2 (Module.Dual K M) →ₗ[K] K :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K (Fin 2) K).compLinearMap
    fun i => Module.Dual.eval K M (![x, y] i))

/-- `dualSqEval` on pure tensors. -/
theorem dualSqEval_tprod (x y : M) (φ : Fin 2 → Module.Dual K M) :
    dualSqEval x y (PiTensorProduct.tprod K φ) = φ 0 x * φ 1 y := by
  simp [dualSqEval, Fin.prod_univ_two]

/-- `dualSqEval` on `φ ⊗ ψ`. -/
theorem dualSqEval_tprod_pair (x y : M) (f g : Module.Dual K M) :
    dualSqEval x y (PiTensorProduct.tprod K ![f, g]) = f x * g y := by
  rw [dualSqEval_tprod]
  rfl

/-- The action of `A` on `(M^*)^{⊗2}` transported through `dualSqEval`. -/
theorem dualSqEval_map (A : M ≃ₗ[K] M) (x y : M) (t : TensorPower K 2 (Module.Dual K M)) :
    dualSqEval x y (PiTensorProduct.map
      (fun _ : Fin 2 => (A.symm.dualMap : Module.Dual K M →ₗ[K] Module.Dual K M)) t) =
      dualSqEval (A.symm x) (A.symm y) t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod _ _ =>
    simp only [map_smul, PiTensorProduct.map_tprod, dualSqEval_tprod, LinearEquiv.coe_coe,
      LinearEquiv.dualMap_apply]
  | add _ _ hs ht => simp only [map_add, hs, ht]

variable {ι : Type*}

/-- The coordinates of a tensor of `(M^*)^{⊗2}` in the product of dual bases are its values on
pairs of basis vectors. -/
theorem dualSqEval_basis [Finite ι] [DecidableEq ι] (b : Module.Basis ι K M)
    (t : TensorPower K 2 (Module.Dual K M)) (p : Fin 2 → ι) :
    dualSqEval (b (p 0)) (b (p 1)) t =
      (Basis.piTensorProduct fun _ : Fin 2 => b.dualBasis).repr t p := by
  have key : dualSqEval (b (p 0)) (b (p 1)) =
      (Basis.piTensorProduct fun _ : Fin 2 => b.dualBasis).coord p := by
    refine (Basis.piTensorProduct fun _ : Fin 2 => b.dualBasis).ext fun q => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [Basis.piTensorProduct_apply, dualSqEval_tprod, Module.Basis.dualBasis_apply_self]
    by_cases h : q = p
    · subst h
      simp
    · have h' : ¬ (p 0 = q 0 ∧ p 1 = q 1) := fun h01 =>
        h (funext (Fin.forall_fin_two.2 ⟨h01.1.symm, h01.2.symm⟩))
      rw [not_and_or] at h'
      rcases h' with h0 | h0 <;> simp [h, h0]
  rw [key, Module.Basis.coord_apply]

/-- A tensor of `(M^*)^{⊗2}` is determined by its values on pairs of basis vectors. -/
theorem eq_of_dualSqEval_basis [Finite ι] (b : Module.Basis ι K M)
    {t t' : TensorPower K 2 (Module.Dual K M)}
    (h : ∀ i j, dualSqEval (b i) (b j) t = dualSqEval (b i) (b j) t') : t = t' := by
  classical
  exact (Basis.piTensorProduct fun _ : Fin 2 => b.dualBasis).ext_elem fun p => by
    rw [← dualSqEval_basis, ← dualSqEval_basis]
    exact h (p 0) (p 1)

variable [Fintype ι] [DecidableEq ι]

/-- **The tensor of a bilinear form**: `β ↦ ∑ᵢ ∑ⱼ β(bᵢ, bⱼ) bᵢ^* ⊗ bⱼ^* ∈ (M^*)^{⊗2}`. -/
@[expose]
noncomputable def bilinDualTensor (b : Module.Basis ι K M) (β : LinearMap.BilinForm K M) :
    TensorPower K 2 (Module.Dual K M) :=
  ∑ i, ∑ j, β (b i) (b j) • PiTensorProduct.tprod K ![b.dualBasis i, b.dualBasis j]

/-- The tensor of `β` evaluates to `β`. -/
theorem dualSqEval_bilinDualTensor (b : Module.Basis ι K M) (β : LinearMap.BilinForm K M)
    (x y : M) : dualSqEval x y (bilinDualTensor b β) = β x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [bilinDualTensor, map_sum, map_smul, dualSqEval_tprod_pair,
    Module.Basis.dualBasis_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The tensor of a bilinear form does not depend on the basis. -/
theorem bilinDualTensor_eq {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis ι K M)
    (b' : Module.Basis κ K M) (β : LinearMap.BilinForm K M) :
    bilinDualTensor b β = bilinDualTensor b' β :=
  eq_of_dualSqEval_basis b fun _ _ => by
    rw [dualSqEval_bilinDualTensor, dualSqEval_bilinDualTensor]

/-- If `A` preserves `β`, the contragredient action of `A` fixes the tensor of `β`. -/
theorem map_dualMap_bilinDualTensor (b : Module.Basis ι K M) (β : LinearMap.BilinForm K M)
    (A : M ≃ₗ[K] M) (hA : ∀ x y, β (A x) (A y) = β x y) :
    PiTensorProduct.map (fun _ : Fin 2 =>
      (A.symm.dualMap : Module.Dual K M →ₗ[K] Module.Dual K M)) (bilinDualTensor b β) =
      bilinDualTensor b β := by
  refine eq_of_dualSqEval_basis b fun i j => ?_
  rw [dualSqEval_map, dualSqEval_bilinDualTensor, dualSqEval_bilinDualTensor]
  have h := hA (A.symm (b i)) (A.symm (b j))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- If the contragredient action of `A` multiplies the tensor of `β` by `c`, then
`β x y = c * β (A x) (A y)`. -/
theorem bilin_eq_smul_of_map_dualMap (b : Module.Basis ι K M) (β : LinearMap.BilinForm K M)
    (A : M ≃ₗ[K] M) (c : K)
    (h : PiTensorProduct.map (fun _ : Fin 2 =>
      (A.symm.dualMap : Module.Dual K M →ₗ[K] Module.Dual K M)) (bilinDualTensor b β) =
      c • bilinDualTensor b β) (x y : M) :
    β x y = c * β (A x) (A y) := by
  have h' := congrArg (dualSqEval (A x) (A y)) h
  rwa [dualSqEval_map, map_smul, dualSqEval_bilinDualTensor, dualSqEval_bilinDualTensor,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, smul_eq_mul] at h'

end DualSquare

section BilinTensor

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **A bilinear form as an element of `T 0 2`**: `1 ⊗ ∑ β(bᵢ, bⱼ) bᵢ^* ⊗ bⱼ^*` for the basis
`Module.finBasis K M` (the choice is irrelevant by `bilinDualTensor_eq`). -/
@[expose]
noncomputable def bilinTensor (β : LinearMap.BilinForm K M) : TensorSpace K M 0 2 :=
  unitTensor K M ⊗ₜ bilinDualTensor (Module.finBasis K M) β

/-- **From `g • β = c • β` in `T 0 2` to the bilinear form**: `β x y = c * β (g x) (g y)`. -/
theorem bilin_eq_smul_of_tensorMap_bilinTensor (β : LinearMap.BilinForm K M) (g : M ≃ₗ[K] M)
    (c : K) (h : tensorMap 0 2 g (bilinTensor β) = c • bilinTensor β) (x y : M) :
    β x y = c * β (g x) (g y) := by
  rw [bilinTensor, tensorMap_unit_tmul, ← TensorProduct.tmul_smul] at h
  have h2 := congrArg (dropUnit 2) h
  rw [dropUnit_tmul, dropUnit_tmul] at h2
  exact bilin_eq_smul_of_map_dualMap _ β g c h2 x y

end BilinTensor

section Realification

/-- The `ℚ`-linear map `X^{⊗k} → Y^{⊗_ℝ k}` induced by a `ℚ`-linear map `f : X → Y` into a real
vector space. -/
@[expose]
noncomputable def realifyPow (k : ℕ) {X Y : Type*} [AddCommGroup X] [Module ℚ X]
    [AddCommGroup Y] [Module ℝ Y] [Module ℚ Y] [IsScalarTower ℚ ℝ Y] (f : X →ₗ[ℚ] Y) :
    TensorPower ℚ k X →ₗ[ℚ] TensorPower ℝ k Y :=
  PiTensorProduct.lift
    (((PiTensorProduct.tprod ℝ : MultilinearMap ℝ (fun _ : Fin k => Y)
      (TensorPower ℝ k Y)).restrictScalars ℚ).compLinearMap fun _ => f)

section

variable {k : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℝ Y]
  [Module ℚ Y] [IsScalarTower ℚ ℝ Y] (f : X →ₗ[ℚ] Y)

/-- `realifyPow` on pure tensors. -/
theorem realifyPow_tprod (φ : Fin k → X) :
    realifyPow k f (PiTensorProduct.tprod ℚ φ) = PiTensorProduct.tprod ℝ fun i => f (φ i) := by
  rw [realifyPow, PiTensorProduct.lift.tprod]
  rfl

/-- `realifyPow` on `a ⊗ b`. -/
theorem realifyPow_tprod_pair (a b : X) :
    realifyPow 2 f (PiTensorProduct.tprod ℚ ![a, b]) = PiTensorProduct.tprod ℝ ![f a, f b] := by
  rw [realifyPow_tprod]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `realifyPow` preserves the empty tensor. -/
theorem realifyPow_unitTensor : realifyPow 0 f (unitTensor ℚ X) = unitTensor ℝ Y := by
  rw [unitTensor, realifyPow_tprod, tprod_fin_zero]

end

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The base change of linear forms `V^* → (V_ℝ)^*`, `φ ↦ φ_ℝ`. -/
@[expose]
noncomputable def dualBaseChange : Module.Dual ℚ V →ₗ[ℚ] Module.Dual ℝ (ℝ ⊗[ℚ] V) :=
  Module.Dual.baseChange (R := ℚ) (A := ℝ) (V := V)

/-- `φ_ℝ (a ⊗ v) = φ(v) • a`. -/
theorem dualBaseChange_tmul (φ : Module.Dual ℚ V) (a : ℝ) (v : V) :
    dualBaseChange φ (a ⊗ₜ v) = φ v • a :=
  rfl

/-- The base change of the dual basis is the dual basis of the base-changed basis. -/
theorem dualBaseChange_dualBasis {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ V) (i : ι) :
    dualBaseChange (b.dualBasis i) = (Algebra.TensorProduct.basis ℝ b).dualBasis i := by
  refine (Algebra.TensorProduct.basis ℝ b).ext fun k => ?_
  rw [Module.Basis.dualBasis_apply_self, Algebra.TensorProduct.basis_apply, dualBaseChange_tmul,
    Module.Basis.dualBasis_apply_self]
  split_ifs <;> simp

/-- **Realification of tensors** `T m n → T_ℝ m n`,
`v₁ ⊗ ⋯ ⊗ φ₁ ⊗ ⋯ ↦ (1 ⊗ v₁) ⊗ ⋯ ⊗ φ₁_ℝ ⊗ ⋯`. -/
@[expose]
noncomputable def realify (m n : ℕ) :
    TensorSpace ℚ V m n →ₗ[ℚ] TensorSpace ℝ (ℝ ⊗[ℚ] V) m n :=
  TensorProduct.lift (LinearMap.mk₂ ℚ
    (fun a b => realifyPow m (TensorProduct.mk ℚ ℝ V 1) a ⊗ₜ[ℝ] realifyPow n dualBaseChange b)
    (fun _ _ _ => by rw [map_add, TensorProduct.add_tmul])
    (fun _ _ _ => by rw [map_smul, TensorProduct.smul_tmul'])
    (fun _ _ _ => by rw [map_add, TensorProduct.tmul_add])
    (fun _ _ _ => by rw [map_smul, TensorProduct.tmul_smul]))

/-- `realify` on pure tensors. -/
theorem realify_tmul (m n : ℕ) (a : TensorPower ℚ m V) (b : TensorPower ℚ n (Module.Dual ℚ V)) :
    realify m n (a ⊗ₜ b) =
      realifyPow m (TensorProduct.mk ℚ ℝ V 1) a ⊗ₜ realifyPow n dualBaseChange b := by
  rw [realify, TensorProduct.lift.tmul, LinearMap.mk₂_apply]

/-- The realification of the tensor of `β` is the tensor of `β_ℝ`. -/
theorem realifyPow_bilinDualTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ V) (β : LinearMap.BilinForm ℚ V) :
    realifyPow 2 dualBaseChange (bilinDualTensor b β) =
      bilinDualTensor (Algebra.TensorProduct.basis ℝ b) (β.baseChange ℝ) := by
  simp only [bilinDualTensor, map_sum, map_smul, realifyPow_tprod_pair, dualBaseChange_dualBasis,
    Algebra.TensorProduct.basis_apply, LinearMap.BilinForm.baseChange_tmul, mul_one,
    smul_one_smul]

/-- The realification of `bilinTensor β`. -/
theorem realify_bilinTensor [FiniteDimensional ℚ V] (β : LinearMap.BilinForm ℚ V) :
    realify 0 2 (bilinTensor β) = unitTensor ℝ (ℝ ⊗[ℚ] V) ⊗ₜ
      bilinDualTensor (Algebra.TensorProduct.basis ℝ (Module.finBasis ℚ V)) (β.baseChange ℝ) := by
  rw [bilinTensor, realify_tmul, realifyPow_unitTensor, realifyPow_bilinDualTensor]

end Realification

/-- **A rational Hodge structure of type `{(-1,0),(0,-1)}`** on the `ℚ`-vector space `V`: a
complex structure `J` (`J ∘ J = -1`) on `V_ℝ = ℝ ⊗[ℚ] V`. -/
structure HodgeStructureNegOne (V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The complex structure `J = h(i)` on `V_ℝ`. -/
  J : Module.End ℝ (ℝ ⊗[ℚ] V)
  /-- `J ∘ J = -1`. -/
  J_mul_J : J * J = -1

namespace HodgeStructureNegOne

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (H : HodgeStructureNegOne V)

/-- `J (J x) = -x`. -/
theorem J_apply_J (x : ℝ ⊗[ℚ] V) : H.J (H.J x) = -x := by
  simpa using LinearMap.congr_fun H.J_mul_J x

/-- `h(z) = Re z + Im z · J` as an endomorphism of `V_ℝ`, for any `z : ℂ`. -/
@[expose]
noncomputable def hEnd (z : ℂ) : Module.End ℝ (ℝ ⊗[ℚ] V) :=
  z.re • 1 + z.im • H.J

/-- `h(z) x = Re z • x + Im z • J x`. -/
theorem hEnd_apply (z : ℂ) (x : ℝ ⊗[ℚ] V) : H.hEnd z x = z.re • x + z.im • H.J x :=
  rfl

/-- `h(z w) = h(z) h(w)`. -/
theorem hEnd_mul (z w : ℂ) : H.hEnd (z * w) = H.hEnd z * H.hEnd w := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, hEnd_apply, map_add, map_smul, J_apply_J, Complex.mul_re,
    Complex.mul_im]
  module

/-- `h` as a monoid homomorphism `ℂ →* End(V_ℝ)`. -/
@[expose]
noncomputable def hodgeMonoidHom : ℂ →* Module.End ℝ (ℝ ⊗[ℚ] V) where
  toFun := H.hEnd
  map_one' := LinearMap.ext fun x => by simp [hEnd_apply]
  map_mul' := H.hEnd_mul

/-- **The Hodge representation** `h : ℂˣ →* GL(V_ℝ)`, `h(a + b i) = a + b J`. -/
@[expose]
noncomputable def hodgeRep : ℂˣ →* ((ℝ ⊗[ℚ] V) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (ℝ ⊗[ℚ] V)).toMonoidHom.comp
    (Units.map H.hodgeMonoidHom)

/-- `h(z) x = Re z • x + Im z • J x`. -/
theorem hodgeRep_apply (z : ℂˣ) (x : ℝ ⊗[ℚ] V) :
    H.hodgeRep z x = (z : ℂ).re • x + (z : ℂ).im • H.J x :=
  rfl

/-- **The circle action** `h|U(1) : U(1) →* GL(V_ℝ)`. -/
@[expose]
noncomputable def circleRep : Circle →* ((ℝ ⊗[ℚ] V) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V)) :=
  H.hodgeRep.comp Circle.toUnits

/-- `h(z) x = Re z • x + Im z • J x` for `|z| = 1`. -/
theorem circleRep_apply (z : Circle) (x : ℝ ⊗[ℚ] V) :
    H.circleRep z x = (z : ℂ).re • x + (z : ℂ).im • H.J x :=
  rfl

/-- **Hodge classes** in `T m n = V^{⊗m} ⊗ (V^*)^{⊗n}`: the tensors whose realification is fixed
by `h(z)` for every `z` with `|z| = 1` (the circle-invariant tensors, i.e. those of type `(p,p)`
with `2 p = n - m`). They form a `ℚ`-subspace. -/
@[expose]
def hodgeClasses (m n : ℕ) : Submodule ℚ (TensorSpace ℚ V m n) where
  carrier := {t | ∀ z : Circle, tensorMap m n (H.circleRep z) (realify m n t) = realify m n t}
  add_mem' := by
    intro _ _ hs ht z
    rw [map_add, map_add, hs z, ht z]
  zero_mem' := by
    intro z
    rw [map_zero, map_zero]
  smul_mem' := by
    intro c t ht z
    rw [map_smul]
    exact ((tensorMap m n (H.circleRep z)).map_smul_of_tower c (realify m n t)).trans
      (congrArg (fun s => c • s) (ht z))

/-- Membership in `hodgeClasses`. -/
theorem mem_hodgeClasses {m n : ℕ} {t : TensorSpace ℚ V m n} :
    t ∈ H.hodgeClasses m n ↔
      ∀ z : Circle, tensorMap m n (H.circleRep z) (realify m n t) = realify m n t :=
  Iff.rfl

/-- **A polarization** of `H`: an alternating `ℚ`-bilinear form `ψ` with
`ψ_ℝ (J x) (J y) = ψ_ℝ x y` and `ψ_ℝ x (J x) > 0` for `x ≠ 0` (see the module docstring for the
sign convention). -/
structure Polarization where
  /-- The form `ψ`. -/
  form : LinearMap.BilinForm ℚ V
  /-- `ψ` is alternating. -/
  form_self : ∀ x, form x x = 0
  /-- `ψ_ℝ` is `J`-invariant. -/
  baseChange_J : ∀ x y, form.baseChange ℝ (H.J x) (H.J y) = form.baseChange ℝ x y
  /-- Positivity: `ψ_ℝ x (J x) > 0` for `x ≠ 0`. -/
  pos : ∀ x : ℝ ⊗[ℚ] V, x ≠ 0 → 0 < form.baseChange ℝ x (H.J x)

namespace Polarization

variable {H} (P : H.Polarization)

/-- **`ψ_ℝ (J x) y = - ψ_ℝ x (J y)`**, from `J`-invariance and `J² = -1`. -/
theorem baseChange_J_left (x y : ℝ ⊗[ℚ] V) :
    P.form.baseChange ℝ (H.J x) y = -P.form.baseChange ℝ x (H.J y) := by
  have h := P.baseChange_J (H.J x) y
  rw [H.J_apply_J, map_neg, LinearMap.neg_apply] at h
  exact h.symm

/-- **The circle preserves `ψ_ℝ`**: `ψ_ℝ (h(z) x) (h(z) y) = ψ_ℝ x y` for `|z| = 1`. -/
theorem baseChange_circleRep (z : Circle) (x y : ℝ ⊗[ℚ] V) :
    P.form.baseChange ℝ (H.circleRep z x) (H.circleRep z y) = P.form.baseChange ℝ x y := by
  have hz : (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im = 1 := by
    rw [← Complex.normSq_apply]
    exact Circle.normSq_coe z
  rw [circleRep_apply, circleRep_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    P.baseChange_J, P.baseChange_J_left]
  linear_combination (P.form.baseChange ℝ x y) * hz

/-- **A polarization is a Hodge class** (of twist `1`) in `T 0 2`. -/
theorem bilinTensor_mem_hodgeClasses [FiniteDimensional ℚ V] :
    bilinTensor P.form ∈ H.hodgeClasses 0 2 := by
  refine H.mem_hodgeClasses.2 fun z => ?_
  rw [realify_bilinTensor, tensorMap_unit_tmul,
    map_dualMap_bilinDualTensor _ _ _ (P.baseChange_circleRep z)]

end Polarization

end HodgeStructureNegOne

end ArithmeticOfJacobiPolynomials
