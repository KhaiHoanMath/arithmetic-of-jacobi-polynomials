/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.HodgeGroup

/-!
# Hodge and Mumford–Tate groups of powers of a Hodge structure are diagonal

For a rational Hodge structure `H` of type `{(-1,0),(0,-1)}` on `V`
(`ArithmeticOfJacobiPolynomials.HodgeStructureNegOne`) and a finite index type `ι`, we build the
Hodge structure
`H.pi ι` on `ι → V` (the direct sum `V^ι`; `H.pow h = H.pi (Fin h)` is `V^h`), whose complex
structure acts diagonally on `ℝ ⊗ (ι → V) ≅ (ι → ℝ ⊗ V)`, and the orthogonal sum
`P.pi ι` of a polarization `P`. We then prove that, for `ι` nonempty and `V` finite-dimensional,
the Hodge group and the Mumford–Tate group of `V^ι` are the diagonal images of those of `V`:

* `HodgeStructureNegOne.hodgeGroup_pi`:
  `(H.pi ι).hodgeGroup = H.hodgeGroup.map (diagHom ℚ ι V)`;
* `HodgeStructureNegOne.mumfordTateGroup_pi`:
  `(H.pi ι).mumfordTateGroup = H.mumfordTateGroup.map (diagHom ℚ ι V)`;

and the consequences `hodgeGroup_pi_eq_map_symplecticGroup` (if `Hdg(V) = Sp(V, ψ)` then
`Hdg(V^ι)` is the diagonal `Sp(V, ψ)`) and `mumfordTateGroup_pi_eq_map_similitudeGroup`
(likewise for `MT` and `GSp`), with the `Fin h` versions `hodgeGroup_pow`, … for `0 < h`.
This is the linear algebra behind the reduction of statements about all powers `J^h` of a
Jacobian to `J` itself (manuscript, Corollary 6.6); nothing about
Jacobians is asserted here.

## Method

* `tensorPush p q : T m n (M) → T m n (N)` is the map induced by linear maps `p k : M → N` on the
  `M` factors and by the transposes of `q k : N → M` on the dual factors. It intertwines the
  actions of `g` and `g'` when `p k ∘ g = g' ∘ p k` and `g ∘ q k = q k ∘ g'`
  (`tensorPush_tensorMap`), commutes with realification (`realify_tensorPush`), and hence maps
  Hodge classes to Hodge classes when the `p k`, `q k` commute with the complex structures
  (`tensorPush_mem_hodgeClasses`).
* For multi-indices `α : Fin m → ι`, `β : Fin n → ι`, `projPush α β` (coordinate projections on
  the `V^ι` factors) and `singlePush α β` (coordinate inclusions) give the decomposition
  `∑ α β, singlePush α β ∘ projPush α β = id` of `T m n (V^ι)` (`sum_singlePush_projPush`)
  into copies of `T m n (V)`. Both maps are equivariant for the diagonal action and preserve
  Hodge classes; this proves `diag (Hdg V) ≤ Hdg (V^ι)` and `diag (MT V) ≤ MT (V^ι)`.
* Conversely, an endomorphism `e` of `V` whose real extension commutes with `J` is a Hodge class
  of `T 1 1` (`exists_mem_hodgeClasses_tensorEndEquiv`, via `End(M) ≅ M ⊗ M^*`), so every
  element of `MT` commutes with it (`commute_of_mem_mumfordTateGroup`). Applied to the block
  endomorphisms `blockEnd i j = single i ∘ proj j` of `V^ι`, an element of `MT (V^ι)` (or of
  `Hdg (V^ι)`) is block-diagonal with equal blocks (`exists_eq_diagHom`), and its block lies in
  `MT V` (resp. `Hdg V`) since `projPush ∘ singlePush = id` for constant multi-indices.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open TensorProduct

section Diagonal

variable (R : Type*) [Semiring R] (ι V : Type*) [AddCommMonoid V] [Module R V]

/-- **The diagonal embedding** `GL(V) →* GL(V^ι)`, `g ↦ (x ↦ (i ↦ g (x i)))`. -/
@[expose]
def diagHom : (V ≃ₗ[R] V) →* ((ι → V) ≃ₗ[R] (ι → V)) where
  toFun g := LinearEquiv.piCongrRight fun _ => g
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

variable {R ι V}

/-- `diag g` acts coordinatewise. -/
theorem diagHom_apply (g : V ≃ₗ[R] V) (x : ι → V) (i : ι) : diagHom R ι V g x i = g (x i) :=
  rfl

/-- `diag g (single i y) = single i (g y)`. -/
theorem diagHom_apply_single [DecidableEq ι] (g : V ≃ₗ[R] V) (i : ι) (y : V) :
    diagHom R ι V g (Pi.single i y) = Pi.single i (g y) :=
  funext fun j => Pi.apply_single (fun _ x => g x) (fun _ => map_zero g) i y j

/-- The diagonal embedding is injective when `ι` is nonempty. -/
theorem diagHom_injective [Nonempty ι] : Function.Injective (diagHom R ι V) := by
  intro g g' h
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact LinearEquiv.ext fun v => congrArg (fun e : (ι → V) ≃ₗ[R] (ι → V) => e (fun _ => v) i₀) h

variable (R V) in
/-- **The block endomorphism** `single i ∘ proj j` of `V^ι`. -/
@[expose]
def blockEnd [DecidableEq ι] (i j : ι) : Module.End R (ι → V) :=
  LinearMap.single R (fun _ : ι => V) i ∘ₗ LinearMap.proj j

/-- `blockEnd i j x = single i (x j)`. -/
theorem blockEnd_apply [DecidableEq ι] (i j : ι) (x : ι → V) :
    blockEnd R V i j x = Pi.single i (x j) :=
  rfl

/-- A map commuting with all `x ↦ single i (x j)` is determined by one diagonal block. -/
theorem apply_eq_of_commute_single [DecidableEq ι] (f : (ι → V) → (ι → V))
    (hf : ∀ i j x, f (Pi.single i (x j)) = Pi.single i (f x j)) (i₀ : ι) (x : ι → V) (j : ι) :
    f x j = f (Pi.single i₀ (x j)) i₀ := by
  rw [hf i₀ j x, Pi.single_eq_same]

/-- **Block-diagonal with equal blocks**: an automorphism of `V^ι` commuting with all block
endomorphisms `x ↦ single i (x j)` is the diagonal image of an automorphism of `V`. -/
theorem exists_eq_diagHom [DecidableEq ι] [Nonempty ι] (g : (ι → V) ≃ₗ[R] (ι → V))
    (hg : ∀ i j x, g (Pi.single i (x j)) = Pi.single i (g x j)) :
    ∃ g₀ : V ≃ₗ[R] V, diagHom R ι V g₀ = g := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hg' : ∀ i j x, g.symm (Pi.single i (x j)) = Pi.single i (g.symm x j) := by
    intro i j x
    rw [LinearEquiv.symm_apply_eq, hg i j (g.symm x), LinearEquiv.apply_symm_apply]
  have hb := apply_eq_of_commute_single (⇑g) hg i₀
  have hb' := apply_eq_of_commute_single (⇑g.symm) hg' i₀
  refine ⟨LinearEquiv.ofLinearMap
    (f := LinearMap.proj i₀ ∘ₗ (g : (ι → V) →ₗ[R] (ι → V)) ∘ₗ
      LinearMap.single R (fun _ : ι => V) i₀)
    (g := LinearMap.proj i₀ ∘ₗ (g.symm : (ι → V) →ₗ[R] (ι → V)) ∘ₗ
      LinearMap.single R (fun _ : ι => V) i₀) ?_ ?_, ?_⟩
  · refine LinearMap.ext fun v => ?_
    change g (Pi.single i₀ (g.symm (Pi.single i₀ v) i₀)) i₀ = v
    rw [← hb (g.symm (Pi.single i₀ v)) i₀, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
  · refine LinearMap.ext fun v => ?_
    change g.symm (Pi.single i₀ (g (Pi.single i₀ v) i₀)) i₀ = v
    rw [← hb' (g (Pi.single i₀ v)) i₀, LinearEquiv.symm_apply_apply, Pi.single_eq_same]
  · refine LinearEquiv.ext fun x => funext fun j => ?_
    change g (Pi.single i₀ (x j)) i₀ = g x j
    exact (hb x j).symm

end Diagonal

section TensorPush

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P] {m n : ℕ}

/-- **Functoriality of tensor spaces**: the map `T m n (M) → T m n (N)` induced by linear maps
`p k : M → N` on the `M` factors and by the transposes of `q k : N → M` on the dual factors. -/
@[expose]
noncomputable def tensorPush (p : Fin m → M →ₗ[R] N) (q : Fin n → N →ₗ[R] M) :
    TensorSpace R M m n →ₗ[R] TensorSpace R N m n :=
  TensorProduct.map (PiTensorProduct.map p) (PiTensorProduct.map fun k => (q k).dualMap)

/-- `tensorPush` on pure tensors `a ⊗ b`. -/
theorem tensorPush_tmul (p : Fin m → M →ₗ[R] N) (q : Fin n → N →ₗ[R] M)
    (a : TensorPower R m M) (b : TensorPower R n (Module.Dual R M)) :
    tensorPush p q (a ⊗ₜ b) =
      PiTensorProduct.map p a ⊗ₜ PiTensorProduct.map (fun k => (q k).dualMap) b :=
  rfl

/-- Composition of `tensorPush` maps. -/
theorem tensorPush_comp (p : Fin m → M →ₗ[R] N) (q : Fin n → N →ₗ[R] M)
    (p' : Fin m → N →ₗ[R] P) (q' : Fin n → P →ₗ[R] N) :
    tensorPush p' q' ∘ₗ tensorPush p q =
      tensorPush (fun k => p' k ∘ₗ p k) (fun k => q k ∘ₗ q' k) := by
  simp only [tensorPush, ← TensorProduct.map_comp, ← PiTensorProduct.map_comp,
    LinearMap.dualMap_comp_dualMap]

/-- Composition of `tensorPush` maps, pointwise. -/
theorem tensorPush_tensorPush (p : Fin m → M →ₗ[R] N) (q : Fin n → N →ₗ[R] M)
    (p' : Fin m → N →ₗ[R] P) (q' : Fin n → P →ₗ[R] N) (t : TensorSpace R M m n) :
    tensorPush p' q' (tensorPush p q t) =
      tensorPush (fun k => p' k ∘ₗ p k) (fun k => q k ∘ₗ q' k) t := by
  rw [← LinearMap.comp_apply, tensorPush_comp]

/-- `tensorPush id id = id`. -/
theorem tensorPush_id :
    tensorPush (fun _ : Fin m => (LinearMap.id : M →ₗ[R] M)) (fun _ : Fin n => LinearMap.id) =
      LinearMap.id := by
  simp only [tensorPush, LinearMap.dualMap_id, PiTensorProduct.map_id, TensorProduct.map_id]

/-- **Equivariance of `tensorPush`**: if `p k ∘ g = g' ∘ p k` and `g ∘ q k = q k ∘ g'`, then
`tensorPush p q` intertwines the actions of `g` and `g'`. -/
theorem tensorPush_tensorMap (p : Fin m → M →ₗ[R] N) (q : Fin n → N →ₗ[R] M)
    (g : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N) (hp : ∀ k x, p k (g x) = g' (p k x))
    (hq : ∀ k y, g (q k y) = q k (g' y)) (t : TensorSpace R M m n) :
    tensorPush p q (tensorMap m n g t) = tensorMap m n g' (tensorPush p q t) := by
  have h1 : (fun k => p k ∘ₗ (g : M →ₗ[R] M)) = fun k => (g' : N →ₗ[R] N) ∘ₗ p k :=
    funext fun k => LinearMap.ext fun x => hp k x
  have h2 : (fun k => (q k).dualMap ∘ₗ
      (g.symm.dualMap : Module.Dual R M →ₗ[R] Module.Dual R M)) =
      fun k => (g'.symm.dualMap : Module.Dual R N →ₗ[R] Module.Dual R N) ∘ₗ (q k).dualMap := by
    funext k
    refine LinearMap.ext fun φ => LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
      LinearEquiv.dualMap_apply]
    congr 1
    rw [LinearEquiv.symm_apply_eq, hq, LinearEquiv.apply_symm_apply]
  have key : tensorPush p q ∘ₗ tensorMap m n g = tensorMap m n g' ∘ₗ tensorPush p q := by
    simp only [tensorPush, tensorMap, ← TensorProduct.map_comp, ← PiTensorProduct.map_comp]
    exact congrArg₂ TensorProduct.map (congrArg PiTensorProduct.map h1)
      (congrArg PiTensorProduct.map h2)
  exact LinearMap.congr_fun key t

end TensorPush

section TensorEnd

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The isomorphism `M^{⊗1} ≅ M`. -/
@[expose]
noncomputable def powOneEquiv : TensorPower R 1 M ≃ₗ[R] M :=
  PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => M) 0

variable {R M}

/-- `powOneEquiv` on pure tensors. -/
theorem powOneEquiv_tprod (f : Fin 1 → M) : powOneEquiv R M (PiTensorProduct.tprod R f) = f 0 := by
  simp only [powOneEquiv, PiTensorProduct.subsingletonEquiv_apply_tprod]

/-- `powOneEquiv` is natural. -/
theorem powOneEquiv_map {N : Type*} [AddCommGroup N] [Module R N] (f : Fin 1 → M →ₗ[R] N)
    (a : TensorPower R 1 M) :
    powOneEquiv R N (PiTensorProduct.map f a) = f 0 (powOneEquiv R M a) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r φ => simp only [map_smul, PiTensorProduct.map_tprod, powOneEquiv_tprod]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (R M) [Module.Free R M] [Module.Finite R M]

/-- **`T 1 1 ≅ End(M)`** for `M` finite free: `v ⊗ φ ↦ (x ↦ φ x • v)`. -/
@[expose]
noncomputable def tensorEndEquiv : TensorSpace R M 1 1 ≃ₗ[R] Module.End R M :=
  (TensorProduct.congr (powOneEquiv R M) (powOneEquiv R (Module.Dual R M))).trans
    ((TensorProduct.comm R M (Module.Dual R M)).trans (dualTensorHomEquiv R M M))

variable {R M}

/-- `tensorEndEquiv (a ⊗ b) x = b x • a`. -/
theorem tensorEndEquiv_tmul (a : TensorPower R 1 M) (b : TensorPower R 1 (Module.Dual R M))
    (x : M) :
    tensorEndEquiv R M (a ⊗ₜ b) x = powOneEquiv R (Module.Dual R M) b x • powOneEquiv R M a :=
  rfl

/-- **Equivariance of `tensorEndEquiv`**: `g • t` corresponds to `g ∘ e ∘ g⁻¹`. -/
theorem tensorEndEquiv_tensorMap (g : M ≃ₗ[R] M) (t : TensorSpace R M 1 1) (x : M) :
    tensorEndEquiv R M (tensorMap 1 1 g t) x = g (tensorEndEquiv R M t (g.symm x)) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [tensorMap_tmul, tensorEndEquiv_tmul, tensorEndEquiv_tmul, powOneEquiv_map,
      powOneEquiv_map, map_smul]
    rfl
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

end TensorEnd

section Realify

/-- `realifyPow` is natural with respect to families of linear maps. -/
theorem realifyPow_map {k : ℕ} {X Y X' Y' : Type*} [AddCommGroup X] [Module ℚ X]
    [AddCommGroup Y] [Module ℚ Y] [AddCommGroup X'] [Module ℝ X'] [Module ℚ X']
    [IsScalarTower ℚ ℝ X'] [AddCommGroup Y'] [Module ℝ Y'] [Module ℚ Y'] [IsScalarTower ℚ ℝ Y']
    (f₁ : X →ₗ[ℚ] X') (f₂ : Y →ₗ[ℚ] Y') (p : Fin k → X →ₗ[ℚ] Y) (p' : Fin k → X' →ₗ[ℝ] Y')
    (h : ∀ i x, f₂ (p i x) = p' i (f₁ x)) (a : TensorPower ℚ k X) :
    realifyPow k f₂ (PiTensorProduct.map p a) = PiTensorProduct.map p' (realifyPow k f₁ a) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r φ =>
    simp only [map_rat_smul, PiTensorProduct.map_tprod, realifyPow_tprod, h]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `realifyPow 1` under `M^{⊗1} ≅ M`. -/
theorem powOneEquiv_realifyPow {X Y : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup Y]
    [Module ℝ Y] [Module ℚ Y] [IsScalarTower ℚ ℝ Y] (f : X →ₗ[ℚ] Y) (a : TensorPower ℚ 1 X) :
    powOneEquiv ℝ Y (realifyPow 1 f a) = f (powOneEquiv ℚ X a) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r φ => simp only [map_rat_smul, realifyPow_tprod, powOneEquiv_tprod]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {M N W : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  [AddCommGroup W] [Module ℚ W]

/-- The base change of a transpose is the transpose of the base change. -/
theorem dualBaseChange_dualMap (q : N →ₗ[ℚ] M) (φ : Module.Dual ℚ M) :
    dualBaseChange (q.dualMap φ) = (q.baseChange ℝ).dualMap (dualBaseChange φ) := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.inductionOn with
  | tmul a v => simp only [LinearMap.dualMap_apply, LinearMap.baseChange_tmul, dualBaseChange_tmul]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']

/-- **Realification commutes with `tensorPush`.** -/
theorem realify_tensorPush {m n : ℕ} (p : Fin m → M →ₗ[ℚ] N) (q : Fin n → N →ₗ[ℚ] M)
    (t : TensorSpace ℚ M m n) :
    realify m n (tensorPush p q t) =
      tensorPush (fun k => (p k).baseChange ℝ) (fun k => (q k).baseChange ℝ) (realify m n t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [tensorPush_tmul, realify_tmul]
    rw [realifyPow_map (TensorProduct.mk ℚ ℝ M 1) (TensorProduct.mk ℚ ℝ N 1) p
        (fun k => (p k).baseChange ℝ) (fun _ _ => rfl),
      realifyPow_map dualBaseChange dualBaseChange (fun k => (q k).dualMap)
        (fun k => ((q k).baseChange ℝ).dualMap) (fun k φ => dualBaseChange_dualMap (q k) φ)]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Realification and `T 1 1 ≅ End`**: the endomorphism of the realified tensor is the real
extension of the endomorphism. -/
theorem tensorEndEquiv_realify [FiniteDimensional ℚ W] (t : TensorSpace ℚ W 1 1)
    (y : ℝ ⊗[ℚ] W) :
    tensorEndEquiv ℝ (ℝ ⊗[ℚ] W) (realify 1 1 t) y = (tensorEndEquiv ℚ W t).baseChange ℝ y := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, LinearMap.baseChange_add, hs, ht]
  | tmul a b =>
    rw [realify_tmul, tensorEndEquiv_tmul, powOneEquiv_realifyPow, powOneEquiv_realifyPow]
    induction y using TensorProduct.inductionOn with
    | tmul c w =>
      rw [dualBaseChange_tmul, LinearMap.baseChange_tmul, tensorEndEquiv_tmul,
        TensorProduct.mk_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add y y' hy hy' => simp only [map_add, add_smul, hy, hy']

end Realify

namespace HodgeStructureNegOne

section Functoriality

variable {M N W : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  [AddCommGroup W] [Module ℚ W]

/-- **`tensorPush` maps Hodge classes to Hodge classes** when the real extensions of the `p k`
and `q k` commute with the complex structures. -/
theorem tensorPush_mem_hodgeClasses (H₁ : HodgeStructureNegOne M) (H₂ : HodgeStructureNegOne N)
    {m n : ℕ} (p : Fin m → M →ₗ[ℚ] N) (q : Fin n → N →ₗ[ℚ] M)
    (hp : ∀ k x, (p k).baseChange ℝ (H₁.J x) = H₂.J ((p k).baseChange ℝ x))
    (hq : ∀ k y, H₁.J ((q k).baseChange ℝ y) = (q k).baseChange ℝ (H₂.J y))
    {t : TensorSpace ℚ M m n} (ht : t ∈ H₁.hodgeClasses m n) :
    tensorPush p q t ∈ H₂.hodgeClasses m n := by
  refine H₂.mem_hodgeClasses.2 fun z => ?_
  have hp' : ∀ k x, (p k).baseChange ℝ (H₁.circleRep z x) =
      H₂.circleRep z ((p k).baseChange ℝ x) := by
    intro k x
    rw [circleRep_apply, circleRep_apply, map_add, map_smul, map_smul, hp]
  have hq' : ∀ k y, H₁.circleRep z ((q k).baseChange ℝ y) =
      (q k).baseChange ℝ (H₂.circleRep z y) := by
    intro k y
    rw [circleRep_apply, circleRep_apply, map_add, map_smul, map_smul, hq]
  rw [realify_tensorPush, ← tensorPush_tensorMap (fun k => (p k).baseChange ℝ)
    (fun k => (q k).baseChange ℝ) (H₁.circleRep z) (H₂.circleRep z) hp' hq',
    H₁.mem_hodgeClasses.1 ht z]

variable (H : HodgeStructureNegOne W)

/-- **Hodge endomorphisms are Hodge classes**: an endomorphism `e` of `W` whose real extension
commutes with `J` is (under `T 1 1 ≅ End`) a Hodge class of `T 1 1`. -/
theorem exists_mem_hodgeClasses_tensorEndEquiv [FiniteDimensional ℚ W] (e : Module.End ℚ W)
    (he : ∀ x, e.baseChange ℝ (H.J x) = H.J (e.baseChange ℝ x)) :
    ∃ t ∈ H.hodgeClasses 1 1, tensorEndEquiv ℚ W t = e := by
  refine ⟨(tensorEndEquiv ℚ W).symm e, H.mem_hodgeClasses.2 fun z => ?_,
    LinearEquiv.apply_symm_apply _ _⟩
  have hc : ∀ x, e.baseChange ℝ (H.circleRep z x) = H.circleRep z (e.baseChange ℝ x) := by
    intro x
    rw [circleRep_apply, circleRep_apply, map_add, map_smul, map_smul, he]
  apply (tensorEndEquiv ℝ (ℝ ⊗[ℚ] W)).injective
  refine LinearMap.ext fun y => ?_
  rw [tensorEndEquiv_tensorMap, tensorEndEquiv_realify, tensorEndEquiv_realify,
    LinearEquiv.apply_symm_apply, ← hc, LinearEquiv.apply_symm_apply]

/-- **The Mumford–Tate group commutes with Hodge endomorphisms**: if the real extension of `e`
commutes with `J` and `g ∈ MT(H)`, then `g ∘ e = e ∘ g`. -/
theorem commute_of_mem_mumfordTateGroup [FiniteDimensional ℚ W] (e : Module.End ℚ W)
    (he : ∀ x, e.baseChange ℝ (H.J x) = H.J (e.baseChange ℝ x)) {g : W ≃ₗ[ℚ] W}
    (hg : g ∈ H.mumfordTateGroup) (x : W) : g (e x) = e (g x) := by
  obtain ⟨t, ht, rfl⟩ := H.exists_mem_hodgeClasses_tensorEndEquiv e he
  obtain ⟨c, hc⟩ := H.mem_mumfordTateGroup.1 hg
  have h1 : tensorMap 1 1 g t = t := by
    rw [hc 1 1 0 (by norm_num) t ht, neg_zero, zpow_zero, Units.val_one, one_smul]
  have h2 := tensorEndEquiv_tensorMap g t (g x)
  rw [h1, LinearEquiv.symm_apply_apply] at h2
  exact h2.symm

end Functoriality

section Power

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (H : HodgeStructureNegOne V)
  (ι : Type*) [Fintype ι] [DecidableEq ι]

variable (V) in
/-- `ℝ ⊗ (ι → V) ≅ (ι → ℝ ⊗ V)`. -/
@[expose]
noncomputable def realPiEquiv : ℝ ⊗[ℚ] (ι → V) ≃ₗ[ℝ] (ι → ℝ ⊗[ℚ] V) :=
  TensorProduct.piRight ℚ ℝ ℝ (fun _ : ι => V)

variable {ι}

/-- `realPiEquiv (a ⊗ f) = (i ↦ a ⊗ f i)`. -/
theorem realPiEquiv_tmul (a : ℝ) (f : ι → V) :
    realPiEquiv V ι (a ⊗ₜ f) = fun i => a ⊗ₜ f i := by
  rw [realPiEquiv, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]

/-- The real extension of the `i`-th projection is the `i`-th coordinate of `realPiEquiv`. -/
theorem baseChange_proj_apply (i : ι) (x : ℝ ⊗[ℚ] (ι → V)) :
    (LinearMap.proj i : (ι → V) →ₗ[ℚ] V).baseChange ℝ x = realPiEquiv V ι x i := by
  induction x using TensorProduct.inductionOn with
  | tmul a f => simp only [LinearMap.baseChange_tmul, realPiEquiv_tmul, LinearMap.proj_apply]
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy]

/-- The real extension of the `i`-th inclusion corresponds to `Pi.single i`. -/
theorem realPiEquiv_baseChange_single (i : ι) (y : ℝ ⊗[ℚ] V) :
    realPiEquiv V ι ((LinearMap.single ℚ (fun _ : ι => V) i).baseChange ℝ y) = Pi.single i y := by
  induction y using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, realPiEquiv_tmul]
    funext j
    rw [LinearMap.coe_single]
    exact Pi.apply_single (fun _ w => a ⊗ₜ[ℚ] w) (fun _ => TensorProduct.tmul_zero V a) i v j
  | add x y hx hy => rw [map_add, map_add, hx, hy, Pi.single_add]

variable (ι)

/-- The diagonal complex structure on `ℝ ⊗ (ι → V) ≅ (ι → ℝ ⊗ V)`. -/
@[expose]
noncomputable def piJ : Module.End ℝ (ℝ ⊗[ℚ] (ι → V)) :=
  (realPiEquiv V ι).symm.toLinearMap ∘ₗ LinearMap.pi (fun i => H.J ∘ₗ LinearMap.proj i) ∘ₗ
    (realPiEquiv V ι).toLinearMap

variable {ι}

/-- `piJ` acts coordinatewise. -/
theorem realPiEquiv_piJ (x : ℝ ⊗[ℚ] (ι → V)) :
    realPiEquiv V ι (H.piJ ι x) = fun i => H.J (realPiEquiv V ι x i) := by
  simp only [piJ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

variable (ι)

/-- **The Hodge structure on `V^ι = ι → V`** (the direct sum of copies of `H`): `J` acts
diagonally on `ℝ ⊗ (ι → V) ≅ (ι → ℝ ⊗ V)`. -/
@[expose]
noncomputable def pi : HodgeStructureNegOne (ι → V) where
  J := H.piJ ι
  J_mul_J := by
    refine LinearMap.ext fun x => (realPiEquiv V ι).injective ?_
    rw [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply, realPiEquiv_piJ,
      realPiEquiv_piJ, map_neg]
    funext i
    simp only [H.J_apply_J, Pi.neg_apply]

/-- **The Hodge structure on `V^h`**. -/
noncomputable abbrev pow (h : ℕ) : HodgeStructureNegOne (Fin h → V) :=
  H.pi (Fin h)

variable {ι}

/-- The complex structure of `H.pi ι` acts coordinatewise. -/
theorem realPiEquiv_pi_J (x : ℝ ⊗[ℚ] (ι → V)) :
    realPiEquiv V ι ((H.pi ι).J x) = fun i => H.J (realPiEquiv V ι x i) :=
  H.realPiEquiv_piJ x

/-- The projections are morphisms of Hodge structures. -/
theorem baseChange_proj_pi_J (i : ι) (x : ℝ ⊗[ℚ] (ι → V)) :
    (LinearMap.proj i : (ι → V) →ₗ[ℚ] V).baseChange ℝ ((H.pi ι).J x) =
      H.J ((LinearMap.proj i : (ι → V) →ₗ[ℚ] V).baseChange ℝ x) := by
  rw [baseChange_proj_apply, baseChange_proj_apply, realPiEquiv_pi_J]

/-- The inclusions are morphisms of Hodge structures. -/
theorem pi_J_baseChange_single (i : ι) (y : ℝ ⊗[ℚ] V) :
    (H.pi ι).J ((LinearMap.single ℚ (fun _ : ι => V) i).baseChange ℝ y) =
      (LinearMap.single ℚ (fun _ : ι => V) i).baseChange ℝ (H.J y) := by
  apply (realPiEquiv V ι).injective
  rw [realPiEquiv_pi_J, realPiEquiv_baseChange_single, realPiEquiv_baseChange_single]
  funext j
  exact Pi.apply_single (fun _ w => H.J w) (fun _ => map_zero H.J) i y j

/-- The block endomorphisms of `V^ι` are endomorphisms of Hodge structures. -/
theorem blockEnd_baseChange_pi_J (i j : ι) (x : ℝ ⊗[ℚ] (ι → V)) :
    (blockEnd ℚ V i j).baseChange ℝ ((H.pi ι).J x) =
      (H.pi ι).J ((blockEnd ℚ V i j).baseChange ℝ x) := by
  rw [blockEnd, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    baseChange_proj_pi_J, pi_J_baseChange_single]

section Polarization

variable (ι) in
/-- The orthogonal sum `∑ᵢ ψ (x i) (y i)` of a bilinear form on `V` over `ι`. -/
@[expose]
def piForm (ψ : LinearMap.BilinForm ℚ V) : LinearMap.BilinForm ℚ (ι → V) :=
  ∑ i, ψ.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

omit [DecidableEq ι] in
/-- `piForm ψ x y = ∑ᵢ ψ (x i) (y i)`. -/
theorem piForm_apply (ψ : LinearMap.BilinForm ℚ V) (x y : ι → V) :
    piForm ι ψ x y = ∑ i, ψ (x i) (y i) := by
  simp only [piForm, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]

/-- The real extension of `piForm ψ` is the orthogonal sum of copies of `ψ_ℝ`. -/
theorem baseChange_piForm_apply (ψ : LinearMap.BilinForm ℚ V) (x y : ℝ ⊗[ℚ] (ι → V)) :
    (piForm ι ψ).baseChange ℝ x y =
      ∑ i, ψ.baseChange ℝ (realPiEquiv V ι x i) (realPiEquiv V ι y i) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hx, hx', Finset.sum_add_distrib]
  | tmul a f =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, Pi.add_apply, hy, hy', Finset.sum_add_distrib]
    | tmul b f' =>
      simp only [LinearMap.BilinForm.baseChange_tmul, realPiEquiv_tmul, piForm_apply,
        Finset.sum_smul]

variable {H} (ι)

/-- **The orthogonal sum of a polarization** is a polarization of `H.pi ι`. -/
@[expose]
noncomputable def Polarization.pi (P : H.Polarization) : (H.pi ι).Polarization where
  form := piForm ι P.form
  form_self x := by simp only [piForm_apply, P.form_self, Finset.sum_const_zero]
  baseChange_J x y := by simp only [baseChange_piForm_apply, realPiEquiv_pi_J, P.baseChange_J]
  pos x hx := by
    simp only [baseChange_piForm_apply, realPiEquiv_pi_J]
    obtain ⟨i, hi⟩ : ∃ i, realPiEquiv V ι x i ≠ 0 := by
      by_contra h
      exact hx ((realPiEquiv V ι).map_eq_zero_iff.1
        (funext fun j => Classical.byContradiction fun hj => h ⟨j, hj⟩))
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, P.pos _ hi⟩
    by_cases hj : realPiEquiv V ι x j = 0
    · simp [hj]
    · exact (P.pos _ hj).le

/-- **The polarization of `V^h`**. -/
noncomputable abbrev Polarization.pow (P : H.Polarization) (h : ℕ) : (H.pow h).Polarization :=
  P.pi (Fin h)

end Polarization

section MultiIndex

variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] [Module R X] {m n : ℕ}

/-- The projection `T m n (X^ι) → T m n (X)` of multi-index `(α, β)`. -/
@[expose]
noncomputable def projPush (α : Fin m → ι) (β : Fin n → ι) :
    TensorSpace R (ι → X) m n →ₗ[R] TensorSpace R X m n :=
  tensorPush (fun k => LinearMap.proj (α k)) (fun k => LinearMap.single R (fun _ : ι => X) (β k))

/-- The inclusion `T m n (X) → T m n (X^ι)` of multi-index `(α, β)`. -/
@[expose]
noncomputable def singlePush (α : Fin m → ι) (β : Fin n → ι) :
    TensorSpace R X m n →ₗ[R] TensorSpace R (ι → X) m n :=
  tensorPush (fun k => LinearMap.single R (fun _ : ι => X) (α k)) (fun k => LinearMap.proj (β k))

/-- `∑ᵢ single i ∘ proj i = id`. -/
theorem sum_single_comp_proj :
    ∑ i, LinearMap.single R (fun _ : ι => X) i ∘ₗ LinearMap.proj i = LinearMap.id :=
  LinearMap.ext fun x => by
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_single,
      LinearMap.proj_apply, LinearMap.id_apply, Finset.univ_sum_single]

/-- `∑ᵢ (single i ∘ proj i)ᵀ = id`. -/
theorem sum_dualMap_single_comp_proj :
    ∑ i, (LinearMap.single R (fun _ : ι => X) i ∘ₗ LinearMap.proj i).dualMap = LinearMap.id := by
  refine LinearMap.ext fun φ => LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun (sum_single_comp_proj (R := R) (ι := ι) (X := X)) x
  simp only [LinearMap.sum_apply, LinearMap.id_apply] at hx
  simp only [LinearMap.sum_apply, LinearMap.dualMap_apply, LinearMap.id_apply, ← map_sum, hx]

omit [DecidableEq ι] in
/-- Expanding `⊗ₖ (∑ᵢ Eᵢ)` multilinearly. -/
theorem sum_piTensorMap_apply {Y : Type*} [AddCommGroup Y] [Module R Y] {k : ℕ}
    (E : ι → Module.End R Y) (hE : ∑ i, E i = LinearMap.id) (a : TensorPower R k Y) :
    ∑ α : Fin k → ι, PiTensorProduct.map (fun j => E (α j)) a = a := by
  have h : ∑ α : Fin k → ι, PiTensorProduct.map (fun j => E (α j)) =
      PiTensorProduct.map (fun _ : Fin k => ∑ i, E i) :=
    ((PiTensorProduct.mapMultilinear R (fun _ : Fin k => Y) (fun _ => Y)).map_sum
      (fun _ i => E i)).symm
  rw [hE, PiTensorProduct.map_id] at h
  simpa only [LinearMap.sum_apply, LinearMap.id_apply] using LinearMap.congr_fun h a

/-- **Decomposition of `T m n (X^ι)`**: `∑_{α, β} singlePush α β ∘ projPush α β = id`. -/
theorem sum_singlePush_projPush (t : TensorSpace R (ι → X) m n) :
    ∑ α : Fin m → ι, ∑ β : Fin n → ι, singlePush α β (projPush α β t) = t := by
  have hcomp : ∀ (α : Fin m → ι) (β : Fin n → ι) (s : TensorSpace R (ι → X) m n),
      singlePush α β (projPush α β s) =
        tensorPush (fun k => blockEnd R X (α k) (α k)) (fun k => blockEnd R X (β k) (β k)) s :=
    fun α β s => by
      rw [singlePush, projPush, tensorPush_tensorPush]
      rfl
  simp only [hcomp]
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | tmul a b =>
    simp only [tensorPush_tmul]
    calc ∑ α : Fin m → ι, ∑ β : Fin n → ι,
          PiTensorProduct.map (fun k => blockEnd R X (α k) (α k)) a ⊗ₜ
            PiTensorProduct.map (fun k => (blockEnd R X (β k) (β k)).dualMap) b
        = ∑ α : Fin m → ι, PiTensorProduct.map (fun k => blockEnd R X (α k) (α k)) a ⊗ₜ
            ∑ β : Fin n → ι,
              PiTensorProduct.map (fun k => (blockEnd R X (β k) (β k)).dualMap) b :=
          Finset.sum_congr rfl fun α _ => (TensorProduct.tmul_sum _ _ _).symm
      _ = (∑ α : Fin m → ι, PiTensorProduct.map (fun k => blockEnd R X (α k) (α k)) a) ⊗ₜ
            ∑ β : Fin n → ι,
              PiTensorProduct.map (fun k => (blockEnd R X (β k) (β k)).dualMap) b :=
          (TensorProduct.sum_tmul _ _ _).symm
      _ = a ⊗ₜ b := by
          rw [sum_piTensorMap_apply (fun i => blockEnd R X i i) sum_single_comp_proj,
            sum_piTensorMap_apply (fun i => (blockEnd R X i i).dualMap)
              sum_dualMap_single_comp_proj]

omit [Fintype ι] in
/-- `projPush ∘ singlePush = id` for constant multi-indices. -/
theorem projPush_singlePush_const (i₀ : ι) (s : TensorSpace R X m n) :
    projPush (fun _ : Fin m => i₀) (fun _ : Fin n => i₀) (singlePush (fun _ => i₀) (fun _ => i₀) s)
      = s := by
  rw [projPush, singlePush, tensorPush_tensorPush]
  simp only [LinearMap.proj_comp_single_same, tensorPush_id, LinearMap.id_apply]

omit [Fintype ι] in
/-- `projPush` is equivariant for the diagonal action. -/
theorem projPush_tensorMap (α : Fin m → ι) (β : Fin n → ι) (g : X ≃ₗ[R] X)
    (t : TensorSpace R (ι → X) m n) :
    projPush α β (tensorMap m n (diagHom R ι X g) t) = tensorMap m n g (projPush α β t) :=
  tensorPush_tensorMap (fun k => LinearMap.proj (α k))
    (fun k => LinearMap.single R (fun _ : ι => X) (β k)) (diagHom R ι X g) g (fun _ _ => rfl)
    (fun k y => diagHom_apply_single g (β k) y) t

omit [Fintype ι] in
/-- `singlePush` is equivariant for the diagonal action. -/
theorem singlePush_tensorMap (α : Fin m → ι) (β : Fin n → ι) (g : X ≃ₗ[R] X)
    (s : TensorSpace R X m n) :
    singlePush α β (tensorMap m n g s) = tensorMap m n (diagHom R ι X g) (singlePush α β s) :=
  tensorPush_tensorMap (fun k => LinearMap.single R (fun _ : ι => X) (α k))
    (fun k => LinearMap.proj (β k)) g (diagHom R ι X g)
    (fun k x => (diagHom_apply_single g (α k) x).symm) (fun _ _ => rfl) s

end MultiIndex

section Groups

variable {m n : ℕ}

/-- `projPush` maps Hodge classes of `H.pi ι` to Hodge classes of `H`. -/
theorem projPush_mem_hodgeClasses (α : Fin m → ι) (β : Fin n → ι)
    {t : TensorSpace ℚ (ι → V) m n} (ht : t ∈ (H.pi ι).hodgeClasses m n) :
    projPush α β t ∈ H.hodgeClasses m n :=
  tensorPush_mem_hodgeClasses (H.pi ι) H (fun k => LinearMap.proj (α k))
    (fun k => LinearMap.single ℚ (fun _ : ι => V) (β k)) (fun k x => H.baseChange_proj_pi_J (α k) x)
    (fun k y => H.pi_J_baseChange_single (β k) y) ht

/-- `singlePush` maps Hodge classes of `H` to Hodge classes of `H.pi ι`. -/
theorem singlePush_mem_hodgeClasses (α : Fin m → ι) (β : Fin n → ι)
    {s : TensorSpace ℚ V m n} (hs : s ∈ H.hodgeClasses m n) :
    singlePush α β s ∈ (H.pi ι).hodgeClasses m n :=
  tensorPush_mem_hodgeClasses H (H.pi ι) (fun k => LinearMap.single ℚ (fun _ : ι => V) (α k))
    (fun k => LinearMap.proj (β k))
    (fun k x => (H.pi_J_baseChange_single (α k) x).symm)
    (fun k y => (H.baseChange_proj_pi_J (β k) y).symm) hs

/-- **`diag (Hdg H) ≤ Hdg (H.pi ι)`**. -/
theorem diagHom_mem_hodgeGroup {g : V ≃ₗ[ℚ] V} (hg : g ∈ H.hodgeGroup) :
    diagHom ℚ ι V g ∈ (H.pi ι).hodgeGroup := by
  refine (H.pi ι).mem_hodgeGroup.2 fun m n t ht => ?_
  calc tensorMap m n (diagHom ℚ ι V g) t
      = ∑ α : Fin m → ι, ∑ β : Fin n → ι,
          singlePush α β (projPush α β (tensorMap m n (diagHom ℚ ι V g) t)) :=
        (sum_singlePush_projPush _).symm
    _ = ∑ α : Fin m → ι, ∑ β : Fin n → ι, singlePush α β (projPush α β t) := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        rw [projPush_tensorMap, H.mem_hodgeGroup.1 hg m n _ (H.projPush_mem_hodgeClasses α β ht)]
    _ = t := sum_singlePush_projPush t

/-- **`diag (MT H) ≤ MT (H.pi ι)`** (with the same multiplier). -/
theorem diagHom_mem_mumfordTateGroup {g : V ≃ₗ[ℚ] V} (hg : g ∈ H.mumfordTateGroup) :
    diagHom ℚ ι V g ∈ (H.pi ι).mumfordTateGroup := by
  obtain ⟨c, hc⟩ := H.mem_mumfordTateGroup.1 hg
  refine (H.pi ι).mem_mumfordTateGroup.2 ⟨c, fun m n p hp t ht => ?_⟩
  calc tensorMap m n (diagHom ℚ ι V g) t
      = ∑ α : Fin m → ι, ∑ β : Fin n → ι,
          singlePush α β (projPush α β (tensorMap m n (diagHom ℚ ι V g) t)) :=
        (sum_singlePush_projPush _).symm
    _ = ∑ α : Fin m → ι, ∑ β : Fin n → ι,
          ((c ^ (-p) : ℚˣ) : ℚ) • singlePush α β (projPush α β t) := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        rw [projPush_tensorMap, hc m n p hp _ (H.projPush_mem_hodgeClasses α β ht), map_smul]
    _ = ((c ^ (-p) : ℚˣ) : ℚ) • ∑ α : Fin m → ι, ∑ β : Fin n → ι,
          singlePush α β (projPush α β t) := by
        simp only [Finset.smul_sum]
    _ = ((c ^ (-p) : ℚˣ) : ℚ) • t := by rw [sum_singlePush_projPush]

/-- **Elements of `MT (H.pi ι)` are block-diagonal with equal blocks**: every element of
`MT (H.pi ι)` commutes with the block endomorphisms (Hodge classes in `T 1 1`), hence is
`diag g₀`. -/
theorem exists_diagHom_eq_of_mem_mumfordTateGroup_pi [FiniteDimensional ℚ V] [Nonempty ι]
    {g : (ι → V) ≃ₗ[ℚ] (ι → V)} (hg : g ∈ (H.pi ι).mumfordTateGroup) :
    ∃ g₀ : V ≃ₗ[ℚ] V, diagHom ℚ ι V g₀ = g := by
  refine exists_eq_diagHom g fun i j x => ?_
  exact (H.pi ι).commute_of_mem_mumfordTateGroup (blockEnd ℚ V i j)
    (H.blockEnd_baseChange_pi_J i j) hg x

/-- **The block of an element of `MT (H.pi ι)` lies in `MT H`.** -/
theorem mem_mumfordTateGroup_of_diagHom_mem [Nonempty ι] {g : V ≃ₗ[ℚ] V}
    (hg : diagHom ℚ ι V g ∈ (H.pi ι).mumfordTateGroup) : g ∈ H.mumfordTateGroup := by
  obtain ⟨c, hc⟩ := (H.pi ι).mem_mumfordTateGroup.1 hg
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine H.mem_mumfordTateGroup.2 ⟨c, fun m n p hp s hs => ?_⟩
  have h := congrArg (projPush (R := ℚ) (X := V) (fun _ : Fin m => i₀) (fun _ : Fin n => i₀))
    (hc m n p hp _ (H.singlePush_mem_hodgeClasses (fun _ => i₀) (fun _ => i₀) hs))
  rwa [← singlePush_tensorMap, projPush_singlePush_const, map_smul,
    projPush_singlePush_const] at h

/-- **The block of an element of `Hdg (H.pi ι)` lies in `Hdg H`.** -/
theorem mem_hodgeGroup_of_diagHom_mem [Nonempty ι] {g : V ≃ₗ[ℚ] V}
    (hg : diagHom ℚ ι V g ∈ (H.pi ι).hodgeGroup) : g ∈ H.hodgeGroup := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine H.mem_hodgeGroup.2 fun m n s hs => ?_
  have h := congrArg (projPush (R := ℚ) (X := V) (fun _ : Fin m => i₀) (fun _ : Fin n => i₀))
    ((H.pi ι).mem_hodgeGroup.1 hg m n _
      (H.singlePush_mem_hodgeClasses (fun _ => i₀) (fun _ => i₀) hs))
  rwa [← singlePush_tensorMap, projPush_singlePush_const, projPush_singlePush_const] at h

variable (ι)

/-- **`MT (V^ι) = diag (MT V)`** for `ι` nonempty and `V` finite-dimensional. -/
theorem mumfordTateGroup_pi [FiniteDimensional ℚ V] [Nonempty ι] :
    (H.pi ι).mumfordTateGroup = H.mumfordTateGroup.map (diagHom ℚ ι V) := by
  ext g
  constructor
  · intro hg
    obtain ⟨g₀, rfl⟩ := H.exists_diagHom_eq_of_mem_mumfordTateGroup_pi hg
    exact Subgroup.mem_map.2 ⟨g₀, H.mem_mumfordTateGroup_of_diagHom_mem hg, rfl⟩
  · intro hg
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hg
    exact H.diagHom_mem_mumfordTateGroup hg₀

/-- **`Hdg (V^ι) = diag (Hdg V)`** for `ι` nonempty and `V` finite-dimensional. -/
theorem hodgeGroup_pi [FiniteDimensional ℚ V] [Nonempty ι] :
    (H.pi ι).hodgeGroup = H.hodgeGroup.map (diagHom ℚ ι V) := by
  ext g
  constructor
  · intro hg
    obtain ⟨g₀, rfl⟩ :=
      H.exists_diagHom_eq_of_mem_mumfordTateGroup_pi ((H.pi ι).hodgeGroup_le_mumfordTateGroup hg)
    exact Subgroup.mem_map.2 ⟨g₀, H.mem_hodgeGroup_of_diagHom_mem hg, rfl⟩
  · intro hg
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hg
    exact H.diagHom_mem_hodgeGroup hg₀

/-- **If `Hdg(V) = Sp(V, ψ)` then `Hdg(V^ι)` is the diagonal `Sp(V, ψ)`.** -/
theorem hodgeGroup_pi_eq_map_symplecticGroup [FiniteDimensional ℚ V] [Nonempty ι]
    (P : H.Polarization) (h : H.hodgeGroup = symplecticGroup P.form) :
    (H.pi ι).hodgeGroup = (symplecticGroup P.form).map (diagHom ℚ ι V) := by
  rw [hodgeGroup_pi, h]

/-- **If `MT(V) = GSp(V, ψ)` then `MT(V^ι)` is the diagonal `GSp(V, ψ)`.** -/
theorem mumfordTateGroup_pi_eq_map_similitudeGroup [FiniteDimensional ℚ V] [Nonempty ι]
    (P : H.Polarization) (h : H.mumfordTateGroup = similitudeGroup P.form) :
    (H.pi ι).mumfordTateGroup = (similitudeGroup P.form).map (diagHom ℚ ι V) := by
  rw [mumfordTateGroup_pi, h]

/-- **`Hdg (V^h) = diag (Hdg V)`** for `h ≥ 1`. -/
theorem hodgeGroup_pow [FiniteDimensional ℚ V] {h : ℕ} (hh : 0 < h) :
    (H.pow h).hodgeGroup = H.hodgeGroup.map (diagHom ℚ (Fin h) V) :=
  haveI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  H.hodgeGroup_pi (Fin h)

/-- **`MT (V^h) = diag (MT V)`** for `h ≥ 1`. -/
theorem mumfordTateGroup_pow [FiniteDimensional ℚ V] {h : ℕ} (hh : 0 < h) :
    (H.pow h).mumfordTateGroup = H.mumfordTateGroup.map (diagHom ℚ (Fin h) V) :=
  haveI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  H.mumfordTateGroup_pi (Fin h)

/-- **If `Hdg(V) = Sp(V, ψ)` then `Hdg(V^h)` is the diagonal `Sp(V, ψ)`** (`h ≥ 1`). -/
theorem hodgeGroup_pow_eq_map_symplecticGroup [FiniteDimensional ℚ V] {h : ℕ} (hh : 0 < h)
    (P : H.Polarization) (hP : H.hodgeGroup = symplecticGroup P.form) :
    (H.pow h).hodgeGroup = (symplecticGroup P.form).map (diagHom ℚ (Fin h) V) := by
  rw [hodgeGroup_pow H hh, hP]

/-- **If `MT(V) = GSp(V, ψ)` then `MT(V^h)` is the diagonal `GSp(V, ψ)`** (`h ≥ 1`). -/
theorem mumfordTateGroup_pow_eq_map_similitudeGroup [FiniteDimensional ℚ V] {h : ℕ}
    (hh : 0 < h) (P : H.Polarization) (hP : H.mumfordTateGroup = similitudeGroup P.form) :
    (H.pow h).mumfordTateGroup = (similitudeGroup P.form).map (diagHom ℚ (Fin h) V) := by
  rw [mumfordTateGroup_pow H hh, hP]

end Groups

end Power

end HodgeStructureNegOne

end ArithmeticOfJacobiPolynomials
