/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateRational
public import ArithmeticOfJacobiPolynomials.Algebra.RationalDescent
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.DirectSum.Module

/-!
# Tate modules of products of abelian groups (generic foundation)

Let `ℓ` be a prime. The Tate module `T_ℓ M = lim_n M[ℓ^n]` of
`ArithmeticOfJacobiPolynomials.Algebra.TateModule` commutes with products (an inverse limit of
products is the
product of the inverse limits), and the rational Tate module `V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M`
commutes with finite products. When a monoid `G` acts componentwise on a product, these
identifications are `G`-equivariant. For a diagonal power `M^ι = ι → M` (proof of Corollary 6.6
of the manuscript: "for powers, the groups act diagonally on direct sums") the representation on
`V_ℓ(M^ι)` is the diagonal representation on `⨁_{i ∈ ι} V_ℓ M`, so it has the same kernel as the
representation on `V_ℓ M` when `ι` is nonempty.

## Main definitions and results

* `tateModule.prodEquiv ℓ M N : T_ℓ(M × N) ≃ₗ[ℤ_ℓ] T_ℓ M × T_ℓ N`, equivariant for
  `Representation.prod` (`tateModule.prodEquiv_representation`);
* `tateModule.piEquiv ℓ M : T_ℓ(∀ i, M i) ≃ₗ[ℤ_ℓ] ∀ i, T_ℓ(M i)` (any index type), equivariant
  componentwise (`tateModule.piEquiv_representation`);
* `rationalTate.prodEquiv`, `rationalTate.piEquiv` (finite index type): the same for `V_ℓ`, with
  `rationalTate.prodEquiv_representation`, `rationalTate.piEquiv_representation`;
* `rationalTate.powEquivDirectSum ℓ ι M : V_ℓ(ι → M) ≃ₗ[ℚ_ℓ] ⨁_{i ∈ ι} V_ℓ M`, intertwining the
  representation on `V_ℓ(ι → M)` with `Representation.directSum fun _ => ρ`
  (`rationalTate.powEquivDirectSum_representation`);
* `rationalTate.ker_representation_pow`: for `ι` nonempty, the kernel of `G` acting on
  `V_ℓ(ι → M)` is the kernel of `G` acting on `V_ℓ M`; `rationalTate.ker_representation_fin_pow`
  for `M^h = Fin h → M`, `h ≥ 1`;
* `tateModule.mapEquiv_representation`, `rationalTate.mapEquiv`,
  `rationalTate.ker_representation_eq_of_addEquiv`: transport along an equivariant additive
  isomorphism.

This is generic: no group scheme, Jacobian or Galois group is treated here.
-/

public section

open PadicInt TensorProduct

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

/-- Two representations intertwined by a linear isomorphism have the same kernel. -/
theorem ker_representation_eq_of_linearEquiv {k G V W : Type*} [CommSemiring k] [Group G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W] (ρ : Representation k G V)
    (σ : Representation k G W) (e : V ≃ₗ[k] W) (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    ρ.ker = σ.ker := by
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    refine LinearMap.ext fun w => ?_
    have hw := he g (e.symm w)
    rw [h, Module.End.one_apply, LinearEquiv.apply_symm_apply] at hw
    rw [Module.End.one_apply]
    exact hw.symm
  · intro h
    refine LinearMap.ext fun v => e.injective ?_
    rw [he, h, Module.End.one_apply, Module.End.one_apply]

/-- Two representations with the same kernel have the same kernel as group homomorphisms to the
units of their endomorphism rings. -/
theorem ker_asGroupHom_eq_of_ker_eq {k G V W : Type*} [CommSemiring k] [Group G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W] {ρ : Representation k G V}
    {σ : Representation k G W} (h : ρ.ker = σ.ker) : ρ.asGroupHom.ker = σ.asGroupHom.ker := by
  ext g
  have hg : g ∈ ρ.ker ↔ g ∈ σ.ker := by rw [h]
  simp only [MonoidHom.mem_ker, Units.ext_iff, Representation.asGroupHom_apply,
    Units.val_one] at hg ⊢
  exact hg

/-- Two representations of a group with the same kernel have isomorphic images (in the unit
groups of the endomorphism rings). -/
theorem nonempty_range_asGroupHom_mulEquiv_of_ker_eq {k G V W : Type*} [CommSemiring k] [Group G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W] {ρ : Representation k G V}
    {σ : Representation k G W} (h : ρ.ker = σ.ker) :
    Nonempty (ρ.asGroupHom.range ≃* σ.asGroupHom.range) :=
  ⟨(QuotientGroup.quotientKerEquivRange _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_asGroupHom_eq_of_ker_eq h)).trans
      (QuotientGroup.quotientKerEquivRange _))⟩

section Prod

variable (ℓ : ℕ) [Fact ℓ.Prime] (M N : Type*) [AddCommGroup M] [AddCommGroup N]

/-- **The Tate module of a product.** `T_ℓ(M × N) ≃ T_ℓ M × T_ℓ N`, `x ↦ (T_ℓ pr₁ x, T_ℓ pr₂ x)`;
the inverse sends `(y, z)` to the sequence `n ↦ (y n, z n)`. -/
@[expose]
noncomputable def tateModule.prodEquiv :
    tateModule (M × N) ℓ ≃ₗ[ℤ_[ℓ]] tateModule M ℓ × tateModule N ℓ :=
  { (tateModuleMap ℓ (AddMonoidHom.fst M N)).prod (tateModuleMap ℓ (AddMonoidHom.snd M N)) with
    invFun := fun p => ⟨fun n => ((p.1 : ℕ → M) n, (p.2 : ℕ → N) n), mem_tateSubgroup.2
      ⟨Prod.ext (seq_zero p.1) (seq_zero p.2), fun n =>
        Prod.ext (smul_seq_succ p.1 n) (smul_seq_succ p.2 n)⟩⟩
    left_inv := fun _ => tateModule_ext fun _ => rfl
    right_inv := fun _ => Prod.ext (tateModule_ext fun _ => rfl) (tateModule_ext fun _ => rfl) }

variable {ℓ M N}

/-- The `n`-th component of the first coordinate of `tateModule.prodEquiv ℓ M N x` is
`(x n).1`. -/
@[simp]
theorem tateModule.prodEquiv_fst_seq (x : tateModule (M × N) ℓ) (n : ℕ) :
    (((tateModule.prodEquiv ℓ M N x).1 : tateModule M ℓ) : ℕ → M) n = ((x : ℕ → M × N) n).1 :=
  rfl

/-- The `n`-th component of the second coordinate of `tateModule.prodEquiv ℓ M N x` is
`(x n).2`. -/
@[simp]
theorem tateModule.prodEquiv_snd_seq (x : tateModule (M × N) ℓ) (n : ℕ) :
    (((tateModule.prodEquiv ℓ M N x).2 : tateModule N ℓ) : ℕ → N) n = ((x : ℕ → M × N) n).2 :=
  rfl

/-- The `n`-th component of `(tateModule.prodEquiv ℓ M N).symm p` is `(p.1 n, p.2 n)`. -/
@[simp]
theorem tateModule.prodEquiv_symm_seq (p : tateModule M ℓ × tateModule N ℓ) (n : ℕ) :
    (((tateModule.prodEquiv ℓ M N).symm p : tateModule (M × N) ℓ) : ℕ → M × N) n =
      ((p.1 : ℕ → M) n, (p.2 : ℕ → N) n) :=
  rfl

variable (G : Type*) [Monoid G] [DistribMulAction G M] [DistribMulAction G N]

/-- **Equivariance.** For `G` acting componentwise on `M × N`, the isomorphism
`T_ℓ(M × N) ≃ T_ℓ M × T_ℓ N` intertwines the representation on `T_ℓ(M × N)` with the product
representation. -/
theorem tateModule.prodEquiv_representation (g : G) (x : tateModule (M × N) ℓ) :
    tateModule.prodEquiv ℓ M N (tateModule.representation ℓ (M × N) G g x) =
      ((tateModule.representation ℓ M G).prod (tateModule.representation ℓ N G)) g
        (tateModule.prodEquiv ℓ M N x) := by
  rw [Representation.prod_apply_apply]
  refine Prod.ext (tateModule_ext fun n => ?_) (tateModule_ext fun n => ?_)
  · simp only [tateModule.prodEquiv_fst_seq, tateModule.representation_seq, Prod.smul_fst]
  · simp only [tateModule.prodEquiv_snd_seq, tateModule.representation_seq, Prod.smul_snd]

variable (ℓ M N)

/-- **The rational Tate module of a product.** `V_ℓ(M × N) ≃ V_ℓ M × V_ℓ N`, the scalar extension
of `tateModule.prodEquiv` followed by `ℚ_ℓ ⊗ (T × T') ≃ (ℚ_ℓ ⊗ T) × (ℚ_ℓ ⊗ T')`. -/
@[expose]
noncomputable def rationalTate.prodEquiv :
    rationalTate ℓ (M × N) ≃ₗ[ℚ_[ℓ]] rationalTate ℓ M × rationalTate ℓ N :=
  ((tateModule.prodEquiv ℓ M N).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).trans
    (TensorProduct.prodRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] (tateModule M ℓ) (tateModule N ℓ))

variable {ℓ M N}

/-- `rationalTate.prodEquiv (a ⊗ x) = (a ⊗ x₁, a ⊗ x₂)` where `(x₁, x₂)` is the image of `x` in
`T_ℓ M × T_ℓ N`. -/
theorem rationalTate.prodEquiv_tmul (a : ℚ_[ℓ]) (x : tateModule (M × N) ℓ) :
    rationalTate.prodEquiv ℓ M N (a ⊗ₜ x) =
      (a ⊗ₜ (tateModule.prodEquiv ℓ M N x).1, a ⊗ₜ (tateModule.prodEquiv ℓ M N x).2) := by
  rw [rationalTate.prodEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    TensorProduct.prodRight_tmul]

/-- **Equivariance.** The isomorphism `V_ℓ(M × N) ≃ V_ℓ M × V_ℓ N` intertwines the representation
on `V_ℓ(M × N)` with the product of the representations on `V_ℓ M` and `V_ℓ N`. -/
theorem rationalTate.prodEquiv_representation (g : G) (v : rationalTate ℓ (M × N)) :
    rationalTate.prodEquiv ℓ M N (rationalTate.representation ℓ (M × N) G g v) =
      ((rationalTate.representation ℓ M G).prod (rationalTate.representation ℓ N G)) g
        (rationalTate.prodEquiv ℓ M N v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [rationalTate.representation_tmul, rationalTate.prodEquiv_tmul,
      tateModule.prodEquiv_representation, Representation.prod_apply_apply]
  | add v w hv hw => simp only [map_add, hv, hw]

end Prod

section Pi

variable (ℓ : ℕ) [Fact ℓ.Prime] {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)]

/-- **The Tate module of a product.** `T_ℓ(∀ i, M i) ≃ ∀ i, T_ℓ(M i)` for an arbitrary index type,
`x ↦ (T_ℓ pr_i x)_i`; the inverse sends `(y_i)_i` to the sequence `n ↦ (y_i n)_i`. -/
@[expose]
noncomputable def tateModule.piEquiv :
    tateModule (∀ i, M i) ℓ ≃ₗ[ℤ_[ℓ]] ∀ i, tateModule (M i) ℓ :=
  { LinearMap.pi fun i => tateModuleMap ℓ (Pi.evalAddMonoidHom M i) with
    invFun := fun p => ⟨fun n i => (p i : ℕ → M i) n, mem_tateSubgroup.2
      ⟨funext fun i => seq_zero (p i),
        fun n => funext fun i => smul_seq_succ (p i) n⟩⟩
    left_inv := fun _ => tateModule_ext fun _ => rfl
    right_inv := fun _ => funext fun _ => tateModule_ext fun _ => rfl }

variable {ℓ M}

/-- The `n`-th component of the `i`-th coordinate of `tateModule.piEquiv ℓ M x` is `x n i`. -/
@[simp]
theorem tateModule.piEquiv_seq (x : tateModule (∀ i, M i) ℓ) (i : ι) (n : ℕ) :
    ((tateModule.piEquiv ℓ M x i : tateModule (M i) ℓ) : ℕ → M i) n =
      (x : ℕ → ∀ i, M i) n i :=
  rfl

/-- The `n`-th component of `(tateModule.piEquiv ℓ M).symm p` is `(p i n)_i`. -/
@[simp]
theorem tateModule.piEquiv_symm_seq (p : ∀ i, tateModule (M i) ℓ) (n : ℕ) :
    (((tateModule.piEquiv ℓ M).symm p : tateModule (∀ i, M i) ℓ) : ℕ → ∀ i, M i) n =
      fun i => (p i : ℕ → M i) n :=
  rfl

variable (G : Type*) [Monoid G] [∀ i, DistribMulAction G (M i)]

/-- **Equivariance.** For `G` acting componentwise on `∀ i, M i`, the `i`-th coordinate of the
image of `g • x` under `T_ℓ(∀ i, M i) ≃ ∀ i, T_ℓ(M i)` is `g` applied to the `i`-th coordinate of
the image of `x`. -/
theorem tateModule.piEquiv_representation (g : G) (x : tateModule (∀ i, M i) ℓ) (i : ι) :
    tateModule.piEquiv ℓ M (tateModule.representation ℓ (∀ i, M i) G g x) i =
      tateModule.representation ℓ (M i) G g (tateModule.piEquiv ℓ M x i) :=
  tateModule_ext fun n => by
    simp only [tateModule.piEquiv_seq, tateModule.representation_seq, Pi.smul_apply]

variable (ℓ M) [Fintype ι] [DecidableEq ι]

/-- **The rational Tate module of a finite product.** `V_ℓ(∀ i, M i) ≃ ∀ i, V_ℓ(M i)` for a finite
index type: the scalar extension of `tateModule.piEquiv` followed by
`ℚ_ℓ ⊗ (∀ i, T_i) ≃ ∀ i, ℚ_ℓ ⊗ T_i`. -/
@[expose]
noncomputable def rationalTate.piEquiv :
    rationalTate ℓ (∀ i, M i) ≃ₗ[ℚ_[ℓ]] ∀ i, rationalTate ℓ (M i) :=
  ((tateModule.piEquiv ℓ M).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).trans
    (TensorProduct.piRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] fun i => tateModule (M i) ℓ)

variable {ℓ M}

/-- `rationalTate.piEquiv (a ⊗ x) = (a ⊗ x_i)_i` where `(x_i)_i` is the image of `x` in
`∀ i, T_ℓ(M i)`. -/
theorem rationalTate.piEquiv_tmul (a : ℚ_[ℓ]) (x : tateModule (∀ i, M i) ℓ) :
    rationalTate.piEquiv ℓ M (a ⊗ₜ x) = fun i => a ⊗ₜ tateModule.piEquiv ℓ M x i := by
  rw [rationalTate.piEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]

/-- **Equivariance.** The `i`-th coordinate of the image of `g • v` under
`V_ℓ(∀ i, M i) ≃ ∀ i, V_ℓ(M i)` is `g` applied to the `i`-th coordinate of the image of `v`. -/
theorem rationalTate.piEquiv_representation (g : G) (v : rationalTate ℓ (∀ i, M i)) (i : ι) :
    rationalTate.piEquiv ℓ M (rationalTate.representation ℓ (∀ i, M i) G g v) i =
      rationalTate.representation ℓ (M i) G g (rationalTate.piEquiv ℓ M v i) := by
  induction v using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [rationalTate.representation_tmul, rationalTate.piEquiv_tmul,
      tateModule.piEquiv_representation]
  | add v w hv hw => simp only [map_add, Pi.add_apply, hv, hw]

end Pi

section Power

variable (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type*) [Fintype ι] [DecidableEq ι] (M : Type*)
  [AddCommGroup M]

omit [DecidableEq ι] in
/-- The `i`-th coordinate of `(DirectSum.linearEquivFunOnFintype R ι V).symm f` is `f i`. -/
private theorem linearEquivFunOnFintype_symm_apply {R : Type*} [Semiring R] {V : ι → Type*}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)] (f : ∀ i, V i) (i : ι) :
    (DirectSum.linearEquivFunOnFintype R ι V).symm f i = f i :=
  (DirectSum.linearEquivFunOnFintype_apply R ι V _ i).symm.trans
    (congrFun ((DirectSum.linearEquivFunOnFintype R ι V).apply_symm_apply f) i)

/-- **The rational Tate module of a power, as a direct sum.**
`V_ℓ(ι → M) ≃ ∀ i, V_ℓ M ≃ ⨁_{i ∈ ι} V_ℓ M` for a finite index type `ι`. -/
@[expose]
noncomputable def rationalTate.powEquivDirectSum :
    rationalTate ℓ (ι → M) ≃ₗ[ℚ_[ℓ]] DirectSum ι fun _ => rationalTate ℓ M :=
  (rationalTate.piEquiv ℓ fun _ : ι => M).trans
    (DirectSum.linearEquivFunOnFintype ℚ_[ℓ] ι fun _ => rationalTate ℓ M).symm

variable {ℓ ι M}

/-- The `i`-th coordinate of `rationalTate.powEquivDirectSum ℓ ι M v` is the `i`-th coordinate
of `rationalTate.piEquiv ℓ (fun _ => M) v`. -/
theorem rationalTate.powEquivDirectSum_apply (v : rationalTate ℓ (ι → M)) (i : ι) :
    rationalTate.powEquivDirectSum ℓ ι M v i = rationalTate.piEquiv ℓ (fun _ : ι => M) v i := by
  rw [rationalTate.powEquivDirectSum, LinearEquiv.trans_apply]
  exact linearEquivFunOnFintype_symm_apply ι _ i

variable (G : Type*) [Monoid G] [DistribMulAction G M]

/-- **For powers, the group acts diagonally on the direct sum.** Under
`V_ℓ(ι → M) ≃ ⨁_{i ∈ ι} V_ℓ M`, the representation of `G` on `V_ℓ(ι → M)` (for the diagonal action
of `G` on `ι → M`) is the diagonal representation `Representation.directSum fun _ => ρ`, where
`ρ` is the representation of `G` on `V_ℓ M`. -/
theorem rationalTate.powEquivDirectSum_representation (g : G) (v : rationalTate ℓ (ι → M)) :
    rationalTate.powEquivDirectSum ℓ ι M (rationalTate.representation ℓ (ι → M) G g v) =
      Representation.directSum (fun _ : ι => rationalTate.representation ℓ M G) g
        (rationalTate.powEquivDirectSum ℓ ι M v) := by
  refine DirectSum.ext fun i => ?_
  rw [Representation.directSum_apply, DirectSum.lmap_apply,
    rationalTate.powEquivDirectSum_apply, rationalTate.powEquivDirectSum_apply]
  exact rationalTate.piEquiv_representation (M := fun _ : ι => M) G g v i

omit [Fintype ι] [DecidableEq ι] in
/-- **Kernel of the diagonal action on a power.** For `G` a group and `ι` a nonempty finite type,
the kernel of the representation of `G` on `V_ℓ(ι → M)` equals the kernel of the representation
of `G` on `V_ℓ M`. -/
theorem rationalTate.ker_representation_pow (G : Type*) [Group G] [DistribMulAction G M]
    [Finite ι] [Nonempty ι] :
    (rationalTate.representation ℓ (ι → M) G).ker = (rationalTate.representation ℓ M G).ker := by
  classical
  have := Fintype.ofFinite ι
  exact (ker_representation_eq_of_linearEquiv _ _ (rationalTate.powEquivDirectSum ℓ ι M)
    (rationalTate.powEquivDirectSum_representation G)).trans
      (ker_directSum_const (rationalTate.representation ℓ M G))

/-- **Kernel of the diagonal action on `M^h`.** For `h ≥ 1`, the kernel of the representation of
a group `G` on `V_ℓ(M^h) = V_ℓ(Fin h → M)` equals the kernel of its representation on `V_ℓ M`. -/
theorem rationalTate.ker_representation_fin_pow (G : Type*) [Group G] [DistribMulAction G M]
    {h : ℕ} (hh : 0 < h) :
    (rationalTate.representation ℓ (Fin h → M) G).ker =
      (rationalTate.representation ℓ M G).ker :=
  haveI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  rationalTate.ker_representation_pow G

end Power

section Transport

variable (ℓ : ℕ) [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The `ℚ_ℓ`-linear isomorphism `V_ℓ M ≃ V_ℓ N` induced by an additive isomorphism
`e : M ≃+ N`: the scalar extension of `tateModule.mapEquiv ℓ e`. -/
@[expose]
noncomputable def rationalTate.mapEquiv (e : M ≃+ N) :
    rationalTate ℓ M ≃ₗ[ℚ_[ℓ]] rationalTate ℓ N :=
  (tateModule.mapEquiv ℓ e).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _

variable {ℓ}

/-- `rationalTate.mapEquiv ℓ e (a ⊗ x) = a ⊗ T_ℓ e x`. -/
theorem rationalTate.mapEquiv_tmul (e : M ≃+ N) (a : ℚ_[ℓ]) (x : tateModule M ℓ) :
    rationalTate.mapEquiv ℓ e (a ⊗ₜ x) = a ⊗ₜ tateModule.mapEquiv ℓ e x := by
  rw [rationalTate.mapEquiv, LinearEquiv.baseChange_tmul]

variable (G : Type*) [Monoid G] [DistribMulAction G M] [DistribMulAction G N]

/-- An equivariant additive isomorphism `e : M ≃+ N` induces an equivariant isomorphism of Tate
modules. -/
theorem tateModule.mapEquiv_representation (e : M ≃+ N)
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) (g : G) (x : tateModule M ℓ) :
    tateModule.mapEquiv ℓ e (tateModule.representation ℓ M G g x) =
      tateModule.representation ℓ N G g (tateModule.mapEquiv ℓ e x) :=
  tateModule_ext fun n => by
    simp only [tateModule.mapEquiv_seq, tateModule.representation_seq, he]

/-- An equivariant additive isomorphism `e : M ≃+ N` induces an equivariant isomorphism of
rational Tate modules. -/
theorem rationalTate.mapEquiv_representation (e : M ≃+ N)
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) (g : G) (v : rationalTate ℓ M) :
    rationalTate.mapEquiv ℓ e (rationalTate.representation ℓ M G g v) =
      rationalTate.representation ℓ N G g (rationalTate.mapEquiv ℓ e v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [rationalTate.representation_tmul, rationalTate.mapEquiv_tmul,
      tateModule.mapEquiv_representation G e he]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Groups acting on `M` and `N` compatibly with an additive isomorphism `e : M ≃+ N` act on
`V_ℓ M` and `V_ℓ N` with the same kernel. -/
theorem rationalTate.ker_representation_eq_of_addEquiv (G : Type*) [Group G]
    [DistribMulAction G M] [DistribMulAction G N] (e : M ≃+ N)
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) :
    (rationalTate.representation ℓ M G).ker = (rationalTate.representation ℓ N G).ker :=
  ker_representation_eq_of_linearEquiv _ _ (rationalTate.mapEquiv ℓ e)
    (rationalTate.mapEquiv_representation G e he)

end Transport

end ArithmeticOfJacobiPolynomials
