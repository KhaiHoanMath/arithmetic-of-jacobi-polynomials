/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateRational
public import ArithmeticOfJacobiPolynomials.Algebra.TateTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The topology of the rational Tate module and continuity of the rational representation

Let `M` be an `ℓ`-divisible abelian group with `M[ℓ^n] ≃ (ℤ/ℓ^n)^r` for all `n` (explicit
hypotheses), so that `T_ℓ M` is free of rank `r` over `ℤ_ℓ`. We give
`V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M` its module topology over `ℚ_ℓ` (`moduleTopology`, the standard
topology of a finite-dimensional `ℚ_ℓ`-vector space) and prove:

* `tateModule.isModuleTopology`: the inverse-limit topology of `T_ℓ M` is the module
  topology over `ℤ_ℓ` (a continuous bijection from the compact module topology to the Hausdorff
  inverse-limit topology);
* `rationalTate.continuous_ofTate`: `x ↦ 1 ⊗ x : T_ℓ M → V_ℓ M` is continuous;
* `rationalTate.continuous_representation_apply`: each `ρ_ℚ(g)` is continuous;
* `rationalTate.continuous_representation`: if the stabilisers of the `ℓ^n`-torsion points of `M`
  are open (the torsion-stabilizer hypothesis), the action map `G × V_ℓ M → V_ℓ M` is jointly
  continuous.

The topology on `V_ℓ M` is a definition (`moduleTopology`), independent of choices; bases are used
only inside proofs. Generic: no specific group is treated.
-/

public section

open PadicInt TensorProduct Topology

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M]

/-- The inverse-limit topology of `T_ℓ M` is Hausdorff. -/
instance tateModule.instT2Space : T2Space (tateModule M ℓ) := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, (x : ℕ → M) n ≠ (y : ℕ → M) n := by
    by_contra h
    push Not at h
    exact hxy (Subtype.ext (funext h))
  refine ⟨{z | (z : ℕ → M) n = (x : ℕ → M) n}, {z | (z : ℕ → M) n = (y : ℕ → M) n},
    tateModule.isOpen_setOf_seq_eq n _, tateModule.isOpen_setOf_seq_eq n _, rfl, rfl, ?_⟩
  rw [Set.disjoint_left]
  intro z hz hz'
  exact hn (hz.symm.trans hz')

variable {r : ℕ} (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
  (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
include hdiv htors

omit hdiv htors in
/-- `T_ℓ M` with its `ℤ_ℓ`-module topology (a type synonym used in the proof below). -/
def TateModTop (ℓ : ℕ) (M : Type*) [AddCommGroup M] : Type _ := tateModule M ℓ

omit hdiv htors in
noncomputable instance : AddCommGroup (TateModTop ℓ M) :=
  inferInstanceAs (AddCommGroup (tateModule M ℓ))

omit hdiv htors in
noncomputable instance : Module ℤ_[ℓ] (TateModTop ℓ M) :=
  inferInstanceAs (Module ℤ_[ℓ] (tateModule M ℓ))

omit hdiv htors in
noncomputable instance : TopologicalSpace (TateModTop ℓ M) := moduleTopology ℤ_[ℓ] _

omit hdiv htors in
instance : IsModuleTopology ℤ_[ℓ] (TateModTop ℓ M) := ⟨rfl⟩

/-- **The inverse-limit topology of `T_ℓ M` is its `ℤ_ℓ`-module topology** (under the explicit
divisibility and torsion hypotheses making `T_ℓ M` finite free). -/
theorem tateModule.isModuleTopology : IsModuleTopology ℤ_[ℓ] (tateModule M ℓ) := by
  have := module_finite_tateModule hdiv htors
  have : Module.Finite ℤ_[ℓ] (TateModTop ℓ M) := this
  have : ContinuousAdd (TateModTop ℓ M) := IsModuleTopology.toContinuousAdd ℤ_[ℓ] _
  have : CompactSpace (TateModTop ℓ M) := Module.Finite.compactSpace ℤ_[ℓ] _
  -- the module topology is finer than the inverse-limit topology
  have hle : moduleTopology ℤ_[ℓ] (tateModule M ℓ) ≤
      (inferInstance : TopologicalSpace (tateModule M ℓ)) := moduleTopology_le ℤ_[ℓ] _
  let e : TateModTop ℓ M ≃ tateModule M ℓ := Equiv.refl _
  have hc : Continuous e :=
    ⟨fun s hs => TopologicalSpace.le_def.mp hle s hs⟩
  -- a continuous bijection from a compact space onto a Hausdorff space is a homeomorphism
  have hinv : Continuous (hc.homeoOfEquivCompactToT2 (f := e)).symm :=
    (hc.homeoOfEquivCompactToT2 (f := e)).symm.continuous
  exact IsModuleTopology.of_continuous_id hinv

omit hdiv htors in
/-- The module topology on `V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M` (the standard topology of a
finite-dimensional `ℚ_ℓ`-vector space). -/
noncomputable instance rationalTate.instTopologicalSpace :
    TopologicalSpace (rationalTate ℓ M) :=
  moduleTopology ℚ_[ℓ] (rationalTate ℓ M)

omit hdiv htors in
instance rationalTate.isModuleTopology : IsModuleTopology ℚ_[ℓ] (rationalTate ℓ M) := ⟨rfl⟩

omit hdiv htors in
instance rationalTate.instContinuousAdd : ContinuousAdd (rationalTate ℓ M) :=
  IsModuleTopology.toContinuousAdd ℚ_[ℓ] _

omit hdiv htors in
instance rationalTate.instContinuousSMulPadicInt :
    ContinuousSMul ℤ_[ℓ] (rationalTate ℓ M) := by
  refine ⟨?_⟩
  have h1 : Continuous fun p : ℤ_[ℓ] × rationalTate ℓ M => ((p.1 : ℚ_[ℓ]), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have h2 := (continuous_smul : Continuous fun p : ℚ_[ℓ] × rationalTate ℓ M => p.1 • p.2).comp h1
  refine h2.congr fun p => ?_
  exact (algebraMap_smul ℚ_[ℓ] p.1 p.2)

/-- **`x ↦ 1 ⊗ x : T_ℓ M → V_ℓ M` is continuous.** -/
theorem rationalTate.continuous_ofTate : Continuous (rationalTate.ofTate ℓ M) := by
  have := tateModule.isModuleTopology hdiv htors
  exact IsModuleTopology.continuous_of_linearMap
    ((rationalTate.ofTate ℓ M).restrictScalars ℤ_[ℓ])

omit hdiv htors in
/-- Each `ρ_ℚ(g)` is continuous. -/
theorem rationalTate.continuous_representation_apply (G : Type*) [Monoid G]
    [DistribMulAction G M] (g : G) :
    Continuous (rationalTate.representation ℓ M G g) :=
  IsModuleTopology.continuous_of_linearMap _

/-- **Joint continuity of the rational representation.** If the stabiliser of every
`ℓ^n`-torsion point of `M` is open, the action map `G × V_ℓ M → V_ℓ M` is continuous. -/
theorem rationalTate.continuous_representation (G : Type*) [Group G] [TopologicalSpace G]
    [ContinuousMul G] [DistribMulAction G M]
    (hcont : ∀ n (P : M), ℓ ^ n • P = 0 → IsOpen (MulAction.stabilizer G P : Set G)) :
    Continuous fun p : G × rationalTate ℓ M => rationalTate.representation ℓ M G p.1 p.2 := by
  have := module_free_tateModule hdiv htors
  have := module_finite_tateModule hdiv htors
  let b := Module.Free.chooseBasis ℤ_[ℓ] (tateModule M ℓ)
  let B := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hρ := tateModule.continuous_representation (ℓ := ℓ) (M := M) (G := G) hcont
  have hof := rationalTate.continuous_ofTate hdiv htors
  -- `ρ(g) v = ∑ᵢ (B.coord i v) • (1 ⊗ ρ(g) bᵢ)`
  have key : ∀ (g : G) (v : rationalTate ℓ M), rationalTate.representation ℓ M G g v =
      ∑ i, B.coord i v • rationalTate.ofTate ℓ M (tateModule.representation ℓ M G g (b i)) := by
    intro g v
    conv_lhs => rw [← B.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.TensorProduct.basis_apply, rationalTate.representation_tmul,
      Module.Basis.coord_apply]
    rfl
  have hcoord : ∀ i, Continuous fun v : rationalTate ℓ M => B.coord i v :=
    fun i => IsModuleTopology.continuous_of_linearMap _
  exact (continuous_finsetSum _ fun i _ => ((hcoord i).comp continuous_snd).smul
    (hof.comp (hρ.comp (continuous_fst.prodMk continuous_const)))).congr
    fun p => (key p.1 p.2).symm

end ArithmeticOfJacobiPolynomials
