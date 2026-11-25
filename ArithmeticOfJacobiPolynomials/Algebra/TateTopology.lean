/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateAction
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The inverse-limit topology on the `ℓ`-adic Tate module (generic foundation)

Let `M` be an abelian group and `ℓ` a prime. The Tate module `T_ℓ M = lim_n M[ℓ^n]` of
`ArithmeticOfJacobiPolynomials.Algebra.TateModule` carries the inverse-limit topology: the coarsest
topology for
which every evaluation `x ↦ x n : T_ℓ M → M[ℓ^n]` is continuous, each torsion group `M[ℓ^n]`
(and `M` itself) being discrete. Equivalently, a map into `T_ℓ M` is continuous iff each of its
components is locally constant (`tateModule.continuous_iff`).

## Main definitions and results

* `ArithmeticOfJacobiPolynomials.tateModule.instTopologicalSpace`: the topology
  `⨅ n, induced (x ↦ x n) ⊥` (`tateModule.topologicalSpace_eq`), characterised as the coarsest
  topology making the components discrete-valued continuous maps (`tateModule.le_iff`);
* `tateModule.isLocallyConstant_seq`, `isLocallyConstant_tateReduction`,
  `continuous_tateReduction`: the evaluations are continuous into the discrete `M[ℓ^n]`;
* instances `ContinuousAdd`, `ContinuousNeg`, `IsTopologicalAddGroup` and
  `ContinuousSMul ℤ_[ℓ] (tateModule M ℓ)` (with the `ℓ`-adic topology on `ℤ_[ℓ]`), using
  `isLocallyConstant_toZModPow`;
* `tateModule.continuous_map`: `T_ℓ f` is continuous for every additive map `f`;
* `tateModule.continuous_representation`: for a group `G` with a topology making multiplication
  continuous, acting on `M` by additive maps such that the stabiliser of every `ℓ^n`-torsion point
  is open (an explicit hypothesis, i.e. continuity of `G × M[ℓ^n] → M[ℓ^n]` for the discrete
  `M[ℓ^n]`), the action map `G × T_ℓ M → T_ℓ M` of `tateModule.representation` is continuous;
* `tateModule.distribMulAction` (a scoped instance, `open scoped
ArithmeticOfJacobiPolynomials.TateAction`) and
  `tateModule.continuousSMul`: the same statement as `ContinuousSMul G (tateModule M ℓ)`.

This is generic: no specific group, Galois group or group scheme is treated, and no continuity is
postulated: the open-stabiliser condition is an explicit hypothesis of the action results.

## Implementation notes

The topology is a global instance on `tateModule M ℓ`. Since `tateModule M ℓ` is (reducibly) a
subtype of `ℕ → M`, it should not be used together with a topology on `M` itself, which would
produce a second (subspace) topology instance. The action of `G` is not a global instance either,
as it would overlap the `ℕ`- and `ℤ`-actions of the additive group `T_ℓ M`.
-/

public section

open PadicInt Topology Filter

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

section Topology

variable {ℓ : ℕ} {M : Type*} [AddCommGroup M]

/-- The inverse-limit topology on `T_ℓ M = lim_n M[ℓ^n]`: the coarsest topology making every
evaluation `x ↦ x n` continuous into `M` with the discrete topology. -/
noncomputable instance tateModule.instTopologicalSpace : TopologicalSpace (tateModule M ℓ) :=
  ⨅ n, TopologicalSpace.induced (fun x : tateModule M ℓ => (x : ℕ → M) n) ⊥

/-- The topology of `T_ℓ M` is `⨅ n, induced (x ↦ x n) ⊥`. -/
theorem tateModule.topologicalSpace_eq :
    (tateModule.instTopologicalSpace : TopologicalSpace (tateModule M ℓ)) =
      ⨅ n, TopologicalSpace.induced (fun x : tateModule M ℓ => (x : ℕ → M) n) ⊥ :=
  rfl

/-- The topology of `T_ℓ M` is the coarsest topology for which all components `x ↦ x n` are
continuous into the discrete `M`: a topology `t` is finer than it iff all components are
`t`-continuous. -/
theorem tateModule.le_iff (t : TopologicalSpace (tateModule M ℓ)) :
    t ≤ tateModule.instTopologicalSpace ↔
      ∀ n, @Continuous (tateModule M ℓ) M t ⊥ (fun x => (x : ℕ → M) n) :=
  le_iInf_iff.trans (forall_congr' fun _ => continuous_iff_le_induced.symm)

/-- **Continuity into the Tate module.** A map `f : X → T_ℓ M` is continuous iff each component
`a ↦ f a n` is locally constant. -/
theorem tateModule.continuous_iff {X : Type*} [TopologicalSpace X] {f : X → tateModule M ℓ} :
    Continuous f ↔ ∀ n, IsLocallyConstant fun a => ((f a : tateModule M ℓ) : ℕ → M) n := by
  refine continuous_iInf_rng.trans (forall_congr' fun n => ?_)
  rw [continuous_induced_rng]
  exact (@IsLocallyConstant.iff_continuous _ _ _ ⊥ (discreteTopology_bot M) _).symm

/-- The components `x ↦ x n` of `T_ℓ M` are locally constant. -/
theorem tateModule.isLocallyConstant_seq (n : ℕ) :
    IsLocallyConstant fun x : tateModule M ℓ => (x : ℕ → M) n :=
  tateModule.continuous_iff.1 continuous_id n

/-- The sets `{x | x n = P}` are open in `T_ℓ M`. -/
theorem tateModule.isOpen_setOf_seq_eq (n : ℕ) (P : M) :
    IsOpen {x : tateModule M ℓ | (x : ℕ → M) n = P} :=
  tateModule.isLocallyConstant_seq n {P}

/-- The evaluation `T_ℓ M → M[ℓ^n]` is locally constant. -/
theorem isLocallyConstant_tateReduction (n : ℕ) :
    IsLocallyConstant (tateReduction (M := M) ℓ n) :=
  IsLocallyConstant.desc _ Subtype.val (tateModule.isLocallyConstant_seq n) Subtype.val_injective

/-- The evaluation `T_ℓ M → M[ℓ^n]` is continuous, `M[ℓ^n]` carrying the discrete topology. -/
theorem continuous_tateReduction (n : ℕ) :
    @Continuous (tateModule M ℓ) (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ)) _ ⊥
      (tateReduction ℓ n) := by
  let : TopologicalSpace (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ)) := ⊥
  exact (isLocallyConstant_tateReduction n).continuous

/-- Addition on `T_ℓ M` is continuous. -/
instance tateModule.instContinuousAdd : ContinuousAdd (tateModule M ℓ) :=
  ⟨tateModule.continuous_iff.2 fun n =>
    ((tateModule.isLocallyConstant_seq n).comp_continuous continuous_fst).comp₂
      ((tateModule.isLocallyConstant_seq n).comp_continuous continuous_snd) (· + ·)⟩

/-- Negation on `T_ℓ M` is continuous. -/
instance tateModule.instContinuousNeg : ContinuousNeg (tateModule M ℓ) :=
  ⟨tateModule.continuous_iff.2 fun n =>
    (tateModule.isLocallyConstant_seq n).comp fun P : M => -P⟩

/-- `T_ℓ M` is a topological additive group. -/
instance tateModule.instIsTopologicalAddGroup : IsTopologicalAddGroup (tateModule M ℓ) where
  continuous_add := continuous_add
  continuous_neg := continuous_neg

/-- The map `T_ℓ f : T_ℓ M → T_ℓ N` induced by an additive map is continuous. -/
theorem tateModule.continuous_map [Fact ℓ.Prime] {N : Type*} [AddCommGroup N] (f : M →+ N) :
    Continuous (tateModuleMap ℓ f) :=
  tateModule.continuous_iff.2 fun n => by
    exact (tateModule.isLocallyConstant_seq n).comp f

end Topology

section PadicInt

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M]

/-- The reduction `ℤ_ℓ → ℤ/ℓ^n` is locally constant for the `ℓ`-adic topology. -/
theorem isLocallyConstant_toZModPow (n : ℕ) :
    IsLocallyConstant (toZModPow n : ℤ_[ℓ] →+* ZMod (ℓ ^ n)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun a => ?_
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (-(n : ℤ)) := zpow_pos (Nat.cast_pos.2 hℓ.out.pos) _
  filter_upwards [Metric.ball_mem_nhds a hpos] with b hb
  have hmem : b - a ∈ (Ideal.span {(ℓ : ℤ_[ℓ]) ^ n} : Ideal ℤ_[ℓ]) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow (b - a) n).1
      (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hb).le)
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, _root_.map_sub, sub_eq_zero] at hmem
  exact hmem

/-- The scalar action `ℤ_ℓ × T_ℓ M → T_ℓ M` is continuous, `ℤ_ℓ` carrying its `ℓ`-adic
topology. -/
instance tateModule.instContinuousSMulPadicInt : ContinuousSMul ℤ_[ℓ] (tateModule M ℓ) :=
  ⟨tateModule.continuous_iff.2 fun n => by
    have h : IsLocallyConstant fun p : ℤ_[ℓ] × tateModule M ℓ =>
        (toZModPow n p.1).val • ((p.2 : tateModule M ℓ) : ℕ → M) n :=
      ((isLocallyConstant_toZModPow n).comp_continuous continuous_fst).comp₂
        ((tateModule.isLocallyConstant_seq n).comp_continuous continuous_snd)
        fun (c : ZMod (ℓ ^ n)) (P : M) => c.val • P
    simp only [smul_seq]
    exact h⟩

end PadicInt

section Representation

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M] {G : Type*}

/-- Each `ρ(g) : T_ℓ M → T_ℓ M` of `tateModule.representation` is continuous. -/
theorem tateModule.continuous_representation_apply [Monoid G] [DistribMulAction G M] (g : G) :
    Continuous (tateModule.representation ℓ M G g) := by
  rw [tateModule.representation_apply]
  exact tateModule.continuous_map _

variable [Group G] [TopologicalSpace G] [ContinuousMul G] [DistribMulAction G M]

/-- If the stabiliser of every `ℓ^n`-torsion point of `M` is open in `G`, then each component
`(g, x) ↦ g • x n` of the action on `T_ℓ M` is locally constant on `G × T_ℓ M`. -/
theorem tateModule.isLocallyConstant_representation_seq
    (hcont : ∀ n (P : M), ℓ ^ n • P = 0 → IsOpen (MulAction.stabilizer G P : Set G)) (n : ℕ) :
    IsLocallyConstant fun p : G × tateModule M ℓ =>
      ((tateModule.representation ℓ M G p.1 p.2 : tateModule M ℓ) : ℕ → M) n := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 ?_
  rintro ⟨g₀, x₀⟩
  have hU : IsOpen ((fun g : G => g₀⁻¹ * g) ⁻¹'
      (MulAction.stabilizer G ((x₀ : ℕ → M) n) : Set G)) :=
    (continuous_const.mul continuous_id).isOpen_preimage _
      (hcont n _ (pow_smul_seq x₀ n))
  have hg : ∀ᶠ g in 𝓝 g₀, g₀⁻¹ * g ∈ MulAction.stabilizer G ((x₀ : ℕ → M) n) :=
    hU.mem_nhds (by
      change g₀⁻¹ * g₀ ∈ MulAction.stabilizer G ((x₀ : ℕ → M) n)
      rw [inv_mul_cancel]
      exact one_mem _)
  have hx : ∀ᶠ x in 𝓝 x₀, ((x : tateModule M ℓ) : ℕ → M) n = (x₀ : ℕ → M) n :=
    (tateModule.isLocallyConstant_seq n).eventually_eq x₀
  refine (hg.prod_nhds hx).mono fun p hp => ?_
  obtain ⟨h1, h2⟩ := hp
  have h1' : (g₀⁻¹ * p.1) • (x₀ : ℕ → M) n = (x₀ : ℕ → M) n :=
    MulAction.mem_stabilizer_iff.1 h1
  simp only [tateModule.representation_seq]
  rw [h2]
  calc p.1 • (x₀ : ℕ → M) n = g₀ • ((g₀⁻¹ * p.1) • (x₀ : ℕ → M) n) := by
        rw [smul_smul, mul_inv_cancel_left]
    _ = g₀ • (x₀ : ℕ → M) n := by rw [h1']

/-- **Continuity of the representation on the Tate module.** Let a group `G` with a topology
making multiplication continuous act on `M` by additive maps, such that the stabiliser of every
`ℓ^n`-torsion point is open (i.e. `G × M[ℓ^n] → M[ℓ^n]` is continuous for the discrete
`M[ℓ^n]`). Then the action map `G × T_ℓ M → T_ℓ M`, `(g, x) ↦ ρ(g) x`, is continuous. -/
theorem tateModule.continuous_representation
    (hcont : ∀ n (P : M), ℓ ^ n • P = 0 → IsOpen (MulAction.stabilizer G P : Set G)) :
    Continuous fun p : G × tateModule M ℓ => tateModule.representation ℓ M G p.1 p.2 :=
  tateModule.continuous_iff.2 (tateModule.isLocallyConstant_representation_seq hcont)

end Representation

section Action

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [AddCommGroup M] (G : Type*)

/-- The action `g • x = ρ(g) x` of `G` on `T_ℓ M` given by `tateModule.representation`. It is a
scoped instance (`open scoped ArithmeticOfJacobiPolynomials.TateAction`), not a global one. -/
@[expose, reducible]
noncomputable def tateModule.distribMulAction [Monoid G] [DistribMulAction G M] :
    DistribMulAction G (tateModule M ℓ) :=
  DistribMulAction.compHom (tateModule M ℓ) (tateModule.representation ℓ M G)

namespace TateAction

attribute [scoped instance] ArithmeticOfJacobiPolynomials.tateModule.distribMulAction

end TateAction

open scoped TateAction

variable {ℓ M G}

/-- With the scoped action, `g • x = ρ(g) x`. -/
theorem tateModule.smul_def [Monoid G] [DistribMulAction G M] (g : G) (x : tateModule M ℓ) :
    g • x = tateModule.representation ℓ M G g x :=
  rfl

/-- With the scoped action, the `n`-th component of `g • x` is `g • x n`. -/
theorem tateModule.smul_seq_of_distribMulAction [Monoid G] [DistribMulAction G M] (g : G)
    (x : tateModule M ℓ) (n : ℕ) : ((g • x : tateModule M ℓ) : ℕ → M) n = g • (x : ℕ → M) n :=
  tateModule.representation_seq g x n

/-- **The representation on `T_ℓ M` is continuous** (as `ContinuousSMul`, for the scoped
action), provided the stabiliser of every `ℓ^n`-torsion point of `M` is open in `G`. -/
theorem tateModule.continuousSMul [Group G] [TopologicalSpace G] [ContinuousMul G]
    [DistribMulAction G M]
    (hcont : ∀ n (P : M), ℓ ^ n • P = 0 → IsOpen (MulAction.stabilizer G P : Set G)) :
    ContinuousSMul G (tateModule M ℓ) :=
  ⟨tateModule.continuous_representation hcont⟩

end Action

end ArithmeticOfJacobiPolynomials
