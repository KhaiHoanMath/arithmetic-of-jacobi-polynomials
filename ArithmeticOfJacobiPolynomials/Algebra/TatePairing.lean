/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateCyclotomic
public import ArithmeticOfJacobiPolynomials.Algebra.SymplecticSimilitude
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Tate-level pairings from compatible finite-level pairings (generic)

Let `M`, `N` be abelian groups and `ℓ` a prime. Given pairings
`e n : M[ℓ^n] × M[ℓ^n] → N[ℓ^n]` (biadditive) compatible with the transition maps,
`e_{ℓ^n}(ℓ x, ℓ y) = ℓ • e_{ℓ^{n+1}}(x, y)` (in multiplicative notation
`e_{ℓ^{n+1}}(x, y)^ℓ = e_{ℓ^n}(ℓ x, ℓ y)`, the compatibility of the Weil pairings), we build the
`ℤ_ℓ`-bilinear pairing `T_ℓ M × T_ℓ M → T_ℓ N` on the Tate modules of
`ArithmeticOfJacobiPolynomials.Algebra.TateModule`, and its scalar extension to the rational Tate
modules
`V_ℓ = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ`. In the application `N = Additive Lˣ`, so that `T_ℓ N = ℤ_ℓ(1)` is the
Tate twist of `ArithmeticOfJacobiPolynomials.Algebra.TateCyclotomic` and `V_ℓ N = ℚ_ℓ(1)`.

This is a **generic** construction: no Jacobian, abelian variety or Weil pairing of any specific
group is constructed or asserted; the finite-level pairings and their properties are explicit
inputs.

## Main definitions

* `ArithmeticOfJacobiPolynomials.torsionTransition ℓ n : M[ℓ^(n+1)] →+ M[ℓ^n]`, multiplication by
`ℓ`;
* `ArithmeticOfJacobiPolynomials.IsCompatibleTorsionPairing ℓ e`: `e n (ℓ x) (ℓ y) = ℓ • e (n + 1)
x y`;
* `ArithmeticOfJacobiPolynomials.tatePairing e he : T_ℓ M →ₗ[ℤ_ℓ] T_ℓ M →ₗ[ℤ_ℓ] T_ℓ N`, with
  `tatePairing_seq`: `(tatePairing e he x y) n = e n (x mod ℓ^n) (y mod ℓ^n)`;
* `ArithmeticOfJacobiPolynomials.rationalTatePairing e he : V_ℓ M →ₗ[ℚ_ℓ] V_ℓ M →ₗ[ℚ_ℓ] V_ℓ N`, the
base change
  (`LinearMap.BilinMap.baseChange`), with `rationalTatePairing_tmul`;
* `ArithmeticOfJacobiPolynomials.rationalTate.autRepresentation`: the action of a group on `V_ℓ M`
by
  `ℚ_ℓ`-linear automorphisms;
* `ArithmeticOfJacobiPolynomials.rationalTate.similitudeRepresentation`: the induced homomorphism
into the
  similitude group `GSp(V_ℓ M, ψ)` of `ArithmeticOfJacobiPolynomials.Algebra.SymplecticSimilitude`.

## Main results

* `isAlt_tatePairing`, `isAlt_rationalTatePairing`: alternating finite-level pairings give
  alternating pairings on `T_ℓ` and `V_ℓ`;
* `tatePairing_representation`, `rationalTatePairing_representation`: equivariant finite-level
  pairings give equivariant pairings, `ψ (g x) (g y) = g (ψ x y)`;
* `rationalTatePairing_representation_eq_smul`,
  `rationalTate.autRepresentation_mem_similitudeGroup`,
  `similitudeMultiplier_similitudeRepresentation`: if `G` acts on `T_ℓ N` through a character
  `χ : G → ℤ_ℓˣ`, every `g` acts on `V_ℓ M` as a similitude of `ψ` with multiplier `χ g`;
* `rationalTatePairing_galois_eq_cyclotomicCharacter_smul`,
  `similitudeMultiplier_galoisSimilitudeRepresentation`: for values in `ℤ_ℓ(1) = T_ℓ(L^×)`
  (`L` algebraically closed, `ℓ ≠ 0` in `L`), the multiplier of `σ ∈ Aut(L/K)` is the
  cyclotomic character `cyclotomicCharacter L ℓ σ`.
-/

public section

open PadicInt TensorProduct

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

section BaseChange

variable {R A P Q : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

/-- The base change of an alternating bilinear map is skew-symmetric. -/
theorem bilinMap_baseChange_apply_swap (B : P →ₗ[R] P →ₗ[R] Q) (hB : LinearMap.IsAlt B)
    (z w : A ⊗[R] P) :
    LinearMap.BilinMap.baseChange (A := A) B z w =
      -LinearMap.BilinMap.baseChange (A := A) B w z := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, neg_add]
  | tmul a x =>
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, neg_add]
    | tmul b y =>
      rw [LinearMap.BilinMap.baseChange_tmul, LinearMap.BilinMap.baseChange_tmul,
        ← LinearMap.IsAlt.neg hB x y, TensorProduct.tmul_neg, neg_neg, mul_comm]

/-- **The base change of an alternating bilinear map is alternating.** -/
theorem bilinMap_baseChange_isAlt (B : P →ₗ[R] P →ₗ[R] Q) (hB : LinearMap.IsAlt B) :
    LinearMap.IsAlt (LinearMap.BilinMap.baseChange (A := A) B) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.BilinMap.baseChange_tmul, LinearMap.IsAlt.self_eq_zero hB x,
      TensorProduct.tmul_zero]
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂, zero_add, add_zero]
    rw [bilinMap_baseChange_apply_swap B hB z₁ z₂, add_neg_cancel]

/-- **Base change of an equivariance.** If `B (f x) (f y) = h (B x y)`, the same holds after base
change: `B_A (f_A z) (f_A w) = h_A (B_A z w)`. -/
theorem bilinMap_baseChange_map_map (B : P →ₗ[R] P →ₗ[R] Q) (f : P →ₗ[R] P) (h : Q →ₗ[R] Q)
    (hB : ∀ x y, B (f x) (f y) = h (B x y)) (z w : A ⊗[R] P) :
    LinearMap.BilinMap.baseChange (A := A) B (f.baseChange A z) (f.baseChange A w) =
      h.baseChange A (LinearMap.BilinMap.baseChange (A := A) B z w) := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a x =>
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.BilinMap.baseChange_tmul, LinearMap.BilinMap.baseChange_tmul, hB,
        LinearMap.baseChange_tmul]

/-- If `f` is multiplication by the scalar `c`, so is its base change (by the image of `c`). -/
theorem baseChange_apply_of_eq_smul (f : Q →ₗ[R] Q) (c : R) (hf : ∀ z, f z = c • z)
    (w : A ⊗[R] Q) : f.baseChange A w = algebraMap R A c • w := by
  induction w using TensorProduct.inductionOn with
  | tmul a z => rw [LinearMap.baseChange_tmul, hf, TensorProduct.tmul_smul, algebraMap_smul]
  | add w₁ w₂ h₁ h₂ => rw [map_add, h₁, h₂, smul_add]

end BaseChange

section Transition

variable (ℓ : ℕ) {M : Type*} [AddCommGroup M]

/-- The transition map `M[ℓ^(n+1)] →+ M[ℓ^n]`, multiplication by `ℓ`. -/
@[expose]
def torsionTransition (n : ℕ) :
    AddSubgroup.torsionBy M ((ℓ ^ (n + 1) : ℕ) : ℤ) →+ AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ)
    where
  toFun x := ⟨ℓ • (x : M), AddSubgroup.torsionBy.nsmul_iff.2 (by
    rw [smul_smul, ← pow_succ]
    exact AddSubgroup.torsionBy.nsmul_iff.1 x.2)⟩
  map_zero' := Subtype.ext (smul_zero ℓ)
  map_add' x y := Subtype.ext (smul_add ℓ (x : M) y)

variable {ℓ}

/-- `torsionTransition ℓ n x = ℓ • x` on underlying elements. -/
@[simp]
theorem coe_torsionTransition (n : ℕ) (x : AddSubgroup.torsionBy M ((ℓ ^ (n + 1) : ℕ) : ℤ)) :
    (torsionTransition ℓ n x : M) = ℓ • (x : M) :=
  rfl

/-- The reductions of an element of `T_ℓ M` are compatible with the transition maps. -/
theorem torsionTransition_tateReduction (n : ℕ) (x : tateModule M ℓ) :
    torsionTransition ℓ n (tateReduction ℓ (n + 1) x) = tateReduction ℓ n x :=
  Subtype.ext (smul_seq_succ x n)

/-- An element of `M[ℓ^0] = M[1]` is zero. -/
theorem coe_eq_zero_of_mem_torsionBy_pow_zero (z : AddSubgroup.torsionBy M ((ℓ ^ 0 : ℕ) : ℤ)) :
    (z : M) = 0 := by
  exact (one_smul ℕ (z : M)).symm.trans
    ((congrArg (· • (z : M)) (pow_zero ℓ).symm).trans (AddSubgroup.torsionBy.nsmul_iff.1 z.2))

end Transition

section Pairing

variable (ℓ : ℕ) {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- **Compatibility of finite-level pairings** `e n : M[ℓ^n] × M[ℓ^n] → N[ℓ^n]` with the
transition maps: `e n (ℓ x) (ℓ y) = ℓ • e (n + 1) x y` (multiplicatively,
`e_{ℓ^n}(ℓ x, ℓ y) = e_{ℓ^{n+1}}(x, y)^ℓ`). -/
@[expose]
def IsCompatibleTorsionPairing
    (e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ)) :
    Prop :=
  ∀ n x y, e n (torsionTransition ℓ n x) (torsionTransition ℓ n y) =
    torsionTransition ℓ n (e (n + 1) x y)

variable {ℓ} in
/-- The compatibility on underlying elements: `e n (ℓ x) (ℓ y) = ℓ • e (n + 1) x y`. -/
theorem IsCompatibleTorsionPairing.coe_eq
    {e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ)}
    (he : IsCompatibleTorsionPairing ℓ e) (n : ℕ)
    (x y : AddSubgroup.torsionBy M ((ℓ ^ (n + 1) : ℕ) : ℤ)) :
    (e n (torsionTransition ℓ n x) (torsionTransition ℓ n y) : N) =
      ℓ • (e (n + 1) x y : N) :=
  congrArg Subtype.val (he n x y)

/-- **Equivariance of finite-level pairings** for actions of a monoid `G` on `M` and `N`:
`e n (g x) (g y) = g (e n x y)`. -/
@[expose]
def IsEquivariantTorsionPairing (G : Type*) [Monoid G] [DistribMulAction G M]
    [DistribMulAction G N]
    (e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ)) :
    Prop :=
  ∀ (g : G) n x y, e n (torsionMap (DistribSMul.toAddMonoidHom M g) _ x)
      (torsionMap (DistribSMul.toAddMonoidHom M g) _ y) =
    torsionMap (DistribSMul.toAddMonoidHom N g) _ (e n x y)

variable {ℓ} [Fact ℓ.Prime]
  (e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ))
  (he : IsCompatibleTorsionPairing ℓ e)

/-- The reduction of `a • x` modulo `ℓ^n`, as a torsion element. -/
theorem tateReduction_smul' (n : ℕ) (a : ℤ_[ℓ]) (x : tateModule M ℓ) :
    tateReduction ℓ n (a • x) = (toZModPow n a).val • tateReduction ℓ n x :=
  Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact coe_tateReduction_smul n a x)

/-- The underlying function of `tatePairing`: `(x, y) ↦ (e n (x mod ℓ^n) (y mod ℓ^n))_n`. -/
@[expose]
def tatePairingFun (x y : tateModule M ℓ) : tateModule N ℓ :=
  ⟨fun n => (e n (tateReduction ℓ n x) (tateReduction ℓ n y) : N), mem_tateSubgroup.2
    ⟨coe_eq_zero_of_mem_torsionBy_pow_zero _, fun n => by
      have h := he.coe_eq n (tateReduction ℓ (n + 1) x) (tateReduction ℓ (n + 1) y)
      rw [torsionTransition_tateReduction, torsionTransition_tateReduction] at h
      exact h.symm⟩⟩

omit [Fact ℓ.Prime] in
/-- The `n`-th component of `tatePairingFun e he x y`. -/
theorem tatePairingFun_seq (x y : tateModule M ℓ) (n : ℕ) :
    ((tatePairingFun e he x y : tateModule N ℓ) : ℕ → N) n =
      (e n (tateReduction ℓ n x) (tateReduction ℓ n y) : N) :=
  rfl

/-- **The Tate pairing** `T_ℓ M × T_ℓ M → T_ℓ N` induced by compatible finite-level pairings
`e n : M[ℓ^n] × M[ℓ^n] → N[ℓ^n]`: `(x, y) ↦ (e n (x mod ℓ^n) (y mod ℓ^n))_n`. It is
`ℤ_ℓ`-bilinear. -/
@[expose]
noncomputable def tatePairing :
    tateModule M ℓ →ₗ[ℤ_[ℓ]] tateModule M ℓ →ₗ[ℤ_[ℓ]] tateModule N ℓ :=
  LinearMap.mk₂ ℤ_[ℓ] (tatePairingFun e he)
    (fun x x' y => by
      ext n
      simp only [tatePairingFun_seq, map_add, AddMonoidHom.add_apply, AddSubgroup.coe_add,
        Pi.add_apply])
    (fun a x y => by
      ext n
      rw [smul_seq, tatePairingFun_seq, tatePairingFun_seq, tateReduction_smul',
        map_nsmul, AddMonoidHom.nsmul_apply, AddSubgroup.coe_nsmul])
    (fun x y y' => by
      ext n
      simp only [tatePairingFun_seq, map_add, AddSubgroup.coe_add, Pi.add_apply])
    (fun a x y => by
      ext n
      rw [smul_seq, tatePairingFun_seq, tatePairingFun_seq, tateReduction_smul',
        map_nsmul, AddSubgroup.coe_nsmul])

/-- **Evaluation formula:** the `n`-th component of `tatePairing e he x y` is
`e n (x mod ℓ^n) (y mod ℓ^n)`. -/
theorem tatePairing_seq (x y : tateModule M ℓ) (n : ℕ) :
    ((tatePairing e he x y : tateModule N ℓ) : ℕ → N) n =
      (e n (tateReduction ℓ n x) (tateReduction ℓ n y) : N) :=
  rfl

/-- The reduction of `tatePairing e he x y` modulo `ℓ^n` is `e n (x mod ℓ^n) (y mod ℓ^n)`. -/
theorem tateReduction_tatePairing (x y : tateModule M ℓ) (n : ℕ) :
    tateReduction ℓ n (tatePairing e he x y) = e n (tateReduction ℓ n x) (tateReduction ℓ n y) :=
  rfl

variable {e he}

/-- **Alternating.** If every `e n` is alternating, so is the Tate pairing. -/
theorem tatePairing_self (halt : ∀ n z, e n z z = 0) (x : tateModule M ℓ) :
    tatePairing e he x x = 0 := by
  ext n
  exact congrArg Subtype.val (halt n (tateReduction ℓ n x))

/-- If every `e n` is alternating, the Tate pairing is alternating (`LinearMap.IsAlt`). -/
theorem isAlt_tatePairing (halt : ∀ n z, e n z z = 0) : LinearMap.IsAlt (tatePairing e he) :=
  tatePairing_self halt

/-- The reduction of `g • x` is `g` applied to the reduction of `x`. -/
theorem tateReduction_representation' {G : Type*} [Monoid G] [DistribMulAction G M] (n : ℕ)
    (g : G) (x : tateModule M ℓ) :
    tateReduction ℓ n (tateModule.representation ℓ M G g x) =
      torsionMap (DistribSMul.toAddMonoidHom M g) _ (tateReduction ℓ n x) :=
  rfl

/-- **Equivariance.** If every `e n` is `G`-equivariant, so is the Tate pairing:
`tatePairing e he (g x) (g y) = g (tatePairing e he x y)`. -/
theorem tatePairing_representation {G : Type*} [Monoid G] [DistribMulAction G M]
    [DistribMulAction G N] (heq : IsEquivariantTorsionPairing ℓ G e) (g : G)
    (x y : tateModule M ℓ) :
    tatePairing e he (tateModule.representation ℓ M G g x)
        (tateModule.representation ℓ M G g y) =
      tateModule.representation ℓ N G g (tatePairing e he x y) := by
  ext n
  rw [tatePairing_seq, tateModule.representation_seq, tatePairing_seq,
    tateReduction_representation', tateReduction_representation', heq g n, coe_torsionMap,
    DistribSMul.toAddMonoidHom_apply]

variable (e he)

/-- **The rational Tate pairing** `V_ℓ M × V_ℓ M → V_ℓ N`, the `ℚ_ℓ`-bilinear base change of
`tatePairing e he` to `V_ℓ = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ`. -/
@[expose]
noncomputable def rationalTatePairing :
    rationalTate ℓ M →ₗ[ℚ_[ℓ]] rationalTate ℓ M →ₗ[ℚ_[ℓ]] rationalTate ℓ N :=
  LinearMap.BilinMap.baseChange (A := ℚ_[ℓ]) (tatePairing e he)

/-- `rationalTatePairing e he (a ⊗ x) (b ⊗ y) = (a b) ⊗ tatePairing e he x y`. -/
theorem rationalTatePairing_tmul (a b : ℚ_[ℓ]) (x y : tateModule M ℓ) :
    rationalTatePairing e he (a ⊗ₜ x) (b ⊗ₜ y) = (a * b) ⊗ₜ tatePairing e he x y :=
  by rw [rationalTatePairing, LinearMap.BilinMap.baseChange_tmul]

/-- On `T_ℓ M ⊆ V_ℓ M`, the rational Tate pairing restricts to the Tate pairing. -/
theorem rationalTatePairing_ofTate (x y : tateModule M ℓ) :
    rationalTatePairing e he (rationalTate.ofTate ℓ M x) (rationalTate.ofTate ℓ M y) =
      rationalTate.ofTate ℓ N (tatePairing e he x y) := by
  rw [rationalTate.ofTate_apply, rationalTate.ofTate_apply, rationalTate.ofTate_apply,
    rationalTatePairing_tmul, one_mul]

variable {e he}

/-- **Alternating.** If every `e n` is alternating, so is the rational Tate pairing. -/
theorem isAlt_rationalTatePairing (halt : ∀ n z, e n z z = 0) :
    LinearMap.IsAlt (rationalTatePairing e he) :=
  bilinMap_baseChange_isAlt _ (isAlt_tatePairing halt)

/-- If every `e n` is alternating, `rationalTatePairing e he z z = 0`. -/
theorem rationalTatePairing_self (halt : ∀ n z, e n z z = 0) (z : rationalTate ℓ M) :
    rationalTatePairing e he z z = 0 :=
  LinearMap.IsAlt.self_eq_zero (isAlt_rationalTatePairing halt) z

/-- **Equivariance.** If every `e n` is `G`-equivariant, so is the rational Tate pairing. -/
theorem rationalTatePairing_representation {G : Type*} [Monoid G] [DistribMulAction G M]
    [DistribMulAction G N] (heq : IsEquivariantTorsionPairing ℓ G e) (g : G)
    (x y : rationalTate ℓ M) :
    rationalTatePairing e he (rationalTate.representation ℓ M G g x)
        (rationalTate.representation ℓ M G g y) =
      rationalTate.representation ℓ N G g (rationalTatePairing e he x y) := by
  simp only [rationalTate.representation_apply]
  exact bilinMap_baseChange_map_map _ _ _ (tatePairing_representation heq g) x y

/-- **The Galois action through a character.** If `G` acts on `T_ℓ N` by a character
`χ : G → ℤ_ℓˣ` (`g • z = χ g • z`), then
`rationalTatePairing e he (g x) (g y) = χ g • rationalTatePairing e he x y`. -/
theorem rationalTatePairing_representation_eq_smul {G : Type*} [Monoid G]
    [DistribMulAction G M] [DistribMulAction G N] (heq : IsEquivariantTorsionPairing ℓ G e)
    (χ : G → ℤ_[ℓ]ˣ) (hχ : ∀ g z, tateModule.representation ℓ N G g z = (χ g : ℤ_[ℓ]) • z)
    (g : G) (x y : rationalTate ℓ M) :
    rationalTatePairing e he (rationalTate.representation ℓ M G g x)
        (rationalTate.representation ℓ M G g y) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] (χ g) • rationalTatePairing e he x y := by
  rw [rationalTatePairing_representation heq, rationalTate.representation_apply]
  exact baseChange_apply_of_eq_smul _ _ (hχ g) _

end Pairing

section Similitude

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [AddCommGroup M] (G : Type*) [Group G]
  [DistribMulAction G M]

/-- The action of a group `G` on `V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M` by `ℚ_ℓ`-linear automorphisms, the
base change of `tateModule.autRepresentation`. -/
@[expose]
noncomputable def rationalTate.autRepresentation :
    G →* (rationalTate ℓ M ≃ₗ[ℚ_[ℓ]] rationalTate ℓ M) where
  toFun g := (tateModule.autRepresentation ℓ M G g).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _
  map_one' := by simp only [_root_.map_one, LinearEquiv.baseChange_one]
  map_mul' g h := by simp only [_root_.map_mul, LinearEquiv.baseChange_mul]

variable {ℓ M G}

/-- `rationalTate.autRepresentation` is the base change of `tateModule.autRepresentation`. -/
theorem rationalTate.autRepresentation_eq (g : G) :
    rationalTate.autRepresentation ℓ M G g =
      (tateModule.autRepresentation ℓ M G g).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ :=
  rfl

/-- The automorphism `rationalTate.autRepresentation ℓ M G g` acts as
`rationalTate.representation ℓ M G g`. -/
theorem rationalTate.autRepresentation_apply (g : G) (z : rationalTate ℓ M) :
    rationalTate.autRepresentation ℓ M G g z = rationalTate.representation ℓ M G g z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    rw [rationalTate.autRepresentation_eq, LinearEquiv.baseChange_tmul,
      rationalTate.representation_tmul]
    exact congrArg (a ⊗ₜ ·) (LinearMap.congr_fun (tateModule.coe_autRepresentation g) x)
  | add z w hz hw => rw [map_add, map_add, hz, hw]

variable {N : Type*} [AddCommGroup N] [DistribMulAction G N]
  {e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ)}
  {he : IsCompatibleTorsionPairing ℓ e}

/-- **Similitudes.** If the finite-level pairings are `G`-equivariant and `G` acts on `T_ℓ N`
through a character `χ : G → ℤ_ℓˣ`, then every `g ∈ G` acts on `V_ℓ M` as an element of the
similitude group `GSp(V_ℓ M, ψ)` of `ψ = rationalTatePairing e he` (with multiplier `χ g`). -/
theorem rationalTate.autRepresentation_mem_similitudeGroup
    (heq : IsEquivariantTorsionPairing ℓ G e) (χ : G → ℤ_[ℓ]ˣ)
    (hχ : ∀ g z, tateModule.representation ℓ N G g z = (χ g : ℤ_[ℓ]) • z) (g : G) :
    rationalTate.autRepresentation ℓ M G g ∈ similitudeGroup (rationalTatePairing e he) :=
  mem_similitudeGroup.2 ⟨Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom (χ g), fun x y => by
    rw [rationalTate.autRepresentation_apply, rationalTate.autRepresentation_apply,
      Units.coe_map]
    exact rationalTatePairing_representation_eq_smul heq χ hχ g x y⟩

/-- The homomorphism `G →* GSp(V_ℓ M, ψ)` of `rationalTate.autRepresentation_mem_similitudeGroup`,
for `ψ = rationalTatePairing e he`. -/
@[expose]
noncomputable def rationalTate.similitudeRepresentation (heq : IsEquivariantTorsionPairing ℓ G e)
    (χ : G → ℤ_[ℓ]ˣ) (hχ : ∀ g z, tateModule.representation ℓ N G g z = (χ g : ℤ_[ℓ]) • z) :
    G →* similitudeGroup (rationalTatePairing e he) :=
  (rationalTate.autRepresentation ℓ M G).codRestrict _
    (rationalTate.autRepresentation_mem_similitudeGroup heq χ hχ)

/-- The underlying automorphism of `rationalTate.similitudeRepresentation heq χ hχ g`. -/
theorem rationalTate.coe_similitudeRepresentation (heq : IsEquivariantTorsionPairing ℓ G e)
    (χ : G → ℤ_[ℓ]ˣ) (hχ : ∀ g z, tateModule.representation ℓ N G g z = (χ g : ℤ_[ℓ]) • z)
    (g : G) :
    (rationalTate.similitudeRepresentation (he := he) heq χ hχ g :
        rationalTate ℓ M ≃ₗ[ℚ_[ℓ]] rationalTate ℓ M) =
      rationalTate.autRepresentation ℓ M G g :=
  rfl

/-- **The multiplier is the character.** For `ψ = rationalTatePairing e he ≠ 0`, the multiplier
of `g` acting on `V_ℓ M` is `χ g` (viewed in `ℚ_ℓˣ`). -/
theorem similitudeMultiplier_similitudeRepresentation (heq : IsEquivariantTorsionPairing ℓ G e)
    (χ : G → ℤ_[ℓ]ˣ) (hχ : ∀ g z, tateModule.representation ℓ N G g z = (χ g : ℤ_[ℓ]) • z)
    (hψ : rationalTatePairing e he ≠ 0) (g : G) :
    similitudeMultiplier _ hψ (rationalTate.similitudeRepresentation (he := he) heq χ hχ g) =
      Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom (χ g) :=
  similitudeMultiplier_eq hψ _ fun x y => by
    rw [rationalTate.coe_similitudeRepresentation, rationalTate.autRepresentation_apply,
      rationalTate.autRepresentation_apply, Units.coe_map]
    exact rationalTatePairing_representation_eq_smul heq χ hχ g x y

end Similitude

section TateTwist

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M] {K L : Type*} [Field K] [Field L]
  [Algebra K L] [DistribMulAction (L ≃ₐ[K] L) M]
  {e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy (Additive Lˣ) ((ℓ ^ n : ℕ) : ℤ)}
  {he : IsCompatibleTorsionPairing ℓ e}

/-- The Galois action on `ℤ_ℓ(1) = T_ℓ(L^×)` is through the cyclotomic character (for `L`
algebraically closed with `(ℓ : L) ≠ 0`), in the form used by the similitude results. -/
theorem tateModule.representation_units_eq_cyclotomicCharacter [IsAlgClosed L]
    (hℓL : (ℓ : L) ≠ 0) (σ : L ≃ₐ[K] L) (z : tateTwist ℓ L) :
    tateModule.representation ℓ (Additive Lˣ) (L ≃ₐ[K] L) σ z =
      ((cyclotomicCharacter L ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • z :=
  tateTwist.representation_eq_cyclotomicCharacter hℓL σ z

/-- **Weil-type pairings with values in `ℚ_ℓ(1)`.** Let `L` be algebraically closed with
`(ℓ : L) ≠ 0` and let the finite-level pairings `e n : M[ℓ^n] × M[ℓ^n] → μ_{ℓ^n}(L)` be
compatible and `Aut(L/K)`-equivariant. Then for `ψ = rationalTatePairing e he` with values in
`V_ℓ(L^×) = ℚ_ℓ(1)`, `ψ (σ x) (σ y) = χ_ℓ(σ) • ψ x y`, with `χ_ℓ` the cyclotomic character. -/
theorem rationalTatePairing_galois_eq_cyclotomicCharacter_smul [IsAlgClosed L]
    (hℓL : (ℓ : L) ≠ 0) (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e) (σ : L ≃ₐ[K] L)
    (x y : rationalTate ℓ M) :
    rationalTatePairing e he (rationalTate.representation ℓ M (L ≃ₐ[K] L) σ x)
        (rationalTate.representation ℓ M (L ≃ₐ[K] L) σ y) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] (cyclotomicCharacter L ℓ σ.toRingEquiv) •
        rationalTatePairing e he x y :=
  rationalTatePairing_representation_eq_smul heq
    (fun τ => cyclotomicCharacter L ℓ τ.toRingEquiv)
    (tateModule.representation_units_eq_cyclotomicCharacter hℓL) σ x y

/-- **`Aut(L/K)` acts on `V_ℓ M` by similitudes of the Weil-type pairing**, as a homomorphism
`Aut(L/K) →* GSp(V_ℓ M, ψ)`. -/
@[expose]
noncomputable def galoisSimilitudeRepresentation [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0)
    (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e) :
    (L ≃ₐ[K] L) →* similitudeGroup (rationalTatePairing e he) :=
  rationalTate.similitudeRepresentation heq (fun τ => cyclotomicCharacter L ℓ τ.toRingEquiv)
    (tateModule.representation_units_eq_cyclotomicCharacter hℓL)

/-- The underlying automorphism of `galoisSimilitudeRepresentation hℓL heq σ` is the action of
`σ` on `V_ℓ M`. -/
theorem coe_galoisSimilitudeRepresentation_apply [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0)
    (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e) (σ : L ≃ₐ[K] L)
    (z : rationalTate ℓ M) :
    (galoisSimilitudeRepresentation (he := he) hℓL heq σ :
        rationalTate ℓ M ≃ₗ[ℚ_[ℓ]] rationalTate ℓ M) z =
      rationalTate.representation ℓ M (L ≃ₐ[K] L) σ z :=
  rationalTate.autRepresentation_apply σ z

/-- **The multiplier is the cyclotomic character.** If `ψ = rationalTatePairing e he ≠ 0`, the
multiplier of `σ ∈ Aut(L/K)` acting on `V_ℓ M` is `χ_ℓ(σ) ∈ ℤ_ℓˣ ⊆ ℚ_ℓˣ`. -/
theorem similitudeMultiplier_galoisSimilitudeRepresentation [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0)
    (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e) (hψ : rationalTatePairing e he ≠ 0)
    (σ : L ≃ₐ[K] L) :
    similitudeMultiplier _ hψ (galoisSimilitudeRepresentation (he := he) hℓL heq σ) =
      Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom (cyclotomicCharacter L ℓ σ.toRingEquiv) :=
  similitudeMultiplier_similitudeRepresentation heq
    (fun τ => cyclotomicCharacter L ℓ τ.toRingEquiv)
    (tateModule.representation_units_eq_cyclotomicCharacter hℓL) hψ σ

end TateTwist

end ArithmeticOfJacobiPolynomials
