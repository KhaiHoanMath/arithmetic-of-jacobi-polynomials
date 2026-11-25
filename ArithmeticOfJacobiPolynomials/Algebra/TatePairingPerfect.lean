/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TatePairing
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Perfectness of Tate pairings induced by perfect finite-level pairings (generic)

Let `M`, `N` be abelian groups, `ℓ` a prime, and `e n : M[ℓ^n] × M[ℓ^n] → N[ℓ^n]` compatible
biadditive pairings (`ArithmeticOfJacobiPolynomials.IsCompatibleTorsionPairing`) inducing the Tate
pairing
`tatePairing e he : T_ℓ M × T_ℓ M → T_ℓ N` and its base change
`rationalTatePairing e he : V_ℓ M × V_ℓ M → V_ℓ N` of
`ArithmeticOfJacobiPolynomials.Algebra.TatePairing`.

Suppose the finite-level pairings are *perfect*: for every `n`, `x ↦ e n x` is injective
`M[ℓ^n] → Hom(M[ℓ^n], N[ℓ^n])`. We prove:

* `eq_zero_of_tatePairing_eq_zero`, `tatePairing_injective`: if `M` is `ℓ`-divisible, the map
  `T_ℓ M → Hom_{ℤ_ℓ}(T_ℓ M, T_ℓ N)` is injective;
* `tatePairing_surjective`, `tatePairing_bijective`: if moreover every `e n` is bijective it is
  bijective; `bijective_of_injective_of_torsionEquiv`: when `M[ℓ^n] ≅ (ℤ/ℓ^n)^r` and
  `N[ℓ^n] ≅ ℤ/ℓ^n`, injectivity of `e n` already implies bijectivity (counting), whence
  `tatePairing_bijective_of_injective` and the isomorphism `tatePairingEquiv`;
* `tateModule.eq_zero_of_smul_eq_zero`: `T_ℓ N` is torsion-free over `ℤ_ℓ`;
* `rationalTatePairing_nondegenerate`: the rational Tate pairing is nondegenerate,
  `∀ z, (∀ w, ψ z w = 0) → z = 0`, in the shape of `ne_zero_of_nondegenerate` and
  `ker_similitudeMultiplier_of_nondegenerate`; `rationalTatePairing_ne_zero`: `ψ ≠ 0` when
  `M[ℓ^n] ≅ (ℤ/ℓ^n)^r` with `r > 0`; `rationalTatePairing_bijective`: `V_ℓ M ≅ Hom(V_ℓ M, V_ℓ N)`
  when moreover `N[ℓ^n] ≅ ℤ/ℓ^n`;
* `ker_similitudeMultiplier_rationalTatePairing`: the kernel of the multiplier of
  `GSp(V_ℓ M, ψ)` is `Sp(V_ℓ M, ψ)`;
* for values in `ℤ_ℓ(1) = T_ℓ(L^×)` (`L` algebraically closed, `(ℓ : L) ≠ 0`):
  `similitudeMultiplier_galoisSimilitudeRepresentation_of_injective` (the multiplier of `σ` is the
  cyclotomic character `χ_ℓ(σ)`, with `ψ ≠ 0` discharged from perfectness) and
  `galoisSimilitudeRepresentation_mem_symplecticGroup_iff` (`σ` acts through `Sp(V_ℓ M, ψ)` iff
  `χ_ℓ(σ) = 1`).

This is **generic**: no Jacobian, abelian variety or Weil pairing of any specific group is
constructed, and perfectness of any specific pairing is not asserted; it is an explicit hypothesis.
-/

public section

open PadicInt TensorProduct

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

section TorsionFree

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M]

/-- **`T_ℓ M` is torsion-free over `ℤ_ℓ`:** if `a ≠ 0` and `a • x = 0`, then `x = 0`. -/
theorem tateModule.eq_zero_of_smul_eq_zero {a : ℤ_[ℓ]} (ha : a ≠ 0) {x : tateModule M ℓ}
    (h : a • x = 0) : x = 0 := by
  rw [PadicInt.unitCoeff_spec ha, mul_smul] at h
  have hk : ((ℓ : ℤ_[ℓ]) ^ a.valuation) • x = 0 :=
    (Units.isUnit (PadicInt.unitCoeff ha)).smul_eq_zero.1 h
  refine tateModule_ext fun n => ?_
  have h0 : (((ℓ : ℤ_[ℓ]) ^ a.valuation • x : tateModule M ℓ) : ℕ → M) (n + a.valuation) = 0 := by
    rw [hk]
    rfl
  rw [smul_seq, nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq x _)
    (natCast_val_toZModPow_pow _ _), pow_smul_seq_add] at h0
  exact h0.trans rfl

end TorsionFree

section Counting

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {q r : ℕ} [NeZero q]

/-- **Finite-level perfectness by counting.** If `A ≅ (ℤ/q)^r` and `B ≅ ℤ/q`, an injective map
`A → Hom(A, B)` is bijective (both sides have `q^r` elements). -/
theorem bijective_of_injective_of_torsionEquiv (eA : A ≃+ (Fin r → ZMod q))
    (eB : B ≃+ (Fin 1 → ZMod q)) {f : A → (A →+ B)} (hf : Function.Injective f) :
    Function.Bijective f := by
  let E : (A →+ B) ≃ A :=
    (((eA.addMonoidHomCongrLeftEquiv.trans eB.addMonoidHomCongrRightEquiv).trans
      (AddMonoidHom.toZModLinearMapEquiv (n := q)).toEquiv).trans
      ((LinearEquiv.piRing (ZMod q) (Fin 1 → ZMod q) (Fin r) (ZMod q)).toEquiv.trans
        (Equiv.arrowCongr (Equiv.refl (Fin r)) (Equiv.funUnique (Fin 1) (ZMod q))))).trans
      eA.symm.toEquiv
  have : Finite A := Finite.of_equiv _ eA.symm.toEquiv
  have : Finite (A →+ B) := Finite.of_equiv _ E.symm
  exact hf.bijective_of_nat_card_le (Nat.card_congr E).le

end Counting

section Perfect

variable {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ)}
  {he : IsCompatibleTorsionPairing ℓ e}

/-- **Left kernel of the Tate pairing.** If `M` is `ℓ`-divisible and every `x ↦ e n x` is
injective, then `tatePairing e he x y = 0` for all `y` forces `x = 0`. -/
theorem eq_zero_of_tatePairing_eq_zero (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (hperf : ∀ n, Function.Injective (e n)) (x : tateModule M ℓ)
    (hx : ∀ y, tatePairing e he x y = 0) : x = 0 := by
  refine tateModule.ext_tateReduction fun n => ?_
  rw [map_zero]
  refine (injective_iff_map_eq_zero (e n)).1 (hperf n) _ (AddMonoidHom.ext fun z => ?_)
  obtain ⟨y, rfl⟩ := tateReduction_surjective hdiv n z
  rw [← tateReduction_tatePairing e he, hx y, map_zero, AddMonoidHom.zero_apply]

/-- **The Tate pairing is perfect (injectivity).** If `M` is `ℓ`-divisible and every
`x ↦ e n x : M[ℓ^n] → Hom(M[ℓ^n], N[ℓ^n])` is injective, then
`T_ℓ M → Hom_{ℤ_ℓ}(T_ℓ M, T_ℓ N)`, `x ↦ tatePairing e he x`, is injective. -/
theorem tatePairing_injective (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (hperf : ∀ n, Function.Injective (e n)) : Function.Injective (tatePairing e he) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact eq_zero_of_tatePairing_eq_zero hdiv hperf x fun y => by rw [hx, LinearMap.zero_apply]

/-- A `ℤ_ℓ`-linear map `φ : T_ℓ M → T_ℓ N` induces `M[ℓ^n] →+ N[ℓ^n]` compatibly with the
reductions, when `M` is `ℓ`-divisible. -/
theorem exists_torsionHom_tateReduction (hdiv : ∀ x : M, ∃ y, ℓ • y = x) (n : ℕ)
    (φ : tateModule M ℓ →ₗ[ℤ_[ℓ]] tateModule N ℓ) :
    ∃ g : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ),
      ∀ y, g (tateReduction ℓ n y) = tateReduction ℓ n (φ y) := by
  have hker : (tateReduction (M := M) ℓ n).ker ≤
      ((tateReduction (M := N) ℓ n).comp φ.toAddMonoidHom).ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, tateReduction_eq_zero_iff]
    obtain ⟨y, -, rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ((tateReduction_eq_zero_iff n x).1 hx)
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  exact ⟨(tateReduction ℓ n).liftOfRightInverse _
      (Function.rightInverse_surjInv (tateReduction_surjective hdiv n)) ⟨_, hker⟩,
    fun y => AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ y⟩

/-- **The Tate pairing is perfect (surjectivity).** If `M` is `ℓ`-divisible and every
`e n : M[ℓ^n] → Hom(M[ℓ^n], N[ℓ^n])` is bijective, every `ℤ_ℓ`-linear map `T_ℓ M → T_ℓ N` is
`tatePairing e he x` for some `x`. -/
theorem tatePairing_surjective (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (hbij : ∀ n, Function.Bijective (e n)) : Function.Surjective (tatePairing e he) := by
  intro φ
  choose g hg using fun n => exists_torsionHom_tateReduction hdiv n φ
  choose x hx using fun n => (hbij n).2 (g n)
  have hcompat : ∀ n, torsionTransition ℓ n (x (n + 1)) = x n := by
    intro n
    refine (hbij n).1 (AddMonoidHom.ext fun z => ?_)
    obtain ⟨y, rfl⟩ := tateReduction_surjective hdiv n z
    rw [hx n, hg n, ← torsionTransition_tateReduction n y, he n, hx (n + 1), hg (n + 1),
      torsionTransition_tateReduction]
  refine ⟨⟨fun n => (x n : M), mem_tateSubgroup.2 ⟨coe_eq_zero_of_mem_torsionBy_pow_zero _,
    fun n => congrArg Subtype.val (hcompat n)⟩⟩, ?_⟩
  refine LinearMap.ext fun y => tateModule.ext_tateReduction fun n => ?_
  rw [tateReduction_tatePairing]
  change e n (x n) (tateReduction ℓ n y) = _
  rw [hx n, hg n]

/-- **The Tate pairing is perfect.** If `M` is `ℓ`-divisible and every
`e n : M[ℓ^n] → Hom(M[ℓ^n], N[ℓ^n])` is bijective, then
`T_ℓ M → Hom_{ℤ_ℓ}(T_ℓ M, T_ℓ N)` is bijective. -/
theorem tatePairing_bijective (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (hbij : ∀ n, Function.Bijective (e n)) : Function.Bijective (tatePairing e he) :=
  ⟨tatePairing_injective hdiv fun n => (hbij n).1, tatePairing_surjective hdiv hbij⟩

/-- **The Tate pairing is perfect, from injective finite-level pairings.** Let `M` be
`ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r`, let `N[ℓ^n] ≅ ℤ/ℓ^n`, and let every
`x ↦ e n x` be injective. Then `T_ℓ M → Hom_{ℤ_ℓ}(T_ℓ M, T_ℓ N)` is bijective. -/
theorem tatePairing_bijective_of_injective {r : ℕ} (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
    (htorsN : ∀ n, Nonempty (AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin 1 → ZMod (ℓ ^ n))))
    (hperf : ∀ n, Function.Injective (e n)) : Function.Bijective (tatePairing e he) :=
  tatePairing_bijective hdiv fun n =>
    bijective_of_injective_of_torsionEquiv (htors n).some (htorsN n).some (hperf n)

/-- The isomorphism `T_ℓ M ≃ Hom_{ℤ_ℓ}(T_ℓ M, T_ℓ N)`, `x ↦ tatePairing e he x`, of
`tatePairing_bijective_of_injective`. -/
@[expose]
noncomputable def tatePairingEquiv {r : ℕ} (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
    (htorsN : ∀ n, Nonempty (AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin 1 → ZMod (ℓ ^ n))))
    (hperf : ∀ n, Function.Injective (e n)) :
    tateModule M ℓ ≃ₗ[ℤ_[ℓ]] (tateModule M ℓ →ₗ[ℤ_[ℓ]] tateModule N ℓ) :=
  LinearEquiv.ofBijective (tatePairing e he)
    (tatePairing_bijective_of_injective hdiv htors htorsN hperf)

/-- `tatePairingEquiv` acts as `x ↦ tatePairing e he x`. -/
theorem tatePairingEquiv_apply {r : ℕ} (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
    (htorsN : ∀ n, Nonempty (AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin 1 → ZMod (ℓ ^ n))))
    (hperf : ∀ n, Function.Injective (e n)) (x : tateModule M ℓ) :
    tatePairingEquiv (he := he) hdiv htors htorsN hperf x = tatePairing e he x :=
  rfl

/-- **The rational Tate pairing is nondegenerate.** If `M` is `ℓ`-divisible and every
`x ↦ e n x` is injective, then `ψ = rationalTatePairing e he` on `V_ℓ M = ℚ_ℓ ⊗ T_ℓ M` satisfies
`∀ z, (∀ w, ψ z w = 0) → z = 0` (the hypothesis of `ne_zero_of_nondegenerate` and
`ker_similitudeMultiplier_of_nondegenerate`). -/
theorem rationalTatePairing_nondegenerate (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (hperf : ∀ n, Function.Injective (e n)) :
    ∀ z, (∀ w, rationalTatePairing e he z w = 0) → z = 0 := by
  intro z hz
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[ℓ])
    (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (tateModule M ℓ) 1) z
  have hs' : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) • z = rationalTate.ofTate ℓ M x := by
    rw [algebraMap_smul]
    exact hs
  have hx : x = 0 := by
    refine eq_zero_of_tatePairing_eq_zero (he := he) hdiv hperf x fun y => ?_
    have h1 : (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (tateModule N ℓ) 1) (tatePairing e he x y) = 0 := by
      change rationalTate.ofTate ℓ N (tatePairing e he x y) = 0
      rw [← rationalTatePairing_ofTate, ← hs', map_smul, LinearMap.smul_apply, hz, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (S := nonZeroDivisors ℤ_[ℓ])
      (f := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (tateModule N ℓ) 1)).1 h1
    exact tateModule.eq_zero_of_smul_eq_zero (nonZeroDivisors.ne_zero t.2) ht
  have hs0 : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])]
    exact nonZeroDivisors.ne_zero s.2
  rw [hx, map_zero] at hs'
  exact (smul_eq_zero.1 hs').resolve_left hs0

/-- **The rational Tate pairing is nonzero.** If `M` is `ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r`,
`r > 0`, and every `x ↦ e n x` is injective, then `rationalTatePairing e he ≠ 0`. -/
theorem rationalTatePairing_ne_zero {r : ℕ} (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
    (hr : 0 < r) (hperf : ∀ n, Function.Injective (e n)) : rationalTatePairing e he ≠ 0 := by
  have : Nontrivial (rationalTate ℓ M) :=
    Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])
      (by rw [finrank_rationalTate hdiv htors]; exact hr)
  exact ne_zero_of_nondegenerate (rationalTatePairing_nondegenerate hdiv hperf)

/-- **The rational Tate pairing is perfect.** If `M` is `ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r`,
`N` is `ℓ`-divisible with `N[ℓ^n] ≅ ℤ/ℓ^n`, and every `x ↦ e n x` is injective, then
`V_ℓ M → Hom_{ℚ_ℓ}(V_ℓ M, V_ℓ N)`, `z ↦ rationalTatePairing e he z`, is bijective. -/
theorem rationalTatePairing_bijective {r : ℕ} (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
    (hdivN : ∀ x : N, ∃ y, ℓ • y = x)
    (htorsN : ∀ n, Nonempty (AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin 1 → ZMod (ℓ ^ n))))
    (hperf : ∀ n, Function.Injective (e n)) : Function.Bijective (rationalTatePairing e he) := by
  have := module_finite_rationalTate hdiv htors
  have := module_finite_rationalTate hdivN htorsN
  have hinj : Function.Injective (rationalTatePairing e he) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact rationalTatePairing_nondegenerate hdiv hperf z fun w => by
      rw [hz, LinearMap.zero_apply]
  have hrank : Module.finrank ℚ_[ℓ] (rationalTate ℓ M) =
      Module.finrank ℚ_[ℓ] (rationalTate ℓ M →ₗ[ℚ_[ℓ]] rationalTate ℓ N) := by
    rw [Module.finrank_linearMap, finrank_rationalTate hdiv htors,
      finrank_rationalTate hdivN htorsN, mul_one]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj⟩

/-- **Kernel of the multiplier.** Under the hypotheses of `rationalTatePairing_ne_zero`, the
kernel of the multiplier `GSp(V_ℓ M, ψ) → ℚ_ℓˣ` of `ψ = rationalTatePairing e he` is
`Sp(V_ℓ M, ψ)`. -/
theorem ker_similitudeMultiplier_rationalTatePairing {r : ℕ} (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
    (hr : 0 < r) (hperf : ∀ n, Function.Injective (e n)) :
    (similitudeMultiplier (rationalTatePairing e he)
        (rationalTatePairing_ne_zero hdiv htors hr hperf)).ker =
      (symplecticGroup (rationalTatePairing e he)).subgroupOf
        (similitudeGroup (rationalTatePairing e he)) :=
  ker_similitudeMultiplier _ _

end Perfect

section TateTwist

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M] {K L : Type*} [Field K] [Field L]
  [Algebra K L] [DistribMulAction (L ≃ₐ[K] L) M]
  {e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy (Additive Lˣ) ((ℓ ^ n : ℕ) : ℤ)}
  {he : IsCompatibleTorsionPairing ℓ e}

/-- **The multiplier is the cyclotomic character (perfect pairings).** Let `L` be algebraically
closed with `(ℓ : L) ≠ 0`, `M` be `ℓ`-divisible with `M[ℓ^n] ≅ (ℤ/ℓ^n)^r`, `r > 0`, and the
compatible `Aut(L/K)`-equivariant pairings `e n : M[ℓ^n] × M[ℓ^n] → μ_{ℓ^n}(L)` be perfect
(`x ↦ e n x` injective). Then `ψ = rationalTatePairing e he ≠ 0` and the multiplier of
`σ ∈ Aut(L/K)` acting on `V_ℓ M` is `χ_ℓ(σ)`. -/
theorem similitudeMultiplier_galoisSimilitudeRepresentation_of_injective [IsAlgClosed L]
    {r : ℕ} (hℓL : (ℓ : L) ≠ 0) (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e)
    (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
    (hr : 0 < r) (hperf : ∀ n, Function.Injective (e n)) (σ : L ≃ₐ[K] L) :
    similitudeMultiplier _ (rationalTatePairing_ne_zero (he := he) hdiv htors hr hperf)
        (galoisSimilitudeRepresentation (he := he) hℓL heq σ) =
      Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom (cyclotomicCharacter L ℓ σ.toRingEquiv) :=
  similitudeMultiplier_galoisSimilitudeRepresentation hℓL heq _ σ

/-- **Symplectic elements are the kernel of the cyclotomic character.** Under the hypotheses of
`similitudeMultiplier_galoisSimilitudeRepresentation_of_injective`, `σ` acts on `V_ℓ M` through
`Sp(V_ℓ M, ψ)` iff `χ_ℓ(σ) = 1`. -/
theorem galoisSimilitudeRepresentation_mem_symplecticGroup_iff [IsAlgClosed L]
    {r : ℕ} (hℓL : (ℓ : L) ≠ 0) (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e)
    (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n))))
    (hr : 0 < r) (hperf : ∀ n, Function.Injective (e n)) (σ : L ≃ₐ[K] L) :
    ((galoisSimilitudeRepresentation (he := he) hℓL heq σ :
        rationalTate ℓ M ≃ₗ[ℚ_[ℓ]] rationalTate ℓ M) ∈
        symplecticGroup (rationalTatePairing e he)) ↔
      cyclotomicCharacter L ℓ σ.toRingEquiv = 1 := by
  have hψ := rationalTatePairing_ne_zero (he := he) hdiv htors hr hperf
  refine Subgroup.mem_subgroupOf.symm.trans ?_
  rw [← ker_similitudeMultiplier _ hψ, MonoidHom.mem_ker,
    similitudeMultiplier_galoisSimilitudeRepresentation hℓL heq hψ σ]
  exact (Units.map_injective (f := (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom)
    (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])).eq_iff' (map_one _)

end TateTwist

end ArithmeticOfJacobiPolynomials
