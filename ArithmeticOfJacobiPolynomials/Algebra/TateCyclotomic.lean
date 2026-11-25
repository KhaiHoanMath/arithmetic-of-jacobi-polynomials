/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateTopology
public import ArithmeticOfJacobiPolynomials.Algebra.TateRational
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The Tate twist `ℤ_ℓ(1)`: the Tate module of the units of a field

Let `L` be a field and `ℓ` a prime. The Tate twist is the `ℓ`-adic Tate module of the
multiplicative group of `L`,
`ℤ_ℓ(1) = T_ℓ(L^×) = lim_n μ_{ℓ^n}(L)`,
built with `tateModule` applied to the additive group `Additive Lˣ`.

## Main definitions

* `ArithmeticOfJacobiPolynomials.tateTwist ℓ L := tateModule (Additive Lˣ) ℓ`;
* `ArithmeticOfJacobiPolynomials.tateTwist.instDistribMulAction`: the action of `L ≃ₐ[K] L` on
`Additive Lˣ`
  by field automorphisms, `σ • u = σ(u)`;
* `ArithmeticOfJacobiPolynomials.tateTwist.representation ℓ K L`: the induced representation of `L
≃ₐ[K] L` on
  `tateTwist ℓ L` (`tateModule.representation` of
  `ArithmeticOfJacobiPolynomials.Algebra.TateAction`);
* `ArithmeticOfJacobiPolynomials.torsionUnitsEquivRootsOfUnity`: `(Additive Mˣ)[k] ≃+ Additive
(μ_k(M))`;
* `ArithmeticOfJacobiPolynomials.torsionUnitsEquivZMod h`: for a primitive `k`-th root of unity `ζ`,
  `(Additive Mˣ)[k] ≃+ ZMod k`, with inverse `i ↦ ζ ^ i` (`coe_torsionUnitsEquivZMod_symm`).

## Main results

Let `L` be algebraically closed with `(ℓ : L) ≠ 0` (characteristic not `ℓ`), e.g.
`L = AlgebraicClosure ℚ`.

* `ArithmeticOfJacobiPolynomials.exists_div_units`: `Lˣ` is `n`-divisible for every `n > 0`;
* `ArithmeticOfJacobiPolynomials.exists_tateTwist_isPrimitiveRoot`: there is a compatible system of
primitive
  `ℓ^n`-th roots of unity, i.e. `x : tateTwist ℓ L` with every `x n` primitive of order `ℓ^n`;
* `ArithmeticOfJacobiPolynomials.exists_torsionEquiv_compatible`: isomorphisms `(Additive Lˣ)[ℓ^n]
≃+ ZMod (ℓ^n)`
  compatible with multiplication by `ℓ` and reduction `ZMod (ℓ^(n+1)) → ZMod (ℓ^n)`;
* `ArithmeticOfJacobiPolynomials.tateTwist.finrank_eq_one`, `tateTwist.module_free`: `ℤ_ℓ(1)` is
free of rank one
  over `ℤ_ℓ` (proved from the divisibility and the torsion structure via
  `finrank_tateModule`); `tateTwist.finrank_rationalTate_eq_one`: its rational
  Tate module is one-dimensional over `ℚ_ℓ`;
* `ArithmeticOfJacobiPolynomials.tateTwist.continuous_representation`: the Galois representation is
continuous
  for the Krull topology (stabilisers of roots of unity are open, as each generates a finite
  extension), with no hypothesis on `L`;
* `ArithmeticOfJacobiPolynomials.tateTwist.representation_eq_cyclotomicCharacter`: `σ` acts on
`ℤ_ℓ(1)` by the
  scalar `cyclotomicCharacter L ℓ σ` of Mathlib.

No Weil pairing or Jacobian is involved.
-/

public section

open PadicInt

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

section Def

variable (ℓ : ℕ) (L : Type*) [Field L]

/-- The Tate twist `ℤ_ℓ(1) = T_ℓ(L^×) = lim_n μ_{ℓ^n}(L)`: the `ℓ`-adic Tate module of the
multiplicative group of the field `L`, written additively. -/
abbrev tateTwist : Type _ :=
  tateModule (Additive Lˣ) ℓ

end Def

section Action

variable (ℓ : ℕ) [Fact ℓ.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The action of `L ≃ₐ[K] L` on the multiplicative group `Lˣ` (written additively) by field
automorphisms: `σ • u = σ(u)`. -/
instance tateTwist.instDistribMulAction : DistribMulAction (L ≃ₐ[K] L) (Additive Lˣ) where
  smul σ x := Additive.ofMul (σ • Additive.toMul x)
  one_smul x := by
    change Additive.ofMul ((1 : L ≃ₐ[K] L) • Additive.toMul x) = x
    rw [one_smul, ofMul_toMul]
  mul_smul σ τ x := by
    change Additive.ofMul ((σ * τ) • Additive.toMul x) =
      Additive.ofMul (σ • Additive.toMul (Additive.ofMul (τ • Additive.toMul x)))
    rw [toMul_ofMul, mul_smul]
  smul_zero σ := by
    change Additive.ofMul (σ • (1 : Lˣ)) = Additive.ofMul 1
    rw [smul_one]
  smul_add σ x y := by
    change Additive.ofMul (σ • (Additive.toMul x * Additive.toMul y)) =
      Additive.ofMul (σ • Additive.toMul x * σ • Additive.toMul y)
    rw [smul_mul']

variable {K L}

/-- `σ • u` on `Additive Lˣ` is `σ(u)`. -/
theorem tateTwist.toMul_smul (σ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    Additive.toMul (σ • x) = σ • Additive.toMul x :=
  rfl

/-- On the underlying element of `L`, `σ • u` is `σ u`. -/
@[simp]
theorem tateTwist.coe_toMul_smul (σ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    ((Additive.toMul (σ • x) : Lˣ) : L) = σ ((Additive.toMul x : Lˣ) : L) :=
  rfl

variable (K L)

/-- The representation of `L ≃ₐ[K] L` on the Tate twist `ℤ_ℓ(1) = T_ℓ(L^×)`, induced by the
action of field automorphisms on `Lˣ`. -/
@[expose]
noncomputable def tateTwist.representation :
    Representation ℤ_[ℓ] (L ≃ₐ[K] L) (tateTwist ℓ L) :=
  tateModule.representation ℓ (Additive Lˣ) (L ≃ₐ[K] L)

/-- `tateTwist.representation` is `tateModule.representation` for the action on `Lˣ`. -/
theorem tateTwist.representation_eq :
    tateTwist.representation ℓ K L = tateModule.representation ℓ (Additive Lˣ) (L ≃ₐ[K] L) :=
  rfl

variable {ℓ K L}

/-- The `n`-th component of `σ • x` is `σ • x n`. -/
@[simp]
theorem tateTwist.representation_seq (σ : L ≃ₐ[K] L) (x : tateTwist ℓ L) (n : ℕ) :
    ((tateTwist.representation ℓ K L σ x : tateTwist ℓ L) : ℕ → Additive Lˣ) n =
      σ • (x : ℕ → Additive Lˣ) n :=
  tateModule.representation_seq σ x n

/-- On underlying elements of `L`, the `n`-th component of `σ • x` is `σ (x n)`. -/
theorem tateTwist.coe_representation_seq (σ : L ≃ₐ[K] L) (x : tateTwist ℓ L) (n : ℕ) :
    ((Additive.toMul (((tateTwist.representation ℓ K L σ x : tateTwist ℓ L) :
        ℕ → Additive Lˣ) n) : Lˣ) : L) =
      σ ((Additive.toMul ((x : ℕ → Additive Lˣ) n) : Lˣ) : L) := by
  rw [tateTwist.representation_seq, tateTwist.coe_toMul_smul]

end Action

section Torsion

variable (M : Type*) [CommMonoid M]

/-- The `k`-torsion of `Additive Mˣ` is the group of `k`-th roots of unity `μ_k(M)`. -/
@[expose]
def torsionUnitsEquivRootsOfUnity (k : ℕ) :
    AddSubgroup.torsionBy (Additive Mˣ) (k : ℤ) ≃+ Additive (rootsOfUnity k M) where
  toFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Mˣ), (mem_rootsOfUnity _ _).2 (by
    rw [← toMul_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 x.2, toMul_zero])⟩
  invFun u := ⟨Additive.ofMul ((Additive.toMul u : rootsOfUnity k M) : Mˣ),
    AddSubgroup.torsionBy.nsmul_iff.2 (by
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_ofMul, toMul_zero]
      exact (mem_rootsOfUnity _ _).1 (Additive.toMul u).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {M}

/-- `torsionUnitsEquivRootsOfUnity` is the identity on underlying units. -/
@[simp]
theorem coe_torsionUnitsEquivRootsOfUnity (k : ℕ)
    (x : AddSubgroup.torsionBy (Additive Mˣ) (k : ℤ)) :
    ((Additive.toMul (torsionUnitsEquivRootsOfUnity M k x) : rootsOfUnity k M) : Mˣ) =
      Additive.toMul (x : Additive Mˣ) :=
  rfl

variable {R : Type*} [CommRing R] [IsDomain R] {ζ : Rˣ} {k : ℕ} [NeZero k]

/-- **The `k`-torsion of the units via a primitive root.** If `ζ` is a primitive `k`-th root of
unity of the domain `R`, then `(Additive Rˣ)[k] ≃+ ZMod k`, with inverse `i ↦ ζ ^ i`. -/
@[expose]
noncomputable def torsionUnitsEquivZMod (h : IsPrimitiveRoot ζ k) :
    AddSubgroup.torsionBy (Additive Rˣ) (k : ℤ) ≃+ ZMod k :=
  (torsionUnitsEquivRootsOfUnity R k).trans
    ((MulEquiv.toAdditive (MulEquiv.subgroupCongr h.zpowers_eq).symm).trans
      h.zmodEquivZPowers.symm)

/-- The inverse of `torsionUnitsEquivZMod h` sends `i` to `ζ ^ i`, written additively. -/
theorem coe_torsionUnitsEquivZMod_symm (h : IsPrimitiveRoot ζ k) (i : ZMod k) :
    ((torsionUnitsEquivZMod h).symm i : Additive Rˣ) = i.val • Additive.ofMul ζ := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← ofMul_pow]
  simp only [torsionUnitsEquivZMod, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
    h.zmodEquivZPowers_apply_coe_nat]
  rfl

end Torsion

section RootsOfUnity

variable (L : Type*) [Field L]

/-- **Divisibility of the units of an algebraically closed field.** Every element of `Lˣ` has an
`n`-th root for `n > 0`: `Additive Lˣ` is `n`-divisible. -/
theorem exists_div_units [IsAlgClosed L] {n : ℕ} (hn : 0 < n) (x : Additive Lˣ) :
    ∃ y, n • y = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul x : Lˣ) : L) hn
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact (Additive.toMul x).ne_zero (by rw [← hz, zero_pow hn.ne'])
  refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_ofMul]
  ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]

/-- An algebraically closed field in which `k ≠ 0` has enough `k`-th roots of unity. -/
theorem hasEnoughRootsOfUnity_of_isAlgClosed [IsAlgClosed L] {k : ℕ} (hk : (k : L) ≠ 0) :
    HasEnoughRootsOfUnity L k :=
  haveI : NeZero (k : L) := ⟨hk⟩
  inferInstance

/-- An algebraically closed field in which `k ≠ 0` has a primitive `k`-th root of unity, as a
unit. -/
theorem exists_isPrimitiveRoot_units [IsAlgClosed L] {k : ℕ} (hk : (k : L) ≠ 0) :
    ∃ ζ : Lˣ, IsPrimitiveRoot ζ k := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk Nat.cast_zero
  have := hasEnoughRootsOfUnity_of_isAlgClosed L hk
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L k
  exact ⟨(hζ.isUnit hk0).unit, hζ.isUnit_unit hk0⟩

/-- If `(ℓ : L) ≠ 0`, then `((ℓ ^ n : ℕ) : L) ≠ 0`. -/
theorem natCast_pow_ne_zero_of_natCast_ne_zero {ℓ : ℕ} (hℓL : (ℓ : L) ≠ 0) (n : ℕ) :
    ((ℓ ^ n : ℕ) : L) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero n hℓL

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- **A compatible system of primitive roots of unity.** If `L` is algebraically closed with
`(ℓ : L) ≠ 0`, there is `x : tateTwist ℓ L` (so `x (n + 1) ^ ℓ = x n`) such that every `x n` is
a primitive `ℓ^n`-th root of unity. -/
theorem exists_tateTwist_isPrimitiveRoot [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0) :
    ∃ x : tateTwist ℓ L, ∀ n,
      IsPrimitiveRoot (Additive.toMul ((x : ℕ → Additive Lˣ) n)) (ℓ ^ n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_units L hℓL
  have hζ' : Additive.ofMul ζ ∈ AddSubgroup.torsionBy (Additive Lˣ) ((ℓ ^ 1 : ℕ) : ℤ) :=
    AddSubgroup.torsionBy.nsmul_iff.2 (by rw [pow_one, ← ofMul_pow, hζ.pow_eq_one, ofMul_one])
  obtain ⟨x, hx⟩ := tateReduction_surjective (exists_div_units L hℓ.out.pos) 1 ⟨_, hζ'⟩
  have hx1 : Additive.toMul ((x : ℕ → Additive Lˣ) 1) = ζ :=
    congrArg (fun P : AddSubgroup.torsionBy (Additive Lˣ) ((ℓ ^ 1 : ℕ) : ℤ) =>
      Additive.toMul (P : Additive Lˣ)) hx
  refine ⟨x, fun n => ?_⟩
  cases n with
  | zero =>
    rw [seq_zero, toMul_zero, pow_zero]
    exact IsPrimitiveRoot.one
  | succ m =>
    have hnot : ¬Additive.toMul ((x : ℕ → Additive Lˣ) (m + 1)) ^ ℓ ^ m = 1 := by
      rw [← toMul_nsmul, show m + 1 = 1 + m from Nat.add_comm m 1,
        pow_smul_seq_add, hx1]
      exact hζ.ne_one hℓ.out.one_lt
    have hfin : Additive.toMul ((x : ℕ → Additive Lˣ) (m + 1)) ^ ℓ ^ (m + 1) = 1 := by
      rw [← toMul_nsmul, pow_smul_seq, toMul_zero]
    rw [← orderOf_eq_prime_pow hnot hfin]
    exact IsPrimitiveRoot.orderOf _

/-- **Torsion of `Lˣ`, compatibly in `n`.** If `L` is algebraically closed with `(ℓ : L) ≠ 0`,
there are isomorphisms `e n : (Additive Lˣ)[ℓ^n] ≃+ ZMod (ℓ^n)` (given by a compatible system of
primitive roots) compatible with the transition maps: multiplication by `ℓ` on torsion
corresponds to reduction `ZMod (ℓ^(n+1)) → ZMod (ℓ^n)`. -/
theorem exists_torsionEquiv_compatible [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0) :
    ∃ e : ∀ n : ℕ, AddSubgroup.torsionBy (Additive Lˣ) ((ℓ ^ n : ℕ) : ℤ) ≃+ ZMod (ℓ ^ n),
      ∀ n (i : ZMod (ℓ ^ (n + 1))),
        ℓ • ((e (n + 1)).symm i : Additive Lˣ) = ((e n).symm (ZMod.cast i) : Additive Lˣ) := by
  obtain ⟨x, hx⟩ := exists_tateTwist_isPrimitiveRoot L ℓ hℓL
  refine ⟨fun n => torsionUnitsEquivZMod (hx n), fun n i => ?_⟩
  rw [coe_torsionUnitsEquivZMod_symm, coe_torsionUnitsEquivZMod_symm, ofMul_toMul, ofMul_toMul,
    smul_comm ℓ, smul_seq_succ]
  exact nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq x n)
    (by rw [ZMod.natCast_zmod_val, ZMod.natCast_val])

/-- If `L` is algebraically closed with `(ℓ : L) ≠ 0`, then `(Additive Lˣ)[ℓ^n] ≅ (ℤ/ℓ^n)^1`
for every `n`. -/
theorem tateTwist.nonempty_torsionEquiv [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0) (n : ℕ) :
    Nonempty (AddSubgroup.torsionBy (Additive Lˣ) ((ℓ ^ n : ℕ) : ℤ) ≃+
      (Fin 1 → ZMod (ℓ ^ n))) := by
  obtain ⟨ζ, hζ⟩ :=
    exists_isPrimitiveRoot_units L (natCast_pow_ne_zero_of_natCast_ne_zero L hℓL n)
  exact ⟨(torsionUnitsEquivZMod hζ).trans
    (LinearEquiv.funUnique (Fin 1) ℤ (ZMod (ℓ ^ n))).symm.toAddEquiv⟩

/-- **`ℤ_ℓ(1)` is free of rank one.** If `L` is algebraically closed with `(ℓ : L) ≠ 0`, then
`T_ℓ(L^×) ≅ ℤ_ℓ`. -/
theorem tateTwist.nonempty_linearEquiv [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0) :
    Nonempty (tateTwist ℓ L ≃ₗ[ℤ_[ℓ]] (Fin 1 → ℤ_[ℓ])) :=
  nonempty_linearEquiv_tateModule (exists_div_units L hℓ.out.pos)
    (tateTwist.nonempty_torsionEquiv L ℓ hℓL)

/-- If `L` is algebraically closed with `(ℓ : L) ≠ 0`, the Tate twist is a free `ℤ_ℓ`-module. -/
theorem tateTwist.module_free [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0) :
    Module.Free ℤ_[ℓ] (tateTwist ℓ L) :=
  module_free_tateModule (exists_div_units L hℓ.out.pos)
    (tateTwist.nonempty_torsionEquiv L ℓ hℓL)

/-- If `L` is algebraically closed with `(ℓ : L) ≠ 0`, the Tate twist is a finitely generated
`ℤ_ℓ`-module. -/
theorem tateTwist.module_finite [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0) :
    Module.Finite ℤ_[ℓ] (tateTwist ℓ L) :=
  module_finite_tateModule (exists_div_units L hℓ.out.pos)
    (tateTwist.nonempty_torsionEquiv L ℓ hℓL)

/-- **The rank of `ℤ_ℓ(1)`.** If `L` is algebraically closed with `(ℓ : L) ≠ 0`, then
`rank_{ℤ_ℓ} T_ℓ(L^×) = 1`. -/
theorem tateTwist.finrank_eq_one [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0) :
    Module.finrank ℤ_[ℓ] (tateTwist ℓ L) = 1 :=
  finrank_tateModule (exists_div_units L hℓ.out.pos) (tateTwist.nonempty_torsionEquiv L ℓ hℓL)

/-- **The rational Tate twist `ℚ_ℓ(1)` is one-dimensional.** If `L` is algebraically closed with
`(ℓ : L) ≠ 0`, then `dim_{ℚ_ℓ} (ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(L^×)) = 1`. -/
theorem tateTwist.finrank_rationalTate_eq_one [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0) :
    Module.finrank ℚ_[ℓ] (rationalTate ℓ (Additive Lˣ)) = 1 :=
  finrank_rationalTate (exists_div_units L hℓ.out.pos) (tateTwist.nonempty_torsionEquiv L ℓ hℓL)

/-- In `AlgebraicClosure ℚ` (characteristic zero), `(ℓ : AlgebraicClosure ℚ) ≠ 0`. -/
theorem natCast_ne_zero_algebraicClosure_rat : (ℓ : AlgebraicClosure ℚ) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (AlgebraicClosure ℚ)), ne_eq,
    map_eq_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective, Nat.cast_eq_zero]
  exact hℓ.out.ne_zero

/-- **`ℤ_ℓ(1)` over `ℚ̄`.** The Tate twist of `AlgebraicClosure ℚ` has rank one over `ℤ_ℓ`. -/
theorem tateTwist.finrank_algebraicClosure_rat :
    Module.finrank ℤ_[ℓ] (tateTwist ℓ (AlgebraicClosure ℚ)) = 1 :=
  tateTwist.finrank_eq_one (AlgebraicClosure ℚ) ℓ (natCast_ne_zero_algebraicClosure_rat ℓ)

end RootsOfUnity

section Continuity

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Open stabilisers of roots of unity.** For `n > 0` and an `n`-torsion point `P` of
`Additive Lˣ` (an `n`-th root of unity), the stabiliser of `P` in `L ≃ₐ[K] L` is open for the
Krull topology: it contains the fixing subgroup of the finite extension `K(P)`. -/
theorem tateTwist.isOpen_stabilizer {n : ℕ} (hn : 0 < n) (P : Additive Lˣ) (hP : n • P = 0) :
    IsOpen (MulAction.stabilizer (L ≃ₐ[K] L) P : Set (L ≃ₐ[K] L)) := by
  have hpow : ((Additive.toMul P : Lˣ) : L) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← toMul_nsmul, hP, toMul_zero, Units.val_one]
  have hint : IsIntegral K ((Additive.toMul P : Lˣ) : L) :=
    IsIntegral.of_pow hn (by rw [hpow]; exact isIntegral_one)
  have := IntermediateField.adjoin.finiteDimensional hint
  have hle : (IntermediateField.adjoin K {((Additive.toMul P : Lˣ) : L)}).fixingSubgroup ≤
      MulAction.stabilizer (L ≃ₐ[K] L) P := by
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    have h := (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ _
      (IntermediateField.mem_adjoin_simple_self K ((Additive.toMul P : Lˣ) : L))
    apply Additive.toMul.injective
    exact Units.ext h
  exact Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen _)

variable (K L)

/-- **Continuity of the Galois representation on `ℤ_ℓ(1)`.** The action map
`(L ≃ₐ[K] L) × T_ℓ(L^×) → T_ℓ(L^×)` is continuous for the Krull topology and the inverse-limit
topology. -/
theorem tateTwist.continuous_representation :
    Continuous fun p : (L ≃ₐ[K] L) × tateTwist ℓ L => tateTwist.representation ℓ K L p.1 p.2 :=
  tateModule.continuous_representation fun n P hP =>
    tateTwist.isOpen_stabilizer (pow_pos hℓ.out.pos n) P hP

end Continuity

section Cyclotomic

variable {ℓ : ℕ} [Fact ℓ.Prime] {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The Galois action on `ℤ_ℓ(1)` is the cyclotomic character.** If `L` is algebraically
closed with `(ℓ : L) ≠ 0`, every `σ : L ≃ₐ[K] L` acts on `T_ℓ(L^×)` as multiplication by the
scalar `cyclotomicCharacter L ℓ σ ∈ ℤ_ℓ^×` (Mathlib's cyclotomic character). -/
theorem tateTwist.representation_eq_cyclotomicCharacter [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0)
    (σ : L ≃ₐ[K] L) (x : tateTwist ℓ L) :
    tateTwist.representation ℓ K L σ x =
      ((cyclotomicCharacter L ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x := by
  have : ∀ i, HasEnoughRootsOfUnity L (ℓ ^ i) := fun i =>
    hasEnoughRootsOfUnity_of_isAlgClosed L (natCast_pow_ne_zero_of_natCast_ne_zero L hℓL i)
  refine tateModule_ext fun n => ?_
  rw [tateTwist.representation_seq, smul_seq]
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_nsmul, Units.val_pow_eq_pow_val]
  exact cyclotomicCharacter.spec ℓ σ.toRingEquiv _
    (by rw [← Units.val_pow_eq_pow_val, ← toMul_nsmul, pow_smul_seq, toMul_zero,
      Units.val_one])

end Cyclotomic

end ArithmeticOfJacobiPolynomials
