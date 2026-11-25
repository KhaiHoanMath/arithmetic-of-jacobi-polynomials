/- Assembled by AxiomProver. -/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Primitivity from an element of prime order (proof of Lemma 5.16)

The manuscript's sentence: "Irreducibility gives transitivity. In a nontrivial system of blocks,
both the block size and the number of blocks are at most `n/2 < p`. An element of order `p` would
act trivially on the blocks and on each block, a contradiction. Hence the group is primitive."

`isPreprimitive_of_prime_cycle` is that counting argument: a transitive group `G` of degree
`n < 2p` that contains a cycle `σ` of prime length `p` is primitive. A nontrivial block `B` has
`|B| · #(translates of B) = n` with `|B| ≥ 2`, so both factors are `≤ n/2 < p`. A permutation of
order dividing `p` of a set with fewer than `p` points is trivial
(`perm_eq_one_of_pow_prime_of_card_lt`, since `p ∤ m!` for `m < p`). So `σ` fixes every
translate of `B` and then every point of every translate, so `σ = 1`, contradicting that `σ` is a
cycle.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open MulAction Equiv Pointwise

/-- A permutation `τ` of a finite set with fewer than `p` points and `τ ^ p = 1`, `p` prime, is
the identity (`p ∤ (card X)!`). -/
theorem perm_eq_one_of_pow_prime_of_card_lt {X : Type*} [Fintype X]
    {τ : Perm X} {p : ℕ} (hp : p.Prime) (hτ : τ ^ p = 1) (hX : Fintype.card X < p) :
    τ = 1 := by
  classical
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hτ) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    have hd : orderOf τ ∣ Fintype.card (Perm X) := orderOf_dvd_card
    rw [Fintype.card_perm, h] at hd
    exact absurd ((Nat.Prime.dvd_factorial hp).mp hd) (not_le.mpr hX)

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Primitivity from a cycle of prime length** (proof of Lemma 5.16, counting argument): a
transitive permutation group of degree `n < 2p` containing a cycle of prime length `p` is
primitive. -/
theorem isPreprimitive_of_prime_cycle {G : Subgroup (Perm α)} [IsPretransitive G α] {p : ℕ}
    (hp : p.Prime) {σ : Perm α} (hσG : σ ∈ G) (hσ : σ.IsCycle) (hcard : σ.support.card = p)
    (hn : Fintype.card α < 2 * p) : IsPreprimitive G α := by
  refine ⟨fun {B} hB => ?_⟩
  by_contra hnt
  simp only [IsTrivialBlock, not_or] at hnt
  obtain ⟨hns, hnu⟩ := hnt
  have hb1 : 1 < B.ncard :=
    Set.one_lt_ncard_iff_nontrivial.mpr (Set.not_subsingleton_iff.mp hns)
  have hne : B.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hprod := hB.ncard_block_mul_ncard_orbit_eq hne
  rw [Nat.card_eq_fintype_card] at hprod
  have hbn : B.ncard < Fintype.card α := by
    have := Set.ncard_lt_card hnu
    rwa [Nat.card_eq_fintype_card] at this
  have hk0 : (orbit G B).ncard ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    have : 0 < Fintype.card α := by
      obtain ⟨x, _⟩ := hne
      exact Fintype.card_pos_iff.mpr ⟨x⟩
    omega
  -- block size and number of blocks are `≤ n/2 < p`
  have hk : (orbit G B).ncard < p := by nlinarith
  have hb : B.ncard < p := by
    have : 2 ≤ (orbit G B).ncard := by
      by_contra h
      have h1 : (orbit G B).ncard = 1 := by omega
      rw [h1, mul_one] at hprod
      omega
    nlinarith
  have hord : orderOf σ = p := by rw [hσ.orderOf, hcard]
  have hσp : σ ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one σ
  set s : G := ⟨σ, hσG⟩ with hs
  have hsp : s ^ p = 1 := Subtype.ext (by simpa [hs] using hσp)
  -- `σ` fixes every translate of `B`
  have : Finite (orbit G B) := (Set.toFinite _)
  have : Fintype (orbit G B) := Fintype.ofFinite _
  have hfixC : ∀ C : orbit G B, s • C = C := by
    intro C
    have h1 : (toPermHom G (orbit G B) s) ^ p = 1 := by
      rw [← map_pow, hsp, map_one]
    have hcardC : Fintype.card (orbit G B) < p := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; exact hk
    have := perm_eq_one_of_pow_prime_of_card_lt hp h1 hcardC
    simpa using congrArg (fun e : Perm (orbit G B) => e C) this
  -- `σ` fixes every point
  have hfix : ∀ x : α, σ x = x := by
    intro x
    obtain ⟨b0, hb0⟩ := hne
    obtain ⟨g, hg⟩ := exists_smul_eq G b0 x
    have hxC : x ∈ g • B := ⟨b0, hb0, hg⟩
    have hCmem : g • B ∈ orbit G B := mem_orbit _ _
    have hsC : s • (g • B) = g • B := congrArg Subtype.val (hfixC ⟨g • B, hCmem⟩)
    have hcardB : (g • B).ncard < p := by rw [Set.ncard_smul_set]; exact hb
    generalize g • B = C at hxC hsC hcardB
    have hstab : ∀ y, σ y ∈ C ↔ y ∈ C := by
      intro y
      constructor
      · intro hy
        rw [← hsC] at hy
        obtain ⟨y', hy', hyy⟩ := hy
        have : σ y' = σ y := hyy
        rwa [← σ.injective this]
      · intro hy
        rw [← hsC]
        exact ⟨y, hy, rfl⟩
    have : Fintype C := Fintype.ofFinite C
    have hcardC : Fintype.card C < p := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; exact hcardB
    have h1 : σ.subtypePerm hstab ^ p = 1 := by
      rw [Equiv.Perm.subtypePerm_pow]
      ext y
      simp [hσp]
    have h3 := perm_eq_one_of_pow_prime_of_card_lt hp h1 hcardC
    have h2 := congrArg (fun e : Perm C => (e ⟨x, hxC⟩ : α)) h3
    simpa using h2
  exact hσ.ne_one (Equiv.ext hfix)

end ArithmeticOfJacobiPolynomials
