/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.PermGroup.SignKernel
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Lemma 5.6: normal generation by supported cycles

1. A normal subgroup of `S_N` containing a single cycle of even length `d`, `2 ≤ d < N`, is
   `S_N` (`eq_top_of_normal_of_isCycle_of_even`).
2. A subgroup `H ≤ W_N = negCommPerm s`, normal in `W_N`, containing single `2d₁`- and
   `2d₂`-cycles with `1 ≤ dᵢ < N`, `d₁` even and `d₂` odd, is `W_N`
   (`eq_negCommPerm_of_normal_of_isCycle`).

The manuscript assumes `N ≥ 3`; this is implied by the hypotheses (`2 ≤ d < N`), so it is not
stated separately.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Equiv Equiv.Perm

/-- **Lemma 5.6 (1)**. A normal subgroup of the symmetric group `S_N` containing a single cycle
of even length `d` with `2 ≤ d < N` is all of `S_N`. -/
theorem eq_top_of_normal_of_isCycle_of_even {α : Type*} [Fintype α] [DecidableEq α]
    {H : Subgroup (Perm α)} (hH : H.Normal) {σ : Perm α} (hσH : σ ∈ H) (hc : σ.IsCycle)
    {d : ℕ} (hd : σ.support.card = d) (heven : Even d) (hd2 : 2 ≤ d)
    (hdα : d < Fintype.card α) : H = ⊤ := by
  obtain ⟨i, hi⟩ : σ.support.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨j, hj⟩ : ∃ j, j ∉ σ.support := by
    by_contra! h
    rw [Finset.eq_univ_of_forall h, Finset.card_univ] at hd
    omega
  have hσi : σ i ≠ i := mem_support.1 hi
  have hσj : σ j = j := notMem_support.1 hj
  have hσij : σ i ≠ j := fun h => hj (h ▸ apply_mem_support.2 hi)
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  -- the commutator `σ (i j) σ⁻¹ (i j) = (σ i j) (i j)` is a 3-cycle in `H`
  have hcH : swap j (σ i) * swap j i ∈ H := by
    have h1 : swap i j * σ⁻¹ * (swap i j)⁻¹ ∈ H := hH.conj_mem _ (H.inv_mem hσH) _
    have h2 := H.mul_mem hσH h1
    rw [show σ * (swap i j * σ⁻¹ * (swap i j)⁻¹) = (σ * swap i j * σ⁻¹) * swap i j by
      rw [swap_inv]; group, ← swap_apply_apply, hσj, swap_comm (σ i), swap_comm i] at h2
    exact h2
  have h3 : IsThreeCycle (swap j (σ i) * swap j i) :=
    isThreeCycle_swap_mul_swap_same (Ne.symm hσij) (Ne.symm hij) hσi
  have hthree : ∀ τ : Perm α, IsThreeCycle τ → τ ∈ H := by
    intro τ hτ
    have hconj : IsConj (swap j (σ i) * swap j i) τ := by
      rw [isConj_iff_cycleType_eq]
      exact (show _ = _ from h3).trans (show _ = _ from hτ).symm
    obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
    exact hH.conj_mem _ hcH g
  have halt : alternatingGroup α ≤ H := by
    rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
    exact hthree
  have hsign : sign σ = -1 := by rw [hc.sign, hd, heven.neg_one_pow]
  rw [eq_top_iff]
  intro τ _
  rcases Int.units_eq_one_or (sign τ) with h | h
  · exact halt (mem_alternatingGroup.2 h)
  · have hστ : σ * τ ∈ H := halt (mem_alternatingGroup.2 (by rw [sign_mul, hsign, h]; rfl))
    simpa using H.mul_mem (H.inv_mem hσH) hστ

variable {L : Type*} [Field L] {s : Set L}

/-- The projection of a single `2d`-cycle of `negCommPerm s` with `d ≥ 2` is a single
`d`-cycle on the pairs. -/
theorem isCycle_pairPerm [Fintype s] [DecidableEq s] [Fintype (squares s)]
    [DecidableEq (squares s)] (h2 : (2 : L) ≠ 0) (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s)
    {σ : Perm s} (hσ : σ ∈ negCommPerm s) (hc : σ.IsCycle) {d : ℕ}
    (hd : σ.support.card = 2 * d) (hd2 : 2 ≤ d) :
    (pairPerm ⟨σ, hσ⟩).IsCycle ∧ (pairPerm ⟨σ, hσ⟩).support.card = d := by
  have hπx : ∀ x, pairPerm ⟨σ, hσ⟩ (toSquare x) = toSquare (σ x) :=
    fun x => pairPerm_apply_toSquare _ x
  have hmoved : ∀ x, pairPerm ⟨σ, hσ⟩ (toSquare x) ≠ toSquare x ↔ x ∈ σ.support := by
    intro x
    rw [hπx, mem_support]
    constructor
    · intro h h'
      exact h (by rw [h'])
    · intro hx h
      rcases eq_or_eq_negPerm_of_toSquare_eq hneg h.symm with h' | h'
      · exact hx h'
      · have hpow := pow_half_apply_of_mem_support h2 h0 hneg hσ hc hd (mem_support.2 hx)
        have h1 : (σ ^ (d - 1)) x = x := by
          apply σ.injective
          rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (by omega), hpow, h']
        have h1' : σ ^ (d - 1) = 1 := hc.pow_eq_one_iff.2 ⟨x, hx, h1⟩
        have hdvd := orderOf_dvd_of_pow_eq_one h1'
        rw [hc.orderOf, hd] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
  have hsupp : (pairPerm ⟨σ, hσ⟩).support = σ.support.image toSquare := by
    ext q
    obtain ⟨x, rfl⟩ := toSquare_surjective q
    rw [mem_support, hmoved, Finset.mem_image]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rcases eq_or_eq_negPerm_of_toSquare_eq hneg hyx with rfl | rfl
      · exact hy
      · exact negPerm_mem_support_of_mem_negCommPerm hneg hσ hy
  refine ⟨?_, ?_⟩
  · obtain ⟨x₀, hx₀⟩ : σ.support.Nonempty := Finset.card_pos.1 (by omega)
    refine ⟨toSquare x₀, (hmoved x₀).2 hx₀, fun q hq => ?_⟩
    obtain ⟨y, rfl⟩ := toSquare_surjective q
    obtain ⟨i, hi⟩ := hc.sameCycle (mem_support.1 hx₀) (mem_support.1 ((hmoved y).1 hq))
    refine ⟨i, ?_⟩
    rw [zpow_pairPerm_apply_toSquare]
    exact congrArg toSquare hi
  · rw [hsupp]
    have := card_eq_two_mul_card_image_toSquare h2 h0 hneg σ.support
      (fun x hx => negPerm_mem_support_of_mem_negCommPerm hneg hσ hx)
    omega

/-- **Lemma 5.6 (2)**. Let `H ≤ W_N = negCommPerm s` be normal in `W_N`. If `H` contains a
single `2d₁`-cycle and a single `2d₂`-cycle with `1 ≤ dᵢ < N`, `d₁` even and `d₂` odd, then
`H = W_N`. (`1 ≤ d₂` follows from `Odd d₂`, and `N ≥ 3` from `2 ≤ d₁ < N`.) -/
theorem eq_negCommPerm_of_normal_of_isCycle [Fintype s] [DecidableEq s] (h2 : (2 : L) ≠ 0)
    (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s) {H : Subgroup (Perm s)}
    (hH : H ≤ negCommPerm s) (hnorm : (H.subgroupOf (negCommPerm s)).Normal)
    {σ₁ σ₂ : Perm s} (hσ₁ : σ₁ ∈ H) (hσ₂ : σ₂ ∈ H) (hc₁ : σ₁.IsCycle) (hc₂ : σ₂.IsCycle)
    {d₁ d₂ : ℕ} (hd₁ : σ₁.support.card = 2 * d₁) (hd₂ : σ₂.support.card = 2 * d₂)
    (heven : Even d₁) (hodd : Odd d₂) (hd₁pos : 1 ≤ d₁) (hd₁N : d₁ < Nat.card (squares s))
    (hd₂N : d₂ < Nat.card (squares s)) : H = negCommPerm s := by
  classical
  have : Fintype (squares s) := Fintype.ofFinite _
  have hM : ((H.subgroupOf (negCommPerm s)).map pairPerm).Normal :=
    hnorm.map _ (pairPerm_surjective h2 h0 hneg)
  have hd₁2 : 2 ≤ d₁ := by
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨hcyc, hcard⟩ := isCycle_pairPerm h2 h0 hneg (hH hσ₁) hc₁ hd₁ hd₁2
  have hmem : pairPerm ⟨σ₁, hH hσ₁⟩ ∈ (H.subgroupOf (negCommPerm s)).map pairPerm :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hσ₁)
  have htop := eq_top_of_normal_of_isCycle_of_even hM hmem hcyc hcard heven hd₁2
    (by rwa [← Nat.card_eq_fintype_card])
  exact eq_negCommPerm_of_isCycle_of_odd h2 h0 hneg hH htop hσ₂ hc₂ hd₂ hodd hd₂N

end ArithmeticOfJacobiPolynomials
