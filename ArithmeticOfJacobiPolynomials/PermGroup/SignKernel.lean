/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.PermGroup.Wreath

/-!
# Lemma 5.5: the sign kernel

Let `Γ ≤ W_N = negCommPerm s` project onto `S_N`. If `Γ` contains a single `2d`-cycle with
`d` odd and `1 ≤ d < N`, then `Γ = W_N`.

The `d`-th power of such a cycle is the sign change on its `d` pairs
(`pow_half_eq_signFlip`); conjugating by lifts of `S_N` gives all sign changes.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Equiv Equiv.Perm

variable {L : Type*} [Field L] {s : Set L}

/-- A single `2d`-cycle `σ ∈ negCommPerm s` satisfies `σ ^ d x = -x` on its support: its
`d`-th power is the half-turn, which flips each of its `d` pairs. -/
theorem pow_half_apply_of_mem_support [Fintype s] [DecidableEq s] (h2 : (2 : L) ≠ 0)
    (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s) {σ : Perm s} (hσ : σ ∈ negCommPerm s)
    (hc : σ.IsCycle) {d : ℕ} (hd : σ.support.card = 2 * d) {x : s} (hx : x ∈ σ.support) :
    (σ ^ d) x = negPerm hneg x := by
  have hnx := negPerm_mem_support_of_mem_negCommPerm hneg hσ hx
  obtain ⟨i, hi⟩ := hc.sameCycle (mem_support.1 hx) (mem_support.1 hnx)
  have hτ : ∀ y ∈ σ.support, (σ ^ i) y = negPerm hneg y := by
    intro y hy
    obtain ⟨j, rfl⟩ := hc.sameCycle (mem_support.1 hx) (mem_support.1 hy)
    rw [← Perm.mul_apply, ← zpow_add, add_comm, zpow_add, Perm.mul_apply, hi]
    exact negCommPerm_apply_negPerm hneg (zpow_mem hσ j) x
  have h1 : (σ ^ i) ^ 2 = 1 := by
    refine Equiv.ext fun y => ?_
    rw [sq, Perm.mul_apply, Perm.one_apply]
    by_cases hy : y ∈ σ.support
    · rw [hτ y hy, hτ _ (negPerm_mem_support_of_mem_negCommPerm hneg hσ hy), negPerm_negPerm]
    · have hy' : σ y = y := notMem_support.1 hy
      rw [zpow_apply_eq_self_of_apply_eq_self hy', zpow_apply_eq_self_of_apply_eq_self hy']
  have hdvd : (orderOf σ : ℤ) ∣ i * 2 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_two, ← sq, h1]
  rw [hc.orderOf, hd] at hdvd
  obtain ⟨m, hm⟩ := hdvd
  push_cast at hm
  have him : i = d * m := by linarith
  have h2d : σ ^ (2 * d) = 1 := by rw [← hd, ← hc.orderOf, pow_orderOf_eq_one]
  rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
  · have hi' : i = ((2 * d : ℕ) : ℤ) * k := by rw [him]; push_cast; ring
    rw [hi', zpow_mul, zpow_natCast, h2d, one_zpow, Perm.one_apply] at hi
    exact absurd hi.symm (negPerm_ne_self hneg h2 h0 x)
  · have hi' : i = ((2 * d : ℕ) : ℤ) * k + (d : ℕ) := by rw [him]; push_cast; ring
    rwa [hi', zpow_add, zpow_mul, zpow_natCast, zpow_natCast, h2d, one_zpow, one_mul] at hi

/-- The `d`-th power of a single `2d`-cycle in `negCommPerm s` is the sign change on the pairs
of its support. -/
theorem pow_half_eq_signFlip [Fintype s] [DecidableEq s] (h2 : (2 : L) ≠ 0)
    (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s) {σ : Perm s} (hσ : σ ∈ negCommPerm s)
    (hc : σ.IsCycle) {d : ℕ} (hd : σ.support.card = 2 * d) :
    σ ^ d = signFlip hneg (toSquare '' (σ.support : Set s)) := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ σ.support
  · have hx' : toSquare x ∈ toSquare '' (σ.support : Set s) := ⟨x, hx, rfl⟩
    rw [pow_half_apply_of_mem_support h2 h0 hneg hσ hc hd hx, signFlip_apply_of_mem hneg hx']
  · have hx' : toSquare x ∉ toSquare '' (σ.support : Set s) := by
      rintro ⟨y, hy, hyx⟩
      rcases eq_or_eq_negPerm_of_toSquare_eq hneg hyx with rfl | rfl
      · exact hx hy
      · exact hx (negPerm_mem_support_of_mem_negCommPerm hneg hσ hy)
    rw [signFlip_apply_of_notMem hneg hx',
      pow_apply_eq_self_of_apply_eq_self (notMem_support.1 hx)]

/-- **Lemma 5.5**. Let `Γ ≤ W_N = negCommPerm s` project onto `S_N`
(the permutations of the `N` pairs). If `Γ` contains a single `2d`-cycle with `d` odd and
`1 ≤ d < N`, then `Γ = W_N`. (`1 ≤ d` is implied by `Odd d`.) -/
theorem eq_negCommPerm_of_isCycle_of_odd [Fintype s] [DecidableEq s] (h2 : (2 : L) ≠ 0)
    (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s) {Γ : Subgroup (Perm s)}
    (hΓ : Γ ≤ negCommPerm s) (hproj : (Γ.subgroupOf (negCommPerm s)).map pairPerm = ⊤)
    {σ : Perm s} (hσΓ : σ ∈ Γ) (hc : σ.IsCycle) {d : ℕ} (hd : σ.support.card = 2 * d)
    (hodd : Odd d) (hdN : d < Nat.card (squares s)) : Γ = negCommPerm s := by
  classical
  have hσ : σ ∈ negCommPerm s := hΓ hσΓ
  have hlift : ∀ π : Perm (squares s), ∃ γ : negCommPerm s, (γ : Perm s) ∈ Γ ∧ pairPerm γ = π := by
    intro π
    have hπ : π ∈ (Γ.subgroupOf (negCommPerm s)).map pairPerm := hproj ▸ Subgroup.mem_top π
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hπ
    exact ⟨γ, Subgroup.mem_subgroupOf.1 hγ, rfl⟩
  have hconj : ∀ T, signFlip hneg T ∈ Γ → ∀ π : Perm (squares s), signFlip hneg (π '' T) ∈ Γ := by
    intro T hT π
    obtain ⟨γ, hγ, rfl⟩ := hlift π
    rw [← conj_signFlip]
    exact Γ.mul_mem (Γ.mul_mem hγ hT) (Γ.inv_mem hγ)
  set A : Finset (squares s) := σ.support.image toSquare with hA_def
  have hA : signFlip hneg (A : Set (squares s)) ∈ Γ := by
    rw [hA_def, Finset.coe_image, ← pow_half_eq_signFlip h2 h0 hneg hσ hc hd]
    exact Γ.pow_mem hσΓ d
  have hAcard : A.card = d := by
    have := card_eq_two_mul_card_image_toSquare h2 h0 hneg σ.support
      (fun x hx => negPerm_mem_support_of_mem_negCommPerm hneg hσ hx)
    rw [← hA_def] at this
    omega
  obtain ⟨i, hi⟩ : A.Nonempty := Finset.card_pos.1 (hAcard ▸ hodd.pos)
  obtain ⟨j, hj⟩ : ∃ j, j ∉ A := by
    by_contra! h
    have : Nat.card (squares s) ≤ A.card := by
      rw [← Set.ncard_univ, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard (fun q _ => h q) (Finset.finite_toSet A)
    rw [hAcard] at this
    omega
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  -- `v + (i j) v = e_i + e_j`
  have hpair : signFlip hneg {i, j} ∈ Γ := by
    have h := Γ.mul_mem hA (hconj _ hA (swap i j))
    rw [signFlip_mul] at h
    convert h using 2
    ext q
    rw [Set.mem_symmDiff, Set.mem_image_equiv, Equiv.symm_swap, Finset.mem_coe, Finset.mem_coe]
    by_cases hqi : q = i
    · subst hqi; simp [swap_apply_left, hi, hj]
    by_cases hqj : q = j
    · subst hqj; simp [swap_apply_right, hi, hj]
    rw [swap_apply_of_ne_of_ne hqi hqj]
    simp [hqi, hqj]
  have hpairs : ∀ a b : squares s, a ≠ b → signFlip hneg {a, b} ∈ Γ := by
    intro a b hab
    have ha' : a ≠ swap i a j := fun h =>
      hij ((swap i a).injective ((swap_apply_left i a).trans h))
    have h := hconj _ hpair (swap (swap i a j) b * swap i a)
    rwa [Set.image_pair, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne ha' hab, swap_apply_left] at h
  -- a single sign change, by removing pairs from `A`
  have hsingle : ∃ a, signFlip hneg {a} ∈ Γ := by
    suffices key : ∀ n : ℕ, ∀ B : Finset (squares s), B.card = 2 * n + 1 →
        signFlip hneg (B : Set (squares s)) ∈ Γ → ∃ a, signFlip hneg {a} ∈ Γ by
      obtain ⟨n, hn⟩ := hodd
      exact key n A (by omega) hA
    intro n
    induction n with
    | zero =>
      intro B hB hBΓ
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hB
      exact ⟨a, by simpa using hBΓ⟩
    | succ n ih =>
      intro B hB hBΓ
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < B.card)
      have hsub : ({a, b} : Finset (squares s)) ⊆ B := Finset.insert_subset ha
        (Finset.singleton_subset_iff.2 hb)
      refine ih (B \ {a, b}) ?_ ?_
      · rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hab]
        omega
      · have h := Γ.mul_mem hBΓ (hpairs a b hab)
        rw [signFlip_mul] at h
        convert h using 2
        have hsub' : ({a, b} : Set (squares s)) ⊆ B := by
          rw [← Finset.coe_pair]; exact Finset.coe_subset.2 hsub
        rw [Finset.coe_sdiff, Finset.coe_pair, symmDiff_of_ge hsub']
  have hall_single : ∀ a, signFlip hneg {a} ∈ Γ := by
    obtain ⟨a₀, h⟩ := hsingle
    intro a
    simpa [Set.image_singleton, swap_apply_left] using hconj _ h (swap a₀ a)
  have hallfin : ∀ B : Finset (squares s), signFlip hneg (B : Set (squares s)) ∈ Γ := by
    intro B
    induction B using Finset.induction_on with
    | empty => simp [Γ.one_mem]
    | insert a B haB ih =>
      have h := Γ.mul_mem (hall_single a) ih
      rw [signFlip_mul] at h
      convert h using 2
      rw [Finset.coe_insert, Set.insert_eq,
        (Set.disjoint_singleton_left.2 (Finset.mem_coe.not.2 haB)).symmDiff_eq_sup]
      rfl
  have hall : ∀ T : Set (squares s), signFlip hneg T ∈ Γ := by
    intro T
    have h := hallfin (Set.toFinite T).toFinset
    rwa [Set.Finite.coe_toFinset] at h
  have hker : pairPerm.ker ≤ Γ.subgroupOf (negCommPerm s) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf, eq_signFlip_of_mem_ker hneg h2 h0 hk]
    exact hall _
  have htop : Γ.subgroupOf (negCommPerm s) = ⊤ := by
    have h := Subgroup.comap_map_eq pairPerm (Γ.subgroupOf (negCommPerm s))
    rw [hproj, Subgroup.comap_top, sup_eq_left.2 hker] at h
    exact h.symm
  exact le_antisymm hΓ (Subgroup.subgroupOf_eq_top.1 htop)

end ArithmeticOfJacobiPolynomials
