/- Assembled by AxiomProver. -/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Blocks and long cycles (Lemma 5.3)

Let a transitive permutation group of degree `N` preserve a nontrivial block `B`, of size
`b`. If it contains a single `d`-cycle with `d > N/2`, then `b ∣ d`.

The proof: `b ≤ N/2 < d`. A translate of `B` containing a fixed point of the cycle is fixed
setwise (it meets its image); if it also contained a moved point it would contain the whole
support, of size `d > b`. So the support is a union of translates of `B`, which partition the
set, and `b ∣ d`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open MulAction Equiv Finset Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A translate of a block that contains a fixed point of a cycle `σ ∈ G` whose support is
larger than the block consists of fixed points of `σ`. -/
theorem isBlock_smul_fixed_of_isCycle {G : Subgroup (Perm α)} {B : Set α}
    (hB : IsBlock G B) {σ : Perm α} (hσG : σ ∈ G) (hσ : σ.IsCycle)
    (hlt : B.ncard < σ.support.card) (g : G) {x : α} (hx : x ∈ g • B) (hxσ : σ x = x)
    {y : α} (hy : y ∈ g • B) : σ y = y := by
  set s : G := ⟨σ, hσG⟩ with hs
  have hsx : s • x = x := by simpa [hs, Subgroup.smul_def] using hxσ
  -- `s • (g • B) = g • B`
  have hstab : s • (g • B) = g • B := by
    rcases hB.smul_eq_smul_or_disjoint (s * g) g with h | h
    · rwa [mul_smul] at h
    · exfalso
      have hx' : x ∈ (s * g) • B := by
        rw [mul_smul, ← hsx]
        exact Set.smul_mem_smul_set hx
      exact Set.disjoint_left.mp h hx' hx
  have hmem : s ∈ stabilizer G (g • B) := hstab
  by_contra hyσ
  apply absurd hlt
  rw [not_lt]
  have hsub : (σ.support : Set α) ⊆ g • B := by
    intro z hz
    have hz' : σ z ≠ z := Perm.mem_support.mp hz
    obtain ⟨i, hi⟩ := hσ.sameCycle hyσ hz'
    have hi' : s ^ i ∈ stabilizer G (g • B) := Subgroup.zpow_mem _ hmem i
    have : (s ^ i) • y ∈ (s ^ i) • (g • B) := Set.smul_mem_smul_set hy
    rw [hi'] at this
    rw [← hi]
    simpa [hs, Subgroup.smul_def] using this
  calc σ.support.card = (σ.support : Set α).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (g • B).ncard := Set.ncard_le_ncard hsub
    _ = B.ncard := Set.ncard_smul_set _ _

/-- **Lemma 5.3**. Let `G` be a transitive permutation group of degree `N`
and `B` a nontrivial block of `G` (`1 < |B| < N`). If `G` contains a single cycle `σ` of
length `d` with `N < 2d`, then `|B|` divides `d`. -/
theorem IsBlock.ncard_dvd_card_support_of_isCycle {G : Subgroup (Perm α)}
    (hG : IsPretransitive G α) {B : Set α} (hB : IsBlock G B) (hB1 : 1 < B.ncard)
    (hBN : B.ncard < Fintype.card α) {σ : Perm α} (hσG : σ ∈ G) (hσ : σ.IsCycle)
    (hd : Fintype.card α < 2 * σ.support.card) : B.ncard ∣ σ.support.card := by
  have := hG
  have hBne : B.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  -- `|B| ≤ N / 2 < d`
  have hdvd : B.ncard ∣ Fintype.card α := by
    simpa [Nat.card_eq_fintype_card] using hB.ncard_dvd_card hBne
  have hlt : B.ncard < σ.support.card := by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · simp at hk; omega
      · simp at hk; omega
      · omega
    have : 2 * B.ncard ≤ Fintype.card α := by
      rw [hk, mul_comm 2]; exact Nat.mul_le_mul_left _ hk2
    omega
  obtain ⟨b₀, hb₀⟩ := hBne
  -- the translate of `B` through each point
  choose g hg using fun x : α => MulAction.exists_smul_eq G b₀ x
  let f : α → Set α := fun x => g x • B
  have hxf : ∀ x, x ∈ f x := fun x => by
    have h := Set.smul_mem_smul_set (a := g x) hb₀
    rwa [hg x] at h
  have hf_eq : ∀ (h : G) (x : α), x ∈ h • B → f x = h • B := by
    intro h x hx
    rcases hB.smul_eq_smul_or_disjoint (g x) h with e | e
    · exact e
    · exact absurd hx (Set.disjoint_left.mp e (hxf x))
  -- each translate meeting the support lies in the support
  have hfib : ∀ x ∈ σ.support,
      ((σ.support.filter fun y => f y = f x : Finset α) : Set α) = f x := by
    intro x hx
    ext y
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, hy⟩
      rw [← hy]; exact hxf y
    · intro hy
      refine ⟨?_, hf_eq (g x) y hy⟩
      rw [Perm.mem_support]
      intro hyσ
      exact Perm.mem_support.mp hx
        (isBlock_smul_fixed_of_isCycle hB hσG hσ hlt (g x) hy hyσ (hxf x))
  classical
  rw [Finset.card_eq_sum_card_image f σ.support]
  have : ∀ C ∈ σ.support.image f, (σ.support.filter fun y => f y = C).card = B.ncard := by
    intro C hC
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
    rw [← Set.ncard_coe_finset, hfib x hx]
    exact Set.ncard_smul_set _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  exact Dvd.intro_left _ rfl

end ArithmeticOfJacobiPolynomials
