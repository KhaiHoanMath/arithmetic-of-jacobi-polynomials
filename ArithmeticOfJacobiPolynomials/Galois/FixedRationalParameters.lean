/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParametersPrimes
public import ArithmeticOfJacobiPolynomials.Galois.JacobiCycle
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge
public import ArithmeticOfJacobiPolynomials.PermGroup.NormalGeneration
public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
public import ArithmeticOfJacobiPolynomials.MainResults

/-!
# Theorem 1.6: the large factor for fixed rational parameters (Section 5.4)

For rational parameters `α = a/u`, `β = b/v` satisfying the denominator condition of
Theorem 1.6, write `D` and `r` for the reduced denominator and numerator of
`α + β` and `B = |r| + |a| + |b| + 4D + 11` (`cycleBound`). Every prime `p ≡ r (mod D)` with
`Dn + B < p`, `2(p + B) ≤ 3Dn` ((5.20), §5.5) satisfies the hypotheses of
Proposition 5.2 (`jacobiCycleHypotheses_of_eligible`), so `Gal(P_n^{(α,β)}/ℚ)` contains a single
`d_p`-cycle, `d_p = 2n + 1 - (p - r)/D`, with `n/2 < d_p ≤ n - 4`.

Main results (stated here with the dominant-factor and denominator conditions unfolded,
`IsDominant` and `DenomCond`):

* `exists_unique_isDominant_jacobiP`: for large `n`, `P_n^{(α,β)}` has a unique monic irreducible
  factor of degree `> n/2`;
* `natDegree_isDominant_jacobiP`: its degree `M_n` satisfies `n - M_n = O(n/(log n)^A)` for
  every `A > 0` (Lemma 5.13);
* `galoisGroupIsSymmetric_isDominant_jacobiP`: `Gal(h_n/ℚ) = S_{M_n}`, and for
  `P_n^{(α,β)} = κ h_n g_n` the restriction `Gal(h_n g_n/ℚ) → Gal(h_n/ℚ) × Gal(g_n/ℚ)` is
  bijective.

The group-theoretic tools: a cycle of `Gal(f)` whose support lies in the roots of a factor `p`
restricts to a cycle of `Gal(p)` of the same length (`galPerm_restrict_isCycle`); a long cycle
lies on the roots of the dominant factor (`aeval_eq_zero_of_isDominant`); primitivity from the
block sizes, Jones's theorem and an odd cycle give `S_M` (`eq_top_of_long_cycles`); a normal
subgroup argument gives the product (`restrictProd_bijective`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Filter

namespace FixedRationalParameters

/-! ### Permutations semiconjugate along an injection -/

/-- If `j ∘ a = b ∘ j` for an injection `j` whose range contains the support of `b`, then `a` is
a cycle iff `b` is, with the same support size. -/
theorem isCycle_iff_and_card_support_eq_of_semiconj {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {j : α → β} (hj : Function.Injective j) {a : Equiv.Perm α}
    {b : Equiv.Perm β} (hab : ∀ x, j (a x) = b (j x)) (hsupp : ∀ y, b y ≠ y → y ∈ Set.range j) :
    (a.IsCycle ↔ b.IsCycle) ∧ a.support.card = b.support.card := by
  classical
  have hb : b = a.extendDomain (Equiv.ofInjective j hj) := by
    ext1 y
    by_cases hy : y ∈ Set.range j
    · obtain ⟨x, rfl⟩ := hy
      have h1 := Equiv.Perm.extendDomain_apply_image a (Equiv.ofInjective j hj) x
      simp only [Equiv.ofInjective_apply] at h1
      rw [h1, hab]
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hy]
      by_contra h
      exact hy (hsupp y h)
  rw [hb, ← Equiv.Perm.card_cycleType_eq_one, ← Equiv.Perm.card_cycleType_eq_one,
    Equiv.Perm.cycleType_extendDomain, Equiv.Perm.card_support_extend_domain]
  exact ⟨Iff.rfl, rfl⟩

/-! ### Restriction of Galois elements to factors -/

section Restriction

variable {F : Type*} [Field F]

/-- The splitting field of `f ≠ 0` splits every factor of `f`. -/
theorem fact_splits_of_dvd {f p : F[X]} (hf : f ≠ 0) (hpf : p ∣ f) :
    Fact ((p.map (algebraMap F f.SplittingField)).Splits) :=
  ⟨(SplittingField.splits f).of_dvd (map_ne_zero hf) ((map_dvd_map' _).mpr hpf)⟩

/-- Restriction to a factor `p` intertwines the root actions along the root embedding
`rootSet p p.SplittingField → f.SplittingField`. -/
theorem coe_rootsEquivRootsAux_galPerm_restrict {f p : F[X]}
    [Fact ((p.map (algebraMap F f.SplittingField)).Splits)] (σ : f.Gal)
    (y : p.rootSet p.SplittingField) :
    ((Gal.rootsEquivRootsAux p f.SplittingField
        (galPerm p (Gal.restrict p f.SplittingField σ) y) : f.SplittingField)) =
      σ (Gal.rootsEquivRootsAux p f.SplittingField y) := by
  have h1 : Gal.rootsEquivRootsAux p f.SplittingField
      (galPerm p (Gal.restrict p f.SplittingField σ) y) =
      (Gal.restrict p f.SplittingField σ) • Gal.rootsEquivRootsAux p f.SplittingField y := by
    rw [Gal.smul_def, Equiv.symm_apply_apply, galPerm_apply]
  rw [h1]
  exact Gal.restrict_smul (p := p) (E := f.SplittingField) σ _

/-- If `σ` fixes every root of `p` in the splitting field of `f`, its restriction to `p` is
trivial. -/
theorem restrict_eq_one_of_forall_fixed {f p : F[X]}
    [Fact ((p.map (algebraMap F f.SplittingField)).Splits)] {σ : f.Gal}
    (hfix : ∀ y : p.rootSet f.SplittingField, σ (y : f.SplittingField) = y) :
    Gal.restrict p f.SplittingField σ = 1 := by
  apply galPerm_injective p
  rw [map_one]
  ext1 y
  apply (Gal.rootsEquivRootsAux p f.SplittingField).injective
  apply Subtype.ext
  rw [coe_rootsEquivRootsAux_galPerm_restrict, hfix]
  rfl

open Classical in
/-- **Restriction of a cycle to a factor.** Let `p ∣ f ≠ 0` and let `σ ∈ Gal(f)` act on the roots
of `f` as a cycle whose support consists of roots of `p`. Then the restriction of `σ` to `p` acts
on the roots of `p` as a cycle with the same support size, and every root of `p` it moves
corresponds to a moved root of `f`: it is a root of each `q` vanishing on the support of `σ`. -/
theorem galPerm_restrict_isCycle {f p : F[X]} (hf : f ≠ 0) (hpf : p ∣ f)
    [Fact ((p.map (algebraMap F f.SplittingField)).Splits)] {σ : f.Gal}
    (hσ : (galPerm f σ).IsCycle)
    (hsupp : ∀ z ∈ (galPerm f σ).support, aeval (z : f.SplittingField) p = 0) :
    (galPerm p (Gal.restrict p f.SplittingField σ)).IsCycle ∧
      (galPerm p (Gal.restrict p f.SplittingField σ)).support.card =
        (galPerm f σ).support.card ∧
      ∀ q : F[X], (∀ z ∈ (galPerm f σ).support, aeval (z : f.SplittingField) q = 0) →
        ∀ y ∈ (galPerm p (Gal.restrict p f.SplittingField σ)).support,
          aeval (y : p.SplittingField) q = 0 := by
  have hp0 : p ≠ 0 := ne_zero_of_dvd_ne_zero hf hpf
  let j : p.rootSet p.SplittingField → f.rootSet f.SplittingField := fun y =>
    ⟨Gal.rootsEquivRootsAux p f.SplittingField y, by
      have hy := (Gal.rootsEquivRootsAux p f.SplittingField y).2
      rw [mem_rootSet] at hy ⊢
      exact ⟨hf, aeval_eq_zero_of_dvd_aeval_eq_zero hpf hy.2⟩⟩
  have hjv : ∀ y, ((j y : f.SplittingField)) = Gal.rootsEquivRootsAux p f.SplittingField y :=
    fun _ => rfl
  have hj : Function.Injective j := fun y₁ y₂ h =>
    (Gal.rootsEquivRootsAux p f.SplittingField).injective
      (Subtype.ext (by rw [← hjv, ← hjv, h]))
  have hab : ∀ y, j (galPerm p (Gal.restrict p f.SplittingField σ) y) = galPerm f σ (j y) := by
    intro y
    apply Subtype.ext
    rw [hjv, coe_rootsEquivRootsAux_galPerm_restrict, galPerm_apply]
    try rfl
  have hrange : ∀ z, galPerm f σ z ≠ z → z ∈ Set.range j := by
    intro z hz
    have hroot := hsupp z (Equiv.Perm.mem_support.mpr hz)
    have hmem : (z : f.SplittingField) ∈ p.rootSet f.SplittingField :=
      mem_rootSet.mpr ⟨hp0, hroot⟩
    obtain ⟨y, hy⟩ := (Gal.rootsEquivRootsAux p f.SplittingField).surjective ⟨z, hmem⟩
    exact ⟨y, Subtype.ext (by rw [hjv, hy])⟩
  obtain ⟨h1, h2⟩ := isCycle_iff_and_card_support_eq_of_semiconj hj hab hrange
  refine ⟨h1.mpr hσ, h2, fun q hq y hy => ?_⟩
  have hy' : galPerm f σ (j y) ≠ j y := by
    rw [← hab]
    exact fun h => Equiv.Perm.mem_support.mp hy (hj h)
  have h3 := hq (j y) (Equiv.Perm.mem_support.mpr hy')
  rw [hjv] at h3
  change aeval (IsScalarTower.toAlgHom F p.SplittingField f.SplittingField
    (y : p.SplittingField)) q = 0 at h3
  rw [aeval_algHom_apply] at h3
  exact (IsScalarTower.toAlgHom F p.SplittingField f.SplittingField).toRingHom.injective
    (h3.trans (map_zero _).symm)

end Restriction

/-! ### Dominant factors -/

/-- `h` is a dominant factor of `f`: monic, irreducible, dividing `f`, of degree `> deg f / 2`
(the unfolded form of `ArithmeticOfJacobiPolynomials.IsDominantFactor`). -/
@[expose] def IsDominant (f h : ℚ[X]) : Prop :=
  h.Monic ∧ Irreducible h ∧ h ∣ f ∧ f.natDegree < 2 * h.natDegree

theorem isDominant_iff (f h : ℚ[X]) :
    IsDominant f h ↔ h.Monic ∧ Irreducible h ∧ h ∣ f ∧ f.natDegree < 2 * h.natDegree :=
  (Iff.rfl)

/-- A nonzero polynomial has at most one dominant factor. -/
theorem eq_of_isDominant {f h h' : ℚ[X]} (hf : f ≠ 0) (hh : IsDominant f h)
    (hh' : IsDominant f h') : h = h' := by
  obtain ⟨hm, hi, hd, hdeg⟩ := hh
  obtain ⟨hm', hi', hd', hdeg'⟩ := hh'
  by_contra hne
  have hndvd : ¬ h ∣ h' := fun hdvd =>
    hne (eq_of_monic_of_associated hm hm' (hi.associated_of_dvd hi' hdvd))
  have hcop : IsCoprime h h' := (hi.coprime_iff_not_dvd).mpr hndvd
  have hmul := natDegree_le_of_dvd (hcop.mul_dvd hd hd') hf
  rw [natDegree_mul hi.ne_zero hi'.ne_zero] at hmul
  omega

/-- A dominant factor and its cofactor have no common root. -/
theorem not_common_root {f h g : ℚ[X]} {κ : ℚ} (hf : f ≠ 0) (hh : IsDominant f h)
    (hfac : f = C κ * h * g) {L : Type*} [Field L] [Algebra ℚ L] {y : L}
    (hyh : aeval y h = 0) (hyg : aeval y g = 0) : False := by
  obtain ⟨hm, hi, -, hdeg⟩ := hh
  have hmin := minpoly.eq_of_irreducible_of_monic hi hyh hm
  have hhg : h ∣ g := hmin ▸ minpoly.dvd ℚ y hyg
  have hdvd : h * h ∣ f := by
    obtain ⟨k, hk⟩ := hhg
    exact ⟨C κ * k, by rw [hfac, hk]; ring⟩
  have h1 := natDegree_le_of_dvd hdvd hf
  rw [natDegree_mul hi.ne_zero hi.ne_zero] at h1
  omega

open Classical in
/-- A cycle in `Gal(f)` has a nonempty support, so `f ≠ 0`. -/
theorem ne_zero_of_isCycle {f : ℚ[X]} {σ : f.Gal} (hσ : (galPerm f σ).IsCycle) : f ≠ 0 := by
  obtain ⟨z, -, -⟩ := hσ
  exact (mem_rootSet.mp z.2).1

open Classical in
/-- If every moved root of `σ` is a root of `h ≠ 0`, the support of `σ` has at most
`deg h` elements. -/
theorem card_support_le_natDegree {f h : ℚ[X]} (hh0 : h ≠ 0) {σ : f.Gal}
    (hroots : ∀ z ∈ (galPerm f σ).support, aeval (z : f.SplittingField) h = 0) :
    (galPerm f σ).support.card ≤ h.natDegree := by
  have hZ : ((galPerm f σ).support.map ⟨Subtype.val, Subtype.val_injective⟩).val ⊆
      (h.map (algebraMap ℚ f.SplittingField)).roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [mem_roots_map hh0, ← aeval_def]
    exact hroots z hz
  have h1 := card_le_degree_of_subset_roots hZ
  rwa [natDegree_map, Finset.card_map] at h1

open Classical in
/-- **The large orbit.** A cycle of `Gal(f)` with support of size `d > n/2 ≥ deg f / 2` lies on
the roots of a dominant factor of `f` (the minimal polynomial of any moved root). -/
theorem exists_isDominant_of_isCycle {f : ℚ[X]} {n : ℕ} (hdeg : f.natDegree ≤ n) {σ : f.Gal}
    (hσ : (galPerm f σ).IsCycle) (hcard : n < 2 * (galPerm f σ).support.card) :
    ∃ h : ℚ[X], IsDominant f h ∧
      ∀ z ∈ (galPerm f σ).support, aeval (z : f.SplittingField) h = 0 := by
  obtain ⟨z₀, hz₀, hall⟩ := hσ
  have hx₀ := (mem_rootSet.mp z₀.2).2
  have hint : IsIntegral ℚ (z₀ : f.SplittingField) := Algebra.IsIntegral.isIntegral _
  have key : ∀ τ : f.Gal, aeval (τ (z₀ : f.SplittingField)) (minpoly ℚ (z₀ : f.SplittingField))
      = 0 := fun τ => by
    have := aeval_algHom_apply (τ : f.SplittingField ≃ₐ[ℚ] f.SplittingField).toAlgHom
      (z₀ : f.SplittingField) (minpoly ℚ (z₀ : f.SplittingField))
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hroots : ∀ z ∈ (galPerm f σ).support,
      aeval (z : f.SplittingField) (minpoly ℚ (z₀ : f.SplittingField)) = 0 := by
    intro z hz
    obtain ⟨i, hi⟩ := hall (Equiv.Perm.mem_support.mp hz)
    have e : (((galPerm f σ ^ i) z₀ : f.rootSet f.SplittingField) : f.SplittingField) =
        (σ ^ i) (z₀ : f.SplittingField) := by
      rw [← map_zpow, galPerm_apply]
      rfl
    rw [← hi, e]
    exact key (σ ^ i)
  have hh0 : minpoly ℚ (z₀ : f.SplittingField) ≠ 0 := minpoly.ne_zero hint
  have hle := card_support_le_natDegree hh0 hroots
  exact ⟨_, ⟨minpoly.monic hint, minpoly.irreducible hint, minpoly.dvd ℚ _ hx₀, by omega⟩,
    hroots⟩

/-- **The orbit `O` of the manuscript.** The roots, in the splitting field of `f`, of a dominant
factor `h` of `f` form exactly one Galois orbit: `h` is the minimal polynomial of each of its
roots (it is monic and irreducible), and two elements of a normal extension have the same
minimal polynomial iff they are Galois conjugate. So the dominant factor is the factor whose
root set is the orbit `O` carrying the long cycles. -/
theorem aeval_eq_zero_iff_mem_orbit {f h : ℚ[X]} (hh : IsDominant f h) {z₀ : f.SplittingField}
    (hz₀ : aeval z₀ h = 0) (z : f.SplittingField) :
    aeval z h = 0 ↔ z ∈ MulAction.orbit (f.SplittingField ≃ₐ[ℚ] f.SplittingField) z₀ := by
  have hmin : ∀ y : f.SplittingField, aeval y h = 0 → minpoly ℚ y = h := fun y hy =>
    (minpoly.eq_of_irreducible_of_monic hh.2.1 hy hh.1).symm
  constructor
  · intro hz
    exact (Normal.minpoly_eq_iff_mem_orbit f.SplittingField).mp
      ((hmin z hz).trans (hmin z₀ hz₀).symm)
  · intro hz
    have h1 := (Normal.minpoly_eq_iff_mem_orbit f.SplittingField).mpr hz
    rw [hmin z₀ hz₀] at h1
    rw [← h1]
    exact minpoly.aeval ℚ z

open Classical in
/-- Every long cycle of `Gal(f)` lies on the roots of the (unique) dominant factor. -/
theorem aeval_eq_zero_of_isDominant {f h : ℚ[X]} {n : ℕ} (hdeg : f.natDegree ≤ n)
    (hh : IsDominant f h) {σ : f.Gal} (hσ : (galPerm f σ).IsCycle)
    (hcard : n < 2 * (galPerm f σ).support.card) :
    ∀ z ∈ (galPerm f σ).support, aeval (z : f.SplittingField) h = 0 := by
  obtain ⟨h', hh', hroots⟩ := exists_isDominant_of_isCycle hdeg hσ hcard
  rw [eq_of_isDominant (ne_zero_of_isCycle hσ) hh hh']
  exact hroots

open Classical in
/-- A long cycle of `Gal(f)` restricts to a cycle of the same length in `Gal(h)`, `h` dominant. -/
theorem exists_isCycle_galPerm_dominant {f h : ℚ[X]} {n : ℕ} (hdeg : f.natDegree ≤ n)
    (hh : IsDominant f h) {σ : f.Gal} (hσ : (galPerm f σ).IsCycle)
    (hcard : n < 2 * (galPerm f σ).support.card) :
    ∃ τ : h.Gal, (galPerm h τ).IsCycle ∧
      (galPerm h τ).support.card = (galPerm f σ).support.card := by
  have hf := ne_zero_of_isCycle hσ
  have := fact_splits_of_dvd hf hh.2.2.1
  obtain ⟨h1, h2, -⟩ := galPerm_restrict_isCycle hf hh.2.2.1 hσ
    (aeval_eq_zero_of_isDominant hdeg hh hσ hcard)
  exact ⟨_, h1, h2⟩

open Classical in
/-- For `f = κ h g` with `h` dominant, a long cycle `σ ∈ Gal(f)` gives `ρ ∈ Gal(hg)` whose
restriction to `h` is a cycle of the same length and whose restriction to `g` is trivial (the
inertia element fixes every root outside the large orbit). -/
theorem exists_restrictProd_isCycle {f h g : ℚ[X]} {κ : ℚ} {n : ℕ} (hdeg : f.natDegree ≤ n)
    (hh : IsDominant f h) (hfac : f = C κ * h * g) {σ : f.Gal} (hσ : (galPerm f σ).IsCycle)
    (hcard : n < 2 * (galPerm f σ).support.card) :
    ∃ ρ : (h * g).Gal, (galPerm h (Gal.restrictProd h g ρ).1).IsCycle ∧
      (galPerm h (Gal.restrictProd h g ρ).1).support.card = (galPerm f σ).support.card ∧
      (Gal.restrictProd h g ρ).2 = 1 := by
  have hf := ne_zero_of_isCycle hσ
  have hP : h * g ∣ f := ⟨C κ, by rw [hfac]; ring⟩
  have hP0 : h * g ≠ 0 := ne_zero_of_dvd_ne_zero hf hP
  have hrootsh := aeval_eq_zero_of_isDominant hdeg hh hσ hcard
  have := fact_splits_of_dvd hf hP
  obtain ⟨c1, c2, c3⟩ := galPerm_restrict_isCycle hf hP hσ (fun z hz => by
    rw [aeval_mul, hrootsh z hz, zero_mul])
  have hsh := c3 h hrootsh
  set ρ := Gal.restrict (h * g) f.SplittingField σ with hρ
  have := fact_splits_of_dvd hP0 (dvd_mul_right h g)
  have := fact_splits_of_dvd hP0 (dvd_mul_left g h)
  obtain ⟨d1, d2, -⟩ := galPerm_restrict_isCycle hP0 (dvd_mul_right h g) c1 hsh
  have hg1 : Gal.restrict g (h * g).SplittingField ρ = 1 := by
    apply restrict_eq_one_of_forall_fixed
    intro y
    by_contra hne
    have hyP : (y : (h * g).SplittingField) ∈ (h * g).rootSet (h * g).SplittingField := by
      have hy := y.2
      rw [mem_rootSet] at hy ⊢
      exact ⟨hP0, by rw [aeval_mul, hy.2, mul_zero]⟩
    have hmem : (⟨y, hyP⟩ : (h * g).rootSet (h * g).SplittingField) ∈
        (galPerm (h * g) ρ).support := by
      rw [Equiv.Perm.mem_support]
      intro heq
      apply hne
      have := congrArg Subtype.val heq
      rw [galPerm_apply] at this
      exact this
    exact not_common_root hf hh hfac (hsh _ hmem) (mem_rootSet.mp y.2).2
  have e1 : (Gal.restrictProd h g ρ).1 = Gal.restrict h (h * g).SplittingField ρ := by
    simp only [Gal.restrictProd, Gal.restrictDvd_def, hP0, ↓reduceDIte]
    rfl
  have e2 : (Gal.restrictProd h g ρ).2 = Gal.restrict g (h * g).SplittingField ρ := by
    simp only [Gal.restrictProd, Gal.restrictDvd_def, hP0, ↓reduceDIte]
    rfl
  refine ⟨ρ, ?_, ?_, ?_⟩
  · rw [e1]; exact d1
  · rw [e1, d2, c2]
  · rw [e2, hg1]

/-! ### Group theory -/

/-- **`S_M` from long cycles** (proof of Theorem 1.6). A transitive `G ≤ Sym(α)` such that every
`2 ≤ s < |α|` fails to divide the length of some cycle of `G` of length `> |α|/2` is primitive
(Lemma 5.3); if moreover it contains an even-length cycle fixing at least three points, Jones's
theorem and the sign give `G = Sym(α)`.

Conditional on [Jones, Corollary 1.3], taken as the hypothesis `hJones`. -/
theorem eq_top_of_long_cycles (hJones : JonesCycleTheorem) {α : Type} [Fintype α]
    [DecidableEq α] (G : Subgroup (Equiv.Perm α)) (hG : MulAction.IsPretransitive G α)
    (hblock : ∀ s : ℕ, 2 ≤ s → s < Fintype.card α → ∃ σ ∈ G, σ.IsCycle ∧
      Fintype.card α < 2 * σ.support.card ∧ ¬ s ∣ σ.support.card)
    {τ : Equiv.Perm α} (hτG : τ ∈ G) (hτ : τ.IsCycle) (hτe : Even τ.support.card)
    (hτ3 : 3 ≤ Fintype.card α - τ.support.card) : G = ⊤ := by
  have hprim : MulAction.IsPreprimitive G α := by
    have := hG
    refine ⟨fun {B} hB => ?_⟩
    by_contra hnt
    simp only [MulAction.IsTrivialBlock, not_or] at hnt
    obtain ⟨hns, hnu⟩ := hnt
    have hb1 : 1 < B.ncard :=
      Set.one_lt_ncard_iff_nontrivial.mpr (Set.not_subsingleton_iff.mp hns)
    have hbN : B.ncard < Fintype.card α := by
      have := Set.ncard_lt_card hnu
      rwa [Nat.card_eq_fintype_card] at this
    obtain ⟨σ, hσG, hσ, hd, hnd⟩ := hblock B.ncard hb1 hbN
    exact hnd (IsBlock.ncard_dvd_card_support_of_isCycle hG hB hb1 hbN hσG hσ hd)
  have hA : alternatingGroup α ≤ G := hJones α G hprim τ hτG hτ hτ3
  have hsign : Equiv.Perm.sign τ = -1 := by
    rw [hτ.sign, hτe.neg_one_pow]
  rw [eq_top_iff]
  intro π _
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
  · exact hA (Equiv.Perm.mem_alternatingGroup.mpr h)
  · have hπτ : π * τ⁻¹ ∈ G := hA (Equiv.Perm.mem_alternatingGroup.mpr (by
      rw [map_mul, map_inv, h, hsign]; rfl))
    simpa using G.mul_mem hπτ hτG

open Classical in
/-- **The product decomposition** (proof of Theorem 1.6). If `Gal(h) = S_M` and some `ρ ∈ Gal(hg)`
restricts to an even-length cycle `2 ≤ d < M` on the roots of `h` and trivially to `g`, then
restriction `Gal(hg) → Gal(h) × Gal(g)` is bijective: its image projects onto both factors, the
kernel on the second factor is normal in `Gal(h) = S_M` and contains the even cycle, hence is
everything (Lemma 5.5(1)). -/
theorem restrictProd_bijective {h g : ℚ[X]} (hP0 : h * g ≠ 0) (hS : GaloisGroupIsSymmetric h)
    {ρ : (h * g).Gal} {d : ℕ} (hρ1 : (galPerm h (Gal.restrictProd h g ρ).1).IsCycle)
    (hρc : (galPerm h (Gal.restrictProd h g ρ).1).support.card = d) (heven : Even d)
    (hd2 : 2 ≤ d) (hdM : d < Fintype.card (h.rootSet h.SplittingField))
    (hρ2 : (Gal.restrictProd h g ρ).2 = 1) : Function.Bijective (Gal.restrictProd h g) := by
  refine ⟨Gal.restrictProd_injective (p := h) (q := g), ?_⟩
  have hsurj1 : ∀ x : h.Gal, ∃ w, (Gal.restrictProd h g w).1 = x :=
    Gal.restrictDvd_surjective (dvd_mul_right h g) hP0
  have hsurj2 : ∀ y : g.Gal, ∃ w, (Gal.restrictProd h g w).2 = y :=
    Gal.restrictDvd_surjective (dvd_mul_left g h) hP0
  set N : Subgroup h.Gal := (Gal.restrictProd h g).range.comap (MonoidHom.inl h.Gal g.Gal)
    with hNdef
  have hmemN : ∀ x : h.Gal, x ∈ N ↔ ∃ v, Gal.restrictProd h g v = (x, 1) := by
    intro x
    rw [hNdef, Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.inl_apply]
  have hN : N.Normal := by
    refine ⟨fun x hx y => ?_⟩
    obtain ⟨w, hw⟩ := hsurj1 y
    obtain ⟨v, hv⟩ := (hmemN x).mp hx
    refine (hmemN _).mpr ⟨w * v * w⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hv]
    ext
    · simp [hw]
    · simp
  have hρN : (Gal.restrictProd h g ρ).1 ∈ N :=
    (hmemN _).mpr ⟨ρ, Prod.ext rfl hρ2⟩
  have htop := eq_top_of_normal_of_isCycle_of_even
    (hN.map (galPerm h) ((galoisGroupIsSymmetric_iff h).mp hS).2)
    (Subgroup.mem_map_of_mem _ hρN) hρ1 hρc heven hd2 hdM
  have hall : ∀ x : h.Gal, x ∈ N := by
    intro x
    have hx : galPerm h x ∈ N.map (galPerm h) := by rw [htop]; trivial
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hx
    rwa [galPerm_injective h hxx'] at hx'
  rintro ⟨x, y⟩
  obtain ⟨w, hw⟩ := hsurj2 y
  obtain ⟨v, hv⟩ := (hmemN _).mp (hall (x * ((Gal.restrictProd h g w).1)⁻¹))
  refine ⟨v * w, ?_⟩
  rw [map_mul, hv]
  ext
  · simp
  · simp [hw]

/-! ### The Jacobi polynomials -/

/-- The denominator condition of Theorem 1.6, unfolded
(`ArithmeticOfJacobiPolynomials.JacobiDenominatorCondition`). -/
@[expose] def DenomCond (α β : ℚ) : Prop :=
  Even (α + β).den ∧ max α.den β.den ≤ (α + β).den ∧
    (∀ k : ℕ, α ≠ -((k : ℚ) + 1)) ∧ ∀ k : ℕ, β ≠ -((k : ℚ) + 1)

theorem denomCond_iff (α β : ℚ) : DenomCond α β ↔ Even (α + β).den ∧
    max α.den β.den ≤ (α + β).den ∧ (∀ k : ℕ, α ≠ -((k : ℚ) + 1)) ∧
      ∀ k : ℕ, β ≠ -((k : ℚ) + 1) :=
  (Iff.rfl)

/-- The constant `B = |r| + |a| + |b| + 4D + 11 > |r| + |a| + |b| + 4D + 10` of the proof of
Theorem 1.6, for `α = a/u`, `β = b/v`, `α + β = r/D`. -/
def cycleBound (α β : ℚ) : ℕ :=
  (α + β).num.natAbs + α.num.natAbs + β.num.natAbs + 4 * (α + β).den + 11

theorem cycleBound_eq (α β : ℚ) : cycleBound α β =
    (α + β).num.natAbs + α.num.natAbs + β.num.natAbs + 4 * (α + β).den + 11 := (rfl)

theorem cycleBound_bounds (α β : ℚ) :
    |(α + β).num| + 4 * ((α + β).den : ℤ) + 10 < cycleBound α β ∧
      |α.num| < cycleBound α β ∧ |β.num| < cycleBound α β ∧ |(α + β).num| < cycleBound α β := by
  have h1 := abs_nonneg (α + β).num
  have h2 := abs_nonneg α.num
  have h3 := abs_nonneg β.num
  rw [cycleBound_eq]
  push_cast [Int.natCast_natAbs]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem gcd_num_den (q : ℚ) : Int.gcd q.num (q.den : ℤ) = 1 := by
  rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
  exact q.reduced

/-- **The primes (5.20) satisfy the hypotheses of Proposition 5.2.** -/
theorem jacobiCycleHypotheses_of_eligible {α β : ℚ} (hcond : DenomCond α β) {n p : ℕ}
    (hp : p.Prime) (h1 : (α + β).den * n + cycleBound α β < p)
    (h2 : 2 * (p + cycleBound α β) ≤ 3 * ((α + β).den * n))
    (h3 : (p : ℤ) ≡ (α + β).num [ZMOD (α + β).den]) :
    JacobiCycleHypotheses p n α.num α.den β.num β.den (α + β).den (α + β).num := by
  obtain ⟨-, hmax, hα, hβ⟩ := hcond
  obtain ⟨hB, haB, hbB, -⟩ := cycleBound_bounds α β
  have hB11 : 4 * (α + β).den + 11 ≤ cycleBound α β := by rw [cycleBound_eq]; omega
  have hDpos := (α + β).den_pos
  have huD : α.den ≤ (α + β).den := le_of_max_le_left hmax
  have hvD : β.den ≤ (α + β).den := le_of_max_le_right hmax
  have hnDn : n ≤ (α + β).den * n := Nat.le_mul_of_pos_left n hDpos
  have hDp : (α + β).den < p := by omega
  have hu : (0 : ℤ) < α.den := by exact_mod_cast α.den_pos
  have hv : (0 : ℤ) < β.den := by exact_mod_cast β.den_pos
  have hD0 : (0 : ℤ) < (α + β).den := by exact_mod_cast hDpos
  have h1' : ((α + β).den : ℤ) * n + cycleBound α β < p := by exact_mod_cast h1
  have h2' : 2 * ((p : ℤ) + cycleBound α β) ≤ 3 * ((α + β).den * n) := by exact_mod_cast h2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hr1 := neg_abs_le (α + β).num
  have hr2 := le_abs_self (α + β).num
  have hb := cycleLength_bounds hDpos hB h1 h2 h3
  -- the small factors
  have hsmall : ∀ {γ : ℚ}, γ.den ≤ (α + β).den → |γ.num| < cycleBound α β →
      (∀ k : ℕ, γ ≠ -((k : ℚ) + 1)) → ∀ k : ℕ, 1 ≤ k → k ≤ n →
        0 < |(γ.den : ℤ) * k + γ.num| ∧ |(γ.den : ℤ) * k + γ.num| < p := by
    intro γ hγD hγB hγ k hk1 hkn
    have hne : (γ.den : ℤ) * k + γ.num ≠ 0 := by
      intro h0
      apply hγ (k - 1)
      have hq : (γ.num : ℚ) = -((γ.den : ℚ) * k) := by
        have := congrArg (Int.cast : ℤ → ℚ) h0
        push_cast at this
        linarith
      have hk : ((k - 1 : ℕ) : ℚ) + 1 = k := by
        rw [Nat.cast_sub hk1]; push_cast; ring
      rw [hk]
      calc γ = (γ.num : ℚ) / (γ.den : ℚ) := (Rat.num_div_den γ).symm
        _ = -(k : ℚ) := by
          rw [hq, neg_div, mul_div_cancel_left₀ _ (by exact_mod_cast γ.den_nz)]
    have hab : |(γ.den : ℤ) * k + γ.num| ≤ (γ.den : ℤ) * k + |γ.num| := by
      calc _ ≤ |(γ.den : ℤ) * k| + |γ.num| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg (by positivity)]
    have hku : (γ.den : ℤ) * k ≤ (α + β).den * n :=
      mul_le_mul (by exact_mod_cast hγD) (by exact_mod_cast hkn) (by positivity)
        (by positivity)
    exact ⟨abs_pos.mpr hne, by linarith⟩
  refine ⟨hp, by omega, hu, hv, hD0, ?_, by omega, ?_, hsmall huD haB hα, hsmall hvD hbB hβ,
    by linarith, by linarith, h3, ?_, ?_⟩
  · push_cast
    rw [Rat.num_div_den, Rat.num_div_den, mul_comm]
    exact (Rat.mul_den_eq_num _).symm
  · intro hdvd
    have hDp' : ((α + β).den : ℤ) < p := by exact_mod_cast hDp
    have huD' : (α.den : ℤ) ≤ (α + β).den := by exact_mod_cast huD
    have hvD' : (β.den : ℤ) ≤ (α + β).den := by exact_mod_cast hvD
    rcases hpZ.dvd_or_dvd hdvd with h | h
    · rcases hpZ.dvd_or_dvd h with h | h
      · have := Int.le_of_dvd hu h; omega
      · have := Int.le_of_dvd hv h; omega
    · have := Int.le_of_dvd hD0 h; omega
  · rw [jacobiCycleIndex_eq]; linarith [hb.2]
  · rw [jacobiCycleIndex_eq]; linarith [hb.1]

open Classical in
/-- **Proposition 5.2 for the primes (5.20).** Each such prime gives a single `d_p`-cycle in
`Gal(P_n^{(α,β)}/ℚ)`, `d_p = 2n + 1 - (p - r)/D` ((5.21), §5.5). -/
theorem exists_isCycle_of_eligible {α β : ℚ} (hcond : DenomCond α β) {n p : ℕ}
    (hp : p.Prime) (h1 : (α + β).den * n + cycleBound α β < p)
    (h2 : 2 * (p + cycleBound α β) ≤ 3 * ((α + β).den * n))
    (h3 : (p : ℤ) ≡ (α + β).num [ZMOD (α + β).den]) :
    ∃ σ : (jacobiP α β n).Gal, (galPerm _ σ).IsCycle ∧
      ((galPerm _ σ).support.card : ℤ) = 2 * n + 1 - ((p : ℤ) - (α + β).num) / (α + β).den := by
  have H := jacobiCycleHypotheses_of_eligible hcond hp h1 h2 h3
  have hb := cycleLength_bounds (α + β).den_pos (cycleBound_bounds α β).1 h1 h2 h3
  have hidx := H.cast_index
  rw [jacobiCycleIndex_eq] at hidx
  generalize ((p : ℤ) - (α + β).num) / ((α + β).den : ℤ) = k at hidx hb ⊢
  have hd : 2 ≤ n + 1 - jacobiCycleIndexNat p n (α + β).den (α + β).num := by omega
  have eα : ((α.num : ℚ) / ((α.den : ℤ) : ℚ)) = α := by push_cast; exact Rat.num_div_den α
  have eβ : ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) = β := by push_cast; exact Rat.num_div_den β
  have key := exists_isCycle_galPerm_jacobiP H hd
  rw [eα, eβ] at key
  obtain ⟨σ, hσ, hcard⟩ := key
  refine ⟨σ, hσ, ?_⟩
  rw [hcard]
  omega

/-- Basic facts on `D` and `r` under the denominator condition. -/
theorem denomCond_facts {α β : ℚ} (hcond : DenomCond α β) :
    2 ≤ (α + β).den ∧ Int.gcd (α + β).num ((α + β).den : ℤ) = 1 ∧
      Int.gcd ((α + β).num + (α + β).den) ((2 * (α + β).den : ℕ) : ℤ) = 1 := by
  obtain ⟨hDe, -⟩ := hcond
  have hpos := (α + β).den_pos
  have hr := gcd_num_den (α + β)
  refine ⟨by obtain ⟨k, hk⟩ := hDe; omega, hr, ?_⟩
  rw [← Int.isCoprime_iff_gcd_eq_one] at hr ⊢
  have hDe' : Even ((α + β).den : ℤ) := by exact_mod_cast hDe
  have hrodd : Odd (α + β).num := by
    rw [← Int.not_even_iff_odd]
    intro hre
    have h2r : (2 : ℤ) ∣ (α + β).num := even_iff_two_dvd.mp hre
    have h2D : (2 : ℤ) ∣ ((α + β).den : ℤ) := even_iff_two_dvd.mp hDe'
    have := Int.dvd_gcd (c := 2) h2r h2D
    rw [Int.isCoprime_iff_gcd_eq_one.mp hr] at this
    omega
  have h2 : IsCoprime ((α + β).num + (α + β).den) 2 := by
    obtain ⟨m, hm⟩ := hrodd.add_even hDe'
    rw [hm]
    exact ⟨1, -m, by ring⟩
  have hD : IsCoprime ((α + β).num + (α + β).den) ((α + β).den : ℤ) := by
    have := hr.add_mul_right_left 1
    simpa using this
  push_cast
  exact h2.mul_right hD

/-- **Theorem 1.6, the dominant factor** (unfolded form). For all large `n`, `P_n^{(α,β)}` has a
unique dominant factor.

Conditional on [BMOR, Proposition 6.19] (through Lemma 5.13), taken as the hypothesis `h619`. -/
theorem exists_unique_isDominant_jacobiP (h619 : BMORLargeModulusPrimeCounting) {α β : ℚ}
    (hcond : DenomCond α β) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ h : ℚ[X], IsDominant (jacobiP α β n) h ∧
      ∀ h' : ℚ[X], IsDominant (jacobiP α β n) h' → h' = h := by
  classical
  obtain ⟨hD2, hr, -⟩ := denomCond_facts hcond
  obtain ⟨C₀, N, hN⟩ := exists_prime_near h619 hD2 hr (cycleBound_bounds α β).2.2.2 one_pos
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨p, hp, h1, h2, h3, -⟩ := hN n hn
  obtain ⟨σ, hσ, hcard⟩ := exists_isCycle_of_eligible hcond hp h1 h2 h3
  have hb := cycleLength_bounds (α + β).den_pos (cycleBound_bounds α β).1 h1 h2 h3
  rw [← hcard] at hb
  obtain ⟨h, hh, -⟩ := exists_isDominant_of_isCycle (natDegree_jacobiP_le α β n) hσ
    (by omega)
  exact ⟨h, hh, fun h' hh' => eq_of_isDominant (ne_zero_of_isCycle hσ) hh' hh⟩

/-- **Theorem 1.6, the degree of the dominant factor** (unfolded form). For every `A > 0`,
`n - M_n = O(n/(log n)^A)`.

Conditional on [BMOR, Proposition 6.19] (through Lemma 5.13), taken as the hypothesis `h619`. -/
theorem natDegree_isDominant_jacobiP (h619 : BMORLargeModulusPrimeCounting) {α β : ℚ}
    (hcond : DenomCond α β) :
    ∀ A : ℝ, 0 < A → ∃ (Cst : ℝ) (N : ℕ), ∀ n ≥ N, ∀ h : ℚ[X],
      IsDominant (jacobiP α β n) h → ((n : ℝ) - h.natDegree) ≤ Cst * n / Real.log n ^ A := by
  classical
  intro A hA
  obtain ⟨hD2, hr, -⟩ := denomCond_facts hcond
  obtain ⟨C₀, N, hN⟩ := exists_prime_near h619 hD2 hr (cycleBound_bounds α β).2.2.2 hA
  refine ⟨C₀, N, fun n hn h hh => ?_⟩
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := hN n hn
  obtain ⟨σ, hσ, hcard⟩ := exists_isCycle_of_eligible hcond hp h1 h2 h3
  have hb := cycleLength_bounds (α + β).den_pos (cycleBound_bounds α β).1 h1 h2 h3
  rw [← hcard] at hb h4
  have hroots := aeval_eq_zero_of_isDominant (natDegree_jacobiP_le α β n) hh hσ (by omega)
  have hle := card_support_le_natDegree hh.2.1.ne_zero hroots
  have hle' : ((galPerm _ σ).support.card : ℝ) ≤ h.natDegree := by exact_mod_cast hle
  push_cast at h4
  linarith

open Classical in
/-- **Theorem 1.6, `Gal(h_n/ℚ) = S_{M_n}` and the product** (unfolded form). For all large `n`
and every factorization `P_n^{(α,β)} = κ h g` with `h` dominant, `Gal(h/ℚ) = S_{M_n}` and
restriction `Gal(hg/ℚ) → Gal(h/ℚ) × Gal(g/ℚ)` is bijective (equivalently, the splitting fields of
`h` and `g` are linearly disjoint and `Gal(f_n/ℚ) = S_{M_n} × Gal(g_n/ℚ)`).

Conditional on [BMOR, Corollary 1.7], [BMOR, Proposition 6.19], Brun–Titchmarsh [MV, Theorem 2]
and [Jones, Corollary 1.3], taken as the hypotheses `hBMOR`, `h619`, `hBT`, `hJones`. -/
theorem galoisGroupIsSymmetric_isDominant_jacobiP (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) {α β : ℚ} (hcond : DenomCond α β) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ h g : ℚ[X], ∀ κ : ℚ, IsDominant (jacobiP α β n) h → g.Monic →
      jacobiP α β n = C κ * h * g →
      GaloisGroupIsSymmetric h ∧ Function.Bijective (Gal.restrictProd h g) := by
  obtain ⟨hD2, hr, hgc⟩ := denomCond_facts hcond
  have hDpos := (α + β).den_pos
  have hBb := cycleBound_bounds α β
  have ev1 := eventually_exists_prime_not_dvd hBMOR h619 hBT (B := cycleBound α β) hD2
    hcond.1 hr
  have ev2 := eventually_exists_prime_upper hBMOR h619 (B := cycleBound α β) hD2 hgc
  obtain ⟨C₀, N₃, hN₃⟩ := exists_prime_near h619 hD2 hr hBb.2.2.2 one_pos
  have ev3 := eventually_le_log_natCast (10 * |C₀| + 1)
  have ev4 := eventually_ge_atTop (N₃ + 100 * ((α + β).num.natAbs + 1) + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ev1.and (ev2.and (ev3.and ev4)))
  refine ⟨N, fun n hn h g κ hh _ hfac => ?_⟩
  obtain ⟨H1, ⟨pe, hpe, he1, he2, he3, he4⟩, hL, hn'⟩ := hN n hn
  have hdeg := natDegree_jacobiP_le α β n
  -- every prime of (5.20) gives a long cycle
  have hcyc : ∀ p : ℕ, p.Prime → (α + β).den * n + cycleBound α β < p →
      2 * (p + cycleBound α β) ≤ 3 * ((α + β).den * n) →
      (p : ℤ) ≡ (α + β).num [ZMOD (α + β).den] → ∃ σ : (jacobiP α β n).Gal,
        (galPerm _ σ).IsCycle ∧ n < 2 * (galPerm _ σ).support.card ∧
        ((galPerm _ σ).support.card : ℤ) =
          2 * n + 1 - ((p : ℤ) - (α + β).num) / (α + β).den := by
    intro p hp h1 h2 h3
    obtain ⟨σ, hσ, hcard⟩ := exists_isCycle_of_eligible hcond hp h1 h2 h3
    have hb := cycleLength_bounds hDpos hBb.1 h1 h2 h3
    rw [← hcard] at hb
    exact ⟨σ, hσ, by omega, hcard⟩
  -- the near prime: `M ≥ 0.9 n`
  obtain ⟨p₃, hp₃, h31, h32, h33, h34⟩ := hN₃ n (by omega)
  obtain ⟨σ₃, hσ₃, hσ₃n, hσ₃c⟩ := hcyc p₃ hp₃ h31 h32 h33
  have hf := ne_zero_of_isCycle hσ₃
  have hM3 := card_support_le_natDegree hh.2.1.ne_zero
    (aeval_eq_zero_of_isDominant hdeg hh hσ₃ hσ₃n)
  rw [← hσ₃c, Real.rpow_one] at h34
  push_cast at h34
  have hn100 : (100 : ℝ) ≤ n := by
    have : 100 ≤ n := by omega
    exact_mod_cast this
  have hlogpos : 0 < Real.log n := by linarith [abs_nonneg C₀]
  have hCn : C₀ * n / Real.log n ≤ 0.1 * n := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n)
      (by linarith [le_abs_self C₀] : (0 : ℝ) ≤ Real.log n - 10 * C₀)]
  have hM3' : ((galPerm _ σ₃).support.card : ℝ) ≤ h.natDegree := by exact_mod_cast hM3
  have hM9 : 0.9 * (n : ℝ) ≤ h.natDegree := by linarith
  -- the even cycle in the upper subinterval
  obtain ⟨he3', heven⟩ := modEq_and_even_of_modEq_add (n := n) hDpos he4
  obtain ⟨σe, hσe, hσen, hσec⟩ := hcyc pe hpe he1 he2 he3'
  have hup := cycleLength_le_of_upper hDpos he3 he3' (by
    have h0 : ((α + β).num.natAbs : ℤ) = |(α + β).num| := Int.natCast_natAbs _
    have h1 : 100 * ((α + β).num.natAbs + 1) ≤ n := by omega
    have h2 : (100 * (((α + β).num.natAbs : ℤ) + 1) : ℤ) ≤ n := by exact_mod_cast h1
    rw [← h0]
    exact h2)
  rw [← hσec] at hup heven
  have hupr : (100 : ℝ) * ((galPerm _ σe).support.card) ≤ 61 * n := by exact_mod_cast hup
  -- the dominant factor and its Galois group
  have hMdeg : h.natDegree ≤ n := (natDegree_le_of_dvd hh.2.2.1 hf).trans hdeg
  have hcardM : Fintype.card (h.rootSet h.SplittingField) = h.natDegree :=
    card_rootSet_of_irreducible hh.2.1
  obtain ⟨τe, hτe, hτec⟩ := exists_isCycle_galPerm_dominant hdeg hh hσe hσen
  have hd3 : 3 ≤ h.natDegree - (galPerm _ σe).support.card := by
    have : (galPerm _ σe).support.card + 3 ≤ h.natDegree := by
      have hr' : ((galPerm _ σe).support.card : ℝ) + 3 ≤ h.natDegree := by linarith
      exact_mod_cast hr'
    omega
  have hS : GaloisGroupIsSymmetric h := by
    rw [galoisGroupIsSymmetric_iff_range_eq_top]
    refine eq_top_of_long_cycles hJones _ (isPretransitive_range_galPerm hh.2.1) ?_
      (τ := galPerm h τe) ⟨τe, rfl⟩ hτe (by rw [hτec]; exact (Int.even_coe_nat _).mp heven)
      (by rw [hτec, hcardM]; exact hd3)
    intro s hs2 hsM
    rw [hcardM] at hsM
    obtain ⟨p, hp, h1, h2, h3, hnd⟩ := H1 s hs2 (by omega)
    obtain ⟨σ, hσ, hσn, hσc⟩ := hcyc p hp h1 h2 h3
    obtain ⟨τ, hτ, hτc⟩ := exists_isCycle_galPerm_dominant hdeg hh hσ hσn
    refine ⟨galPerm h τ, ⟨τ, rfl⟩, hτ, by rw [hcardM, hτc]; omega, ?_⟩
    rw [hτc]
    intro hdvd
    apply hnd
    rw [← hσc]
    exact_mod_cast hdvd
  refine ⟨hS, ?_⟩
  obtain ⟨ρ, hρ1, hρc, hρ2⟩ := exists_restrictProd_isCycle hdeg hh hfac hσe hσen
  have hP0 : h * g ≠ 0 := by
    intro h0
    apply hf
    rw [hfac, mul_assoc, h0, mul_zero]
  exact restrictProd_bijective hP0 hS hρ1 hρc ((Int.even_coe_nat _).mp heven) (by omega)
    (by rw [hcardM]; omega) hρ2

end FixedRationalParameters

end ArithmeticOfJacobiPolynomials
