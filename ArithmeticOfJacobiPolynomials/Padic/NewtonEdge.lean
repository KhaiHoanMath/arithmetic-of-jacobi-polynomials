/- Assembled by AxiomProver. -/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Root valuations over `ℚ_p` and the single-edge criterion

Roots of polynomials over `ℚ_p` are taken in the algebraic closure `PadicAlgCl p`, whose norm
is the spectral norm extending the `p`-adic norm.

* `norm_pow_natDegree_eq_norm_coeff_zero`: a root `z` of a monic irreducible `g ∈ ℚ_p[X]`
  satisfies `‖z‖ ^ deg g = ‖g(0)‖`;
* `norm_coeff_le_of_aeval_eq_zero`: the coefficients of such a `g` satisfy
  `‖g_i‖ ≤ ‖z‖ ^ (deg g - i)`;
* `exists_ne_le_of_irreducible_factor`: for `f = ∑ b_j X^j ∈ ℚ[X]` with `b_0 ≠ 0` and a monic
  irreducible factor `g` of `f` over `ℚ_p` of degree `d` with `k = v(g(0))`, the minimum of
  `d·v(b_j) + j·k` over the nonzero coefficients is attained at least twice (the
  "dominant term" principle: a root `z` has `‖z‖^d = p^{-k}`);
* `irreducible_map_padic_of_single_edge`: the single-edge criterion. If `f` is monic of
  degree `n ≥ 1`, `H = v(b_0)`, `gcd(H, n) = 1` and `n·v(b_j) > H(n - j)` for every
  `0 < j < n` with `b_j ≠ 0`, then `f` is irreducible over `ℚ_p`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- The norm of a nonzero rational in `PadicAlgCl p`. -/
theorem norm_ratCast_padicAlgCl (q : ℚ) (hq : q ≠ 0) :
    ‖(algebraMap ℚ_[p] (PadicAlgCl p) (q : ℚ_[p]))‖ = (p : ℝ) ^ (-padicValRat p q) := by
  rw [PadicAlgCl.norm_extends, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq),
    Padic.valuation_ratCast]

/-- A root `z` of a monic irreducible `g ∈ ℚ_p[X]` satisfies `‖z‖ ^ deg g = ‖g(0)‖`. -/
theorem norm_pow_natDegree_eq_norm_coeff_zero {g : ℚ_[p][X]} (hg : g.Monic)
    (hirr : Irreducible g) {z : PadicAlgCl p} (hz : aeval z g = 0) :
    ‖z‖ ^ g.natDegree = ‖(algebraMap ℚ_[p] (PadicAlgCl p) (g.coeff 0))‖ := by
  have hmin : g = minpoly ℚ_[p] z := minpoly.eq_of_irreducible_of_monic hirr hz hg
  have hd : (g.natDegree : ℝ) ≠ 0 := by exact_mod_cast hirr.natDegree_pos.ne'
  have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (PadicAlgCl p) z
  rw [PadicAlgCl.spectralNorm_eq, ← hmin] at h
  rw [PadicAlgCl.norm_extends, h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    one_div, inv_mul_cancel₀ hd, Real.rpow_one]

/-- The coefficients of a monic irreducible `g ∈ ℚ_p[X]` with root `z` satisfy
`‖g_i‖ ≤ ‖z‖ ^ (deg g - i)`. -/
theorem norm_coeff_le_of_aeval_eq_zero {g : ℚ_[p][X]} (hg : g.Monic)
    (hirr : Irreducible g) {z : PadicAlgCl p} (hz : aeval z g = 0) (i : ℕ) :
    ‖(algebraMap ℚ_[p] (PadicAlgCl p) (g.coeff i))‖ ≤ ‖z‖ ^ (g.natDegree - i) := by
  rw [PadicAlgCl.norm_extends]
  rcases lt_or_ge i g.natDegree with hi | hi
  · have hmin : g = minpoly ℚ_[p] z := minpoly.eq_of_irreducible_of_monic hirr hz hg
    have hsp : spectralValue g = ‖z‖ := by
      rw [← PadicAlgCl.spectralNorm_eq, hmin]; rfl
    have hterm : spectralValueTerms g i ≤ spectralValue g :=
      le_ciSup (spectralValueTerms_bddAbove g) i
    rw [spectralValueTerms_of_lt_natDegree g hi, hsp] at hterm
    have hm : (0 : ℝ) < (g.natDegree - i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hi
    have hm' : ((g.natDegree : ℝ) - i) = ((g.natDegree - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hi.le]
    rw [hm'] at hterm
    calc ‖g.coeff i‖ = (‖g.coeff i‖ ^ (1 / ((g.natDegree - i : ℕ) : ℝ))) ^
          (g.natDegree - i) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div,
            inv_mul_cancel₀ hm.ne', Real.rpow_one]
      _ ≤ ‖z‖ ^ (g.natDegree - i) :=
          pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hterm _
  · rcases hi.eq_or_lt with hi | hi
    · subst hi; simp [hg.coeff_natDegree]
    · rw [coeff_eq_zero_of_natDegree_lt hi]; simp

/-- The dominant-term principle at a root. Let `f ∈ ℚ[X]` and let `z` be a root of `f` in
`PadicAlgCl p` with `‖z‖ ^ d = p ^ (-k)`, `d ≥ 1`. Then no index `i` with `b_i ≠ 0` is the
unique minimizer of `d·v(b_j) + j·k`. -/
theorem exists_ne_le_of_aeval_eq_zero {f : ℚ[X]} {z : PadicAlgCl p}
    (hz : aeval z (f.map (algebraMap ℚ ℚ_[p])) = 0) {d : ℕ} {k : ℤ} (hd : 0 < d)
    (hzk : ‖z‖ ^ d = (p : ℝ) ^ (-k)) (i : ℕ) (hi : f.coeff i ≠ 0) :
    ∃ j, j ≠ i ∧ f.coeff j ≠ 0 ∧
      (d : ℤ) * padicValRat p (f.coeff j) + j * k ≤ d * padicValRat p (f.coeff i) + i * k := by
  by_contra hcon
  push Not at hcon
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set t : ℕ → PadicAlgCl p := fun j =>
    algebraMap ℚ_[p] (PadicAlgCl p) ((f.coeff j : ℚ) : ℚ_[p]) * z ^ j with ht
  have hnorm : ∀ j, f.coeff j ≠ 0 →
      ‖t j‖ ^ d = (p : ℝ) ^ (-((d : ℤ) * padicValRat p (f.coeff j) + j * k)) := by
    intro j hj
    rw [ht]
    simp only [norm_mul, norm_pow, mul_pow]
    rw [norm_ratCast_padicAlgCl _ hj, ← pow_mul, mul_comm j d, pow_mul, hzk,
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hp0.ne']
    congr 1; ring
  have hti : 0 < ‖t i‖ := by
    have := hnorm i hi
    rcases (norm_nonneg (t i)).eq_or_lt with h | h
    · rw [← h, zero_pow hd.ne'] at this
      exact absurd this.symm (zpow_pos hp0 _).ne'
    · exact h
  have hlt : ∀ j, j ≠ i → ‖t j‖ < ‖t i‖ := by
    intro j hj
    by_cases hj0 : f.coeff j = 0
    · have : t j = 0 := by simp [ht, hj0]
      rw [this, norm_zero]; exact hti
    · have h1 := hnorm j hj0
      have h2 := hnorm i hi
      have : ‖t j‖ ^ d < ‖t i‖ ^ d := by
        rw [h1, h2]
        exact zpow_lt_zpow_right₀ hp1 (by linarith [hcon j hj hj0])
      exact lt_of_pow_lt_pow_left₀ d (norm_nonneg _) this
  -- the sum over all coefficients
  set N := (f.map (algebraMap ℚ ℚ_[p])).natDegree + 1 with hN
  have hsum : ∑ j ∈ Finset.range (N + i), t j = 0 := by
    have hz' := hz
    rw [aeval_eq_sum_range' (n := N + i) (by omega)] at hz'
    rw [← hz']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ht, coeff_map, Algebra.smul_def]
    rfl
  have hmem : i ∈ Finset.range (N + i) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hmem] at hsum
  have hrest : ‖∑ j ∈ (Finset.range (N + i)).erase i, t j‖ < ‖t i‖ := by
    obtain ⟨j0, hj0, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le
      ((Finset.range (N + i)).erase i) t
    by_cases hne : ((Finset.range (N + i)).erase i).Nonempty
    · have := hj0 hne
      exact lt_of_le_of_lt hle (hlt j0 (Finset.ne_of_mem_erase this))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, norm_zero]; exact hti
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hrest)
  rw [hsum, norm_zero, max_eq_left hrest.le] at this
  exact hti.ne' this.symm

/-- The dominant-term principle for an irreducible factor. Let `f ∈ ℚ[X]` with `b_0 ≠ 0`, and
let `g` be a monic irreducible factor of `f` over `ℚ_p` of degree `d`, with `k = v(g(0))`.
Then `g(0) ≠ 0`, and no index `i` with `b_i ≠ 0` is the unique minimizer of
`d·v(b_j) + j·k`. -/
theorem exists_ne_le_of_irreducible_factor {f : ℚ[X]} (h0 : f.coeff 0 ≠ 0) {g : ℚ_[p][X]}
    (hg : g.Monic) (hirr : Irreducible g) (hdvd : g ∣ f.map (algebraMap ℚ ℚ_[p])) :
    g.coeff 0 ≠ 0 ∧ ∀ i, f.coeff i ≠ 0 → ∃ j, j ≠ i ∧ f.coeff j ≠ 0 ∧
      (g.natDegree : ℤ) * padicValRat p (f.coeff j) + j * (g.coeff 0).valuation ≤
        g.natDegree * padicValRat p (f.coeff i) + i * (g.coeff 0).valuation := by
  have hdeg : g.degree ≠ 0 := by
    have := hirr.natDegree_pos
    rw [degree_eq_natDegree hirr.ne_zero]; exact_mod_cast this.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero (PadicAlgCl p) g hdeg
  have hzf : aeval z (f.map (algebraMap ℚ ℚ_[p])) = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hz
  have hnorm := norm_pow_natDegree_eq_norm_coeff_zero hg hirr hz
  have hg0 : g.coeff 0 ≠ 0 := by
    intro hg0
    rw [hg0, map_zero, norm_zero] at hnorm
    have hz0 : z = 0 := by
      have h1 : ‖z‖ = 0 := (pow_eq_zero_iff hirr.natDegree_pos.ne').mp hnorm
      exact norm_eq_zero.mp h1
    rw [hz0, ← coeff_zero_eq_aeval_zero', coeff_map] at hzf
    apply h0
    have : ((f.coeff 0 : ℚ) : ℚ_[p]) = 0 := by
      have := (algebraMap ℚ_[p] (PadicAlgCl p)).injective (hzf.trans (map_zero _).symm)
      exact this
    exact_mod_cast this
  refine ⟨hg0, fun i hi => exists_ne_le_of_aeval_eq_zero hzf hirr.natDegree_pos ?_ i hi⟩
  rw [hnorm, PadicAlgCl.norm_extends, Padic.norm_eq_zpow_neg_valuation hg0]

/-- A monic polynomial of positive degree over a field all of whose monic irreducible factors
have degree at least its own degree is irreducible. -/
theorem irreducible_of_forall_monic_irreducible_factor {K : Type*} [Field K] {F : K[X]}
    (hF : F.Monic) (hn : 0 < F.natDegree)
    (h : ∀ g : K[X], g.Monic → Irreducible g → g ∣ F → F.natDegree ≤ g.natDegree) :
    Irreducible F := by
  rw [hF.irreducible_iff_natDegree]
  refine ⟨fun h1 => by simp [h1] at hn, fun a b ha hb hab => ?_⟩
  by_contra hcon
  push Not at hcon
  have key : ∀ c : K[X], c.Monic → c ∣ F → c.natDegree ≠ 0 → F.natDegree ≤ c.natDegree := by
    intro c hc hcF hc0
    have hu : ¬ IsUnit c := fun hu => hc0 (natDegree_eq_zero_of_isUnit hu)
    obtain ⟨q, hq, hqirr, hqc⟩ := Polynomial.exists_monic_irreducible_factor c hu
    exact (h q hq hqirr (hqc.trans hcF)).trans (natDegree_le_of_dvd hqc hc.ne_zero)
  have h1 := key a ha ⟨b, hab.symm⟩ hcon.1
  have h2 := key b hb ⟨a, by rw [← hab, mul_comm]⟩ hcon.2
  have := ha.natDegree_mul hb
  rw [hab] at this
  omega

/-- **The single-edge criterion.** Let `f = ∑ b_j X^j ∈ ℚ[X]` be monic of degree `n ≥ 1`,
with `b_0 ≠ 0`, `H = v_p(b_0)` and `gcd(H, n) = 1`, and suppose `n·v_p(b_j) > H(n - j)` for
every `0 < j < n` with `b_j ≠ 0` (every intermediate coefficient point lies strictly above
the segment from `(0, H)` to `(n, 0)`). Then `f` is irreducible over `ℚ_p`. -/
theorem irreducible_map_padic_of_single_edge {f : ℚ[X]} (hf : f.Monic) (hn : 0 < f.natDegree)
    (h0 : f.coeff 0 ≠ 0) (hcop : Int.gcd (padicValRat p (f.coeff 0)) f.natDegree = 1)
    (hedge : ∀ j, 0 < j → j < f.natDegree → f.coeff j ≠ 0 →
      padicValRat p (f.coeff 0) * (f.natDegree - j : ℤ) <
        f.natDegree * padicValRat p (f.coeff j)) :
    Irreducible (f.map (algebraMap ℚ ℚ_[p])) := by
  set n := f.natDegree with hn_def
  set H := padicValRat p (f.coeff 0) with hH
  have hFm : (f.map (algebraMap ℚ ℚ_[p])).Monic := hf.map _
  have hFn : (f.map (algebraMap ℚ ℚ_[p])).natDegree = n := natDegree_map _
  have hbn : f.coeff n = 1 := hf.coeff_natDegree
  have hvn : padicValRat p (f.coeff n) = 0 := by rw [hbn]; simp
  refine irreducible_of_forall_monic_irreducible_factor hFm (by omega) fun g hg hirr hdvd => ?_
  rw [hFn]
  obtain ⟨hg0, hmin⟩ := exists_ne_le_of_irreducible_factor h0 hg hirr hdvd
  set d := g.natDegree with hd_def
  set k := (g.coeff 0).valuation with hk
  have hdpos : 0 < d := hirr.natDegree_pos
  have hd0 : (0 : ℤ) < d := by exact_mod_cast hdpos
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  -- the root valuation is `H / n`
  have hkn : k * n = H * d := by
    rcases lt_trichotomy (k * n) (H * d) with hlt | heq | hgt
    · exfalso
      obtain ⟨j, hjn, hj0, hle⟩ := hmin n (by rw [hbn]; exact one_ne_zero)
      rw [hvn] at hle
      have hjle : j ≤ n := by
        by_contra hj; exact hj0 (coeff_eq_zero_of_natDegree_lt (by omega))
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp only [Nat.cast_zero, zero_mul, add_zero, mul_zero, zero_add] at hle
        rw [← hH] at hle
        nlinarith
      · have hjlt : j < n := lt_of_le_of_ne hjle hjn
        have he := hedge j hjpos hjlt hj0
        have hjn' : (0 : ℤ) < n - j := by
          have : (j : ℤ) < n := by exact_mod_cast hjlt
          linarith
        have h1 : (d : ℤ) * (H * (n - j)) < d * (n * padicValRat p (f.coeff j)) :=
          mul_lt_mul_of_pos_left he hd0
        have h2 : (n - j : ℤ) * (k * n) < (n - j) * (H * d) := mul_lt_mul_of_pos_left hlt hjn'
        nlinarith
    · exact heq
    · exfalso
      obtain ⟨j, hj0n, hj0, hle⟩ := hmin 0 h0
      simp only [Nat.cast_zero, zero_mul, add_zero] at hle
      rw [← hH] at hle
      have hjle : j ≤ n := by
        by_contra hj; exact hj0 (coeff_eq_zero_of_natDegree_lt (by omega))
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0n
      have hj' : (0 : ℤ) < j := by exact_mod_cast hjpos
      rcases hjle.eq_or_lt with rfl | hjlt
      · rw [hvn] at hle; nlinarith
      · have he := hedge j hjpos hjlt hj0
        have h1 : (d : ℤ) * (H * (n - j)) < d * (n * padicValRat p (f.coeff j)) :=
          mul_lt_mul_of_pos_left he hd0
        have h2 : (j : ℤ) * (H * d) < j * (k * n) := mul_lt_mul_of_pos_left hgt hj'
        nlinarith
  have hdvd' : (n : ℤ) ∣ H * d := ⟨k, by rw [← hkn]; ring⟩
  have hgcd : Int.gcd (n : ℤ) H = 1 := by rw [Int.gcd_comm]; exact hcop
  have : (n : ℤ) ∣ d := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd' hgcd
  have : n ∣ d := by exact_mod_cast this
  exact Nat.le_of_dvd hdpos this

end ArithmeticOfJacobiPolynomials
