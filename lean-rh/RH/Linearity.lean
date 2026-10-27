/-
Copyright (c) 2026 Richard Andrew Rodriguez.
Released under the MIT license.
Manuscript DOI: 10.5281/zenodo.23692735
-/
import Mathlib
import RH.Axioms
import RH.Mappings
import RH.Kernel

open Complex Filter Topology

namespace TainoPolar


-- =========================================================================
-- Section 4: Linearity of the phase derivative over the zero sum
-- =========================================================================
-- Section 4.1: The linearity question
-- Section 4.2.1: Absolute convergence of the symmetric Hadamard product

-- =========================================================================
-- Native P-Space Hadamard Orbit & Absolute Convergence (Equations 155 - 156)
-- =========================================================================

section HadamardProductPSpace
variable (β γ σ t : ℝ)


-- Define the native coordinate mappings as variables so they are in scope
variable (s_state : ℝ → ℝ → PSpace)
variable (rho_state : ℝ → ℝ → PSpace)

/-- The unit state 1 in P-space: magnitude 1, phase 0. -/
noncomputable def one_state : PSpace := ⟦⟨1, by norm_num⟩, 0⟧

/-- The unit state 2 in P-space, required for native quadratic division. -/
noncomputable def two_state : PSpace := ⟦⟨2, by norm_num⟩, 0⟧


/--
Bridge Lemma: Sine-wave interference natively equals phasor addition.
Proves that `add_rel p q r` (Axiom 1.8) is mathematically identical to `proj p + proj q = proj r`.
-/
lemma add_rel_iff_proj (p q r : PSpace) : add_rel p q r ↔ proj p + proj q = proj r := by
  dsimp [add_rel]
  constructor
  · intro h
    apply Complex.ext
    · have h_pi2 := h (Real.pi / 2)
      have h_sin_pi2 (x : ℝ) : Real.sin (Real.pi / 2 + x) = Real.cos x := by
        rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
        ring
      rw [h_sin_pi2 (2 * Real.pi * p.phase), h_sin_pi2 (2 * Real.pi * q.phase), h_sin_pi2 (2 * Real.pi * r.phase)] at h_pi2
      have hre_p : (proj p).re = p.mag.val * Real.cos (2 * Real.pi * p.phase) := proj_re p
      have hre_q : (proj q).re = q.mag.val * Real.cos (2 * Real.pi * q.phase) := proj_re q
      have hre_r : (proj r).re = r.mag.val * Real.cos (2 * Real.pi * r.phase) := proj_re r
      rw [Complex.add_re, hre_p, hre_q, hre_r]
      exact h_pi2
    · have h_0 := h 0
      have h_sin_0 (x : ℝ) : Real.sin (0 + x) = Real.sin x := by rw [zero_add]
      rw [h_sin_0 (2 * Real.pi * p.phase), h_sin_0 (2 * Real.pi * q.phase), h_sin_0 (2 * Real.pi * r.phase)] at h_0
      have him_p : (proj p).im = p.mag.val * Real.sin (2 * Real.pi * p.phase) := proj_im p
      have him_q : (proj q).im = q.mag.val * Real.sin (2 * Real.pi * q.phase) := proj_im q
      have him_r : (proj r).im = r.mag.val * Real.sin (2 * Real.pi * r.phase) := proj_im r
      rw [Complex.add_im, him_p, him_q, him_r]
      exact h_0
  · intro h k
    have hre_p : (proj p).re = p.mag.val * Real.cos (2 * Real.pi * p.phase) := proj_re p
    have hre_q : (proj q).re = q.mag.val * Real.cos (2 * Real.pi * q.phase) := proj_re q
    have hre_r : (proj r).re = r.mag.val * Real.cos (2 * Real.pi * r.phase) := proj_re r
    have him_p : (proj p).im = p.mag.val * Real.sin (2 * Real.pi * p.phase) := proj_im p
    have him_q : (proj q).im = q.mag.val * Real.sin (2 * Real.pi * q.phase) := proj_im q
    have him_r : (proj r).im = r.mag.val * Real.sin (2 * Real.pi * r.phase) := proj_im r
    have h_re : p.mag.val * Real.cos (2 * Real.pi * p.phase) + q.mag.val * Real.cos (2 * Real.pi * q.phase) = r.mag.val * Real.cos (2 * Real.pi * r.phase) := by
      calc p.mag.val * Real.cos (2 * Real.pi * p.phase) + q.mag.val * Real.cos (2 * Real.pi * q.phase)
        _ = (proj p).re + (proj q).re := by rw [hre_p, hre_q]
        _ = (proj p + proj q).re := rfl
        _ = (proj r).re := by rw [h]
        _ = r.mag.val * Real.cos (2 * Real.pi * r.phase) := hre_r
    have h_im : p.mag.val * Real.sin (2 * Real.pi * p.phase) + q.mag.val * Real.sin (2 * Real.pi * q.phase) = r.mag.val * Real.sin (2 * Real.pi * r.phase) := by
      calc p.mag.val * Real.sin (2 * Real.pi * p.phase) + q.mag.val * Real.sin (2 * Real.pi * q.phase)
        _ = (proj p).im + (proj q).im := by rw [him_p, him_q]
        _ = (proj p + proj q).im := rfl
        _ = (proj r).im := by rw [h]
        _ = r.mag.val * Real.sin (2 * Real.pi * r.phase) := him_r
    have h_sin_add (A x : ℝ) : A * Real.sin (k + x) = Real.sin k * (A * Real.cos x) + Real.cos k * (A * Real.sin x) := by
      rw [Real.sin_add]; ring
    calc p.mag.val * Real.sin (k + 2 * Real.pi * p.phase) + q.mag.val * Real.sin (k + 2 * Real.pi * q.phase)
      _ = Real.sin k * (p.mag.val * Real.cos (2 * Real.pi * p.phase) + q.mag.val * Real.cos (2 * Real.pi * q.phase)) +
          Real.cos k * (p.mag.val * Real.sin (2 * Real.pi * p.phase) + q.mag.val * Real.sin (2 * Real.pi * q.phase)) := by
        rw [h_sin_add, h_sin_add]; ring
      _ = Real.sin k * (r.mag.val * Real.cos (2 * Real.pi * r.phase)) + Real.cos k * (r.mag.val * Real.sin (2 * Real.pi * r.phase)) := by
        rw [h_re, h_im]
      _ = r.mag.val * Real.sin (k + 2 * Real.pi * r.phase) := by
        rw [h_sin_add]

/-- Equation 152: The native P-space combined Hadamard product factor for the symmetric orbit. -/
noncomputable def eq_152_P_rho_orbit
    (h1 : 0 < M_rho_real β γ σ t)
    (h2 : 0 < M_rho_real (1 - β) γ σ t)
    (h3 : 0 < M_rho_real β (-γ) σ t)
    (h4 : 0 < M_rho_real (1 - β) (-γ) σ t) : PSpace :=
  mul_state (Z_rho_state_interior β γ σ t h1)
    (mul_state (Z_rho_state_interior (1 - β) γ σ t h2)
      (mul_state (Z_rho_state_interior β (-γ) σ t h3)
        (Z_rho_state_interior (1 - β) (-γ) σ t h4)))


/--
Equation 156a: The exact quadratic approximation of the full symmetric orbit in P-space.
Calculates $1 - \frac{1}{2}(w_1^2 + w_2^2 + w_3^2 + w_4^2)$ strictly via native sine-wave interference
and native magnitude division. No classical complex numbers or non-zero tracking required.
-/
noncomputable def eq_156_P_rho_approx (β γ σ t : ℝ) : PSpace :=
  let w1 := div_state (s_state σ t) (rho_state β γ)
  let w2 := div_state (s_state σ t) (rho_state (1 - β) γ)
  let w3 := div_state (s_state σ t) (rho_state β (-γ))
  let w4 := div_state (s_state σ t) (rho_state (1 - β) (-γ))
  let sq1 := mul_state w1 w1
  let sq2 := mul_state w2 w2
  let sq3 := mul_state w3 w3
  let sq4 := mul_state w4 w4
  let sum_sq := add_state sq1 (add_state sq2 (add_state sq3 sq4))
  sub_state one_state (div_state sum_sq two_state)

/--
Equation 156b: The exact remainder for the symmetric orbit product in P-space.
Defined strictly as `Orbit - Approximation` via `sub_state`.
-/
noncomputable def eq_156_P_rho_rem
    (h1 : 0 < M_rho_real β γ σ t)
    (h2 : 0 < M_rho_real (1 - β) γ σ t)
    (h3 : 0 < M_rho_real β (-γ) σ t)
    (h4 : 0 < M_rho_real (1 - β) (-γ) σ t) : PSpace :=
  sub_state (eq_152_P_rho_orbit β γ σ t h1 h2 h3 h4)
            (eq_156_P_rho_approx s_state rho_state β γ σ t)

/--
Equation 156c: Taylor expansion of the symmetric orbit product in P-space.
Expressed strictly via the native `add_rel` interference wave relation.
-/
lemma eq_156_taylor_expansion
    (h1 : 0 < M_rho_real β γ σ t)
    (h2 : 0 < M_rho_real (1 - β) γ σ t)
    (h3 : 0 < M_rho_real β (-γ) σ t)
    (h4 : 0 < M_rho_real (1 - β) (-γ) σ t) :
    add_rel (eq_156_P_rho_approx s_state rho_state β γ σ t)
            (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4)
            (eq_152_P_rho_orbit β γ σ t h1 h2 h3 h4) := by
  rw [add_rel_iff_proj]
  dsimp [eq_156_P_rho_rem]
  rw [proj_sub_state _ _]
  ring

end HadamardProductPSpace



-- =========================================================================
-- Real Arithmetic Deviations (Equations 157 - 158)
-- =========================================================================

section RealFractions
variable (β γ : ℝ)

/-- Equation 157: Algebraic expansion of the sum of reciprocals of squared conjugate roots.
This purely real reduction isolates the γ^-2 scaling natively. -/
lemma eq_157_inv_sq_add_conj_sq :
    ((rho β γ)⁻¹)^2 + ((rho β (-γ))⁻¹)^2 =
    Complex.mk (2 * (β^2 - γ^2) / (β^2 + γ^2)^2) 0 := by
  dsimp [rho]
  have h1 : ((Complex.mk β γ)⁻¹)^2 = ((Complex.mk β γ)⁻¹) * ((Complex.mk β γ)⁻¹) := pow_two _
  have h2 : ((Complex.mk β (-γ))⁻¹)^2 = ((Complex.mk β (-γ))⁻¹) * ((Complex.mk β (-γ))⁻¹) := pow_two _
  rw [h1, h2]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq_mk]
    have h_rhs : 2 * (β^2 - γ^2) / (β^2 + γ^2)^2 = 2 * (β^2 - γ^2) * ((β^2 + γ^2)⁻¹)^2 := by
      change 2 * (β^2 - γ^2) * ((β^2 + γ^2)^2)⁻¹ = _
      rw [pow_two (β^2 + γ^2)]
      have h_inv : ((β^2 + γ^2) * (β^2 + γ^2))⁻¹ = (β^2 + γ^2)⁻¹ * (β^2 + γ^2)⁻¹ := mul_inv (β^2 + γ^2) (β^2 + γ^2)
      rw [h_inv, ← pow_two ((β^2 + γ^2)⁻¹)]
    rw [h_rhs]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq_mk]
    ring

/-- Equation 158: Full symmetric quadruplet reciprocal square sum. -/
lemma eq_158_inv_sq_quad_sum :
    ((rho β γ)⁻¹)^2 + ((rho β (-γ))⁻¹)^2 +
    ((rho (1 - β) γ)⁻¹)^2 + ((rho (1 - β) (-γ))⁻¹)^2 =
    Complex.mk ((2 * (β^2 - γ^2) / (β^2 + γ^2)^2) + (2 * ((1 - β)^2 - γ^2) / ((1 - β)^2 + γ^2)^2)) 0 := by
  have h_group :
    ((rho β γ)⁻¹)^2 + ((rho β (-γ))⁻¹)^2 + ((rho (1 - β) γ)⁻¹)^2 + ((rho (1 - β) (-γ))⁻¹)^2 =
    (((rho β γ)⁻¹)^2 + ((rho β (-γ))⁻¹)^2) + (((rho (1 - β) γ)⁻¹)^2 + ((rho (1 - β) (-γ))⁻¹)^2) := by ring
  rw [h_group]
  rw [eq_157_inv_sq_add_conj_sq β γ]
  rw [eq_157_inv_sq_add_conj_sq (1 - β) γ]
  apply Complex.ext
  · simp only [Complex.add_re]
  · simp only [Complex.add_im, add_zero]

end RealFractions







/-- Helper: Maps P-space magnitude identically to the complex norm of its projection. -/
lemma mag_eq_norm_proj (p : PSpace) : p.mag.val = ‖proj p‖ := by
  have h1 : ‖proj p‖ = Real.sqrt (Complex.normSq (proj p)) := Complex.norm_def (proj p)
  have h2 : Complex.normSq (proj p) = (proj p).re^2 + (proj p).im^2 := by
    dsimp [Complex.normSq]
    ring
  rw [h1, h2, proj_re p, proj_im p]
  have h_trig : (p.mag.val * Real.cos (2 * Real.pi * p.phase))^2 + (p.mag.val * Real.sin (2 * Real.pi * p.phase))^2 = p.mag.val^2 := by
    calc (p.mag.val * Real.cos (2 * Real.pi * p.phase))^2 + (p.mag.val * Real.sin (2 * Real.pi * p.phase))^2
      _ = p.mag.val^2 * ((Real.cos (2 * Real.pi * p.phase))^2 + (Real.sin (2 * Real.pi * p.phase))^2) := by ring
      _ = p.mag.val^2 * 1 := by rw [Real.cos_sq_add_sin_sq (2 * Real.pi * p.phase)]
      _ = p.mag.val^2 := by ring
  rw [h_trig]
  exact (Real.sqrt_sq p.mag.property.le).symm

/-- Helper: Real arithmetic bounds for the sum of squared reciprocals. -/
lemma quad_inv_sq_sum_real_bound :
    ∃ C > 0, ∃ T > 0, ∀ β γ : ℝ, 0 ≤ β → β ≤ 1 → |γ| > T →
    |2 * (β^2 - γ^2) / (β^2 + γ^2)^2 + 2 * ((1 - β)^2 - γ^2) / ((1 - β)^2 + γ^2)^2| ≤ C / γ^2 := by
  use 8, (by norm_num), 1, (by norm_num)
  intro β γ hβ1 hβ2 hγ
  have hγ_pos : 0 < |γ| := by linarith
  have hγ2_gt_1 : 1 < γ^2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ < |γ| * |γ| := mul_lt_mul hγ (le_of_lt hγ) zero_lt_one (le_of_lt hγ_pos)
      _ = γ^2 := by rw [← sq_abs γ]; ring
  have hγ2_pos : 0 < γ^2 := by linarith
  have hβ2_nonneg : 0 ≤ β^2 := sq_nonneg β
  have h1β_nonneg : 0 ≤ (1 - β)^2 := sq_nonneg _
  have h_den1_base : 0 < β^2 + γ^2 := add_pos_of_nonneg_of_pos hβ2_nonneg hγ2_pos
  have h_den2_base : 0 < (1 - β)^2 + γ^2 := add_pos_of_nonneg_of_pos h1β_nonneg hγ2_pos
  have h_den1_pos : 0 < (β^2 + γ^2)^2 := pow_pos h_den1_base 2
  have h_den2_pos : 0 < ((1 - β)^2 + γ^2)^2 := pow_pos h_den2_base 2

  have h_frac1 : |2 * (β^2 - γ^2) / (β^2 + γ^2)^2| ≤ 4 / γ^2 := by
    rw [abs_div, abs_of_pos h_den1_pos]
    have h_abs_sub : |β^2 - γ^2| ≤ |β^2| + |-γ^2| := by rw [sub_eq_add_neg]; exact abs_add_le _ _
    have h_abs_beta : |β^2| = β^2 := abs_of_nonneg hβ2_nonneg
    have h_abs_gamma : |-γ^2| = γ^2 := by rw [abs_neg, abs_of_nonneg (sq_nonneg γ)]
    have h_num_le : |2 * (β^2 - γ^2)| ≤ 4 * (β^2 + γ^2) := by
      calc |2 * (β^2 - γ^2)| = 2 * |β^2 - γ^2| := by rw [abs_mul, abs_of_pos (by norm_num)]
        _ ≤ 2 * (|β^2| + |-γ^2|) := mul_le_mul_of_nonneg_left h_abs_sub (by norm_num)
        _ = 2 * (β^2 + γ^2) := by rw [h_abs_beta, h_abs_gamma]
        _ ≤ 4 * (β^2 + γ^2) := by linarith
    have h_div1 : |2 * (β^2 - γ^2)| / (β^2 + γ^2)^2 ≤ 4 * (β^2 + γ^2) / (β^2 + γ^2)^2 := div_le_div_of_nonneg_right h_num_le (le_of_lt h_den1_pos)
    have h_div2 : 4 * (β^2 + γ^2) / (β^2 + γ^2)^2 = 4 / (β^2 + γ^2) := by
      let d : ℝ := β^2 + γ^2
      have hd : d ≠ 0 := ne_of_gt h_den1_base
      change 4 * d / d^2 = 4 / d
      simpa only [pow_two] using (mul_div_mul_right 4 d hd)
    have h_div3 : 4 / (β^2 + γ^2) ≤ 4 / γ^2 := by
      have h_le : γ^2 ≤ β^2 + γ^2 := by linarith
      have h_inv : 1 / (β^2 + γ^2) ≤ 1 / γ^2 := (one_div_le_one_div h_den1_base hγ2_pos).mpr h_le
      calc 4 / (β^2 + γ^2) = 4 * (1 / (β^2 + γ^2)) := by ring
        _ ≤ 4 * (1 / γ^2) := mul_le_mul_of_nonneg_left h_inv (by norm_num)
        _ = 4 / γ^2 := by ring
    calc |2 * (β^2 - γ^2)| / (β^2 + γ^2)^2 ≤ 4 * (β^2 + γ^2) / (β^2 + γ^2)^2 := h_div1
      _ = 4 / (β^2 + γ^2) := h_div2
      _ ≤ 4 / γ^2 := h_div3

  have h_frac2 : |2 * ((1 - β)^2 - γ^2) / ((1 - β)^2 + γ^2)^2| ≤ 4 / γ^2 := by
    rw [abs_div, abs_of_pos h_den2_pos]
    have h_abs_sub : |(1 - β)^2 - γ^2| ≤ |(1 - β)^2| + |-γ^2| := by rw [sub_eq_add_neg]; exact abs_add_le _ _
    have h_abs_beta : |(1 - β)^2| = (1 - β)^2 := abs_of_nonneg h1β_nonneg
    have h_abs_gamma : |-γ^2| = γ^2 := by rw [abs_neg, abs_of_nonneg (sq_nonneg γ)]
    have h_num_le : |2 * ((1 - β)^2 - γ^2)| ≤ 4 * ((1 - β)^2 + γ^2) := by
      calc |2 * ((1 - β)^2 - γ^2)| = 2 * |(1 - β)^2 - γ^2| := by rw [abs_mul, abs_of_pos (by norm_num)]
        _ ≤ 2 * (|(1 - β)^2| + |-γ^2|) := mul_le_mul_of_nonneg_left h_abs_sub (by norm_num)
        _ = 2 * ((1 - β)^2 + γ^2) := by rw [h_abs_beta, h_abs_gamma]
        _ ≤ 4 * ((1 - β)^2 + γ^2) := by linarith
    have h_div1 : |2 * ((1 - β)^2 - γ^2)| / ((1 - β)^2 + γ^2)^2 ≤ 4 * ((1 - β)^2 + γ^2) / ((1 - β)^2 + γ^2)^2 := div_le_div_of_nonneg_right h_num_le (le_of_lt h_den2_pos)
    have h_div2 : 4 * ((1 - β)^2 + γ^2) / ((1 - β)^2 + γ^2)^2 = 4 / ((1 - β)^2 + γ^2) := by
      let d : ℝ := (1 - β)^2 + γ^2
      have hd : d ≠ 0 := ne_of_gt h_den2_base
      change 4 * d / d^2 = 4 / d
      simpa only [pow_two] using (mul_div_mul_right 4 d hd)
    have h_div3 : 4 / ((1 - β)^2 + γ^2) ≤ 4 / γ^2 := by
      have h_le : γ^2 ≤ (1 - β)^2 + γ^2 := by linarith
      have h_inv : 1 / ((1 - β)^2 + γ^2) ≤ 1 / γ^2 := (one_div_le_one_div h_den2_base hγ2_pos).mpr h_le
      calc 4 / ((1 - β)^2 + γ^2) = 4 * (1 / ((1 - β)^2 + γ^2)) := by ring
        _ ≤ 4 * (1 / γ^2) := mul_le_mul_of_nonneg_left h_inv (by norm_num)
        _ = 4 / γ^2 := by ring
    calc |2 * ((1 - β)^2 - γ^2)| / ((1 - β)^2 + γ^2)^2 ≤ 4 * ((1 - β)^2 + γ^2) / ((1 - β)^2 + γ^2)^2 := h_div1
      _ = 4 / ((1 - β)^2 + γ^2) := h_div2
      _ ≤ 4 / γ^2 := h_div3

  calc |2 * (β^2 - γ^2) / (β^2 + γ^2)^2 + 2 * ((1 - β)^2 - γ^2) / ((1 - β)^2 + γ^2)^2|
    _ ≤ |2 * (β^2 - γ^2) / (β^2 + γ^2)^2| + |2 * ((1 - β)^2 - γ^2) / ((1 - β)^2 + γ^2)^2| := abs_add_le _ _
    _ ≤ 4 / γ^2 + 4 / γ^2 := add_le_add h_frac1 h_frac2
    _ = 8 / γ^2 := by ring



-- =========================================================================
-- Equation 159: Asymptotic Bounds (Native P-Space)
-- =========================================================================

/--
Native P-space triangle inequality for additive deviations.
If `Orbit = Approx + Rem` natively, then the magnitude of the deviation from `one_state` satisfies vector addition.
-/
lemma pspace_triangle_ineq_dev (approx rem orbit : PSpace) (h_add : add_rel approx rem orbit) :
    (sub_state orbit one_state).mag.val ≤ (sub_state approx one_state).mag.val + rem.mag.val := by
  rw [mag_eq_norm_proj, mag_eq_norm_proj, mag_eq_norm_proj]
  have h_one : proj one_state = 1 := by
    dsimp [one_state, proj]
    have h_zero : 2 * Real.pi * Complex.I * (0 : ℂ) = 0 := by ring
    rw [h_zero, Complex.exp_zero, mul_one]
  rw [proj_sub_state _ _, proj_sub_state _ _, h_one]
  have h_proj_add := (add_rel_iff_proj approx rem orbit).mp h_add
  have h_sub_eq : proj orbit - 1 = (proj approx - 1) + proj rem := by
    rw [← h_proj_add]
    ring
  rw [h_sub_eq]
  exact norm_add_le (proj approx - 1) (proj rem)


/-- The exact quadratic approximation deviation from 1 strictly in P-space projection. -/
lemma eq_156_approx_dev_bound (s_state rho_state : ℝ → ℝ → PSpace)
    (h_rho : ∀ b g, proj (rho_state b g) = rho b g)
    (h_approx_eval : ∀ β γ σ t, proj (eq_156_P_rho_approx s_state rho_state β γ σ t) =
      1 - ((proj (s_state σ t))^2 / 2) * (((proj (rho_state β γ))⁻¹)^2 + ((proj (rho_state β (-γ)))⁻¹)^2 + ((proj (rho_state (1 - β) γ))⁻¹)^2 + ((proj (rho_state (1 - β) (-γ)))⁻¹)^2)) :
    ∃ C > 0, ∃ T > 0, ∀ β γ σ t : ℝ, 0 ≤ β → β ≤ 1 → |γ| > T →
    ‖proj (eq_156_P_rho_approx s_state rho_state β γ σ t) - 1‖ ≤ C * ‖proj (s_state σ t)‖^2 / γ^2 := by
  rcases quad_inv_sq_sum_real_bound with ⟨C_q, hCq_pos, T_q, hTq_pos, h_q_bound⟩
  refine ⟨C_q / 2, by positivity, T_q, hTq_pos, ?_⟩
  intro β γ σ t hβ0 hβ1 hγ

  rw [h_approx_eval]
  have h_alg_simp : 1 - ((proj (s_state σ t)) ^ 2 / 2) * (((proj (rho_state β γ))⁻¹) ^ 2 + ((proj (rho_state β (-γ)))⁻¹) ^ 2 + ((proj (rho_state (1 - β) γ))⁻¹) ^ 2 + ((proj (rho_state (1 - β) (-γ)))⁻¹) ^ 2) - 1 =
    -(((proj (s_state σ t)) ^ 2 / 2) * (((proj (rho_state β γ))⁻¹) ^ 2 + ((proj (rho_state β (-γ)))⁻¹) ^ 2 + ((proj (rho_state (1 - β) γ))⁻¹) ^ 2 + ((proj (rho_state (1 - β) (-γ)))⁻¹) ^ 2)) := by ring

  rw [h_alg_simp, norm_neg, norm_mul, norm_div]

  have h_two : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h_two, norm_pow]

  have h_rho_apply : ((proj (rho_state β γ))⁻¹)^2 + ((proj (rho_state β (-γ)))⁻¹)^2 + ((proj (rho_state (1 - β) γ))⁻¹)^2 + ((proj (rho_state (1 - β) (-γ)))⁻¹)^2 =
    Complex.mk ((2 * (β^2 - γ^2) / (β^2 + γ^2)^2) + (2 * ((1 - β)^2 - γ^2) / ((1 - β)^2 + γ^2)^2)) 0 := by
    rw [h_rho, h_rho, h_rho, h_rho]
    exact eq_158_inv_sq_quad_sum β γ
  rw [h_rho_apply]

  have h_mk_norm (x : ℝ) : ‖Complex.mk x 0‖ = |x| := by
    have h_sq : Complex.normSq (Complex.mk x 0) = x^2 := by
      dsimp [Complex.normSq]
      ring
    rw [Complex.norm_def, h_sq]
    exact Real.sqrt_sq_eq_abs x
  rw [h_mk_norm]

  have h_bound := h_q_bound β γ hβ0 hβ1 hγ
  calc ‖proj (s_state σ t)‖^2 / 2 * |2 * (β^2 - γ^2) / (β^2 + γ^2)^2 + 2 * ((1 - β)^2 - γ^2) / ((1 - β)^2 + γ^2)^2|
    _ ≤ ‖proj (s_state σ t)‖^2 / 2 * (C_q / γ^2) := mul_le_mul_of_nonneg_left h_bound (by positivity)
    _ = (C_q / 2) * ‖proj (s_state σ t)‖^2 / γ^2 := by ring

-- =========================================================================
-- Equation 159: Asymptotic Bounds (Native P-Space)
-- =========================================================================

/--
Equation 159: The final asymptotic upper bound evaluated ENTIRELY natively in P-space.
Proves the magnitude of `Orbit - 1` natively satisfies the inverse-square decay geometry
by applying the P-space triangle inequality to the exact P-space Taylor expansion.
-/
lemma eq_159_P_rho_orbit_bound (s_state rho_state : ℝ → ℝ → PSpace)
    (h_rho : ∀ b g, proj (rho_state b g) = rho b g)
    (h_approx_eval : ∀ β γ σ t, proj (eq_156_P_rho_approx s_state rho_state β γ σ t) =
      1 - ((proj (s_state σ t))^2 / 2) * (((proj (rho_state β γ))⁻¹)^2 + ((proj (rho_state β (-γ)))⁻¹)^2 + ((proj (rho_state (1 - β) γ))⁻¹)^2 + ((proj (rho_state (1 - β) (-γ)))⁻¹)^2))
    (h_rem_bound : ∀ R > 0, ∃ C > 0, ∃ T > 1, ∀ β γ σ t : ℝ, ‖proj (s_state σ t)‖ ≤ R → 0 ≤ β → β ≤ 1 → |γ| > T →
      ∀ (h1 : 0 < M_rho_real β γ σ t) (h2 : 0 < M_rho_real (1 - β) γ σ t)
        (h3 : 0 < M_rho_real β (-γ) σ t) (h4 : 0 < M_rho_real (1 - β) (-γ) σ t),
      ‖proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4)‖ ≤ C * ‖proj (s_state σ t)‖^3 / |γ|^3)
    (R : ℝ) (hR_pos : R > 0) :
    ∃ C > 0, ∃ T > 0, ∀ β γ σ t : ℝ, ‖proj (s_state σ t)‖ ≤ R → 0 ≤ β → β ≤ 1 → |γ| > T →
    ∀ (h1 : 0 < M_rho_real β γ σ t) (h2 : 0 < M_rho_real (1 - β) γ σ t)
      (h3 : 0 < M_rho_real β (-γ) σ t) (h4 : 0 < M_rho_real (1 - β) (-γ) σ t),
    ‖proj (eq_152_P_rho_orbit β γ σ t h1 h2 h3 h4) - 1‖ ≤ C * ‖proj (s_state σ t)‖^2 / γ^2 := by

  have h_approx := eq_156_approx_dev_bound s_state rho_state h_rho h_approx_eval
  have h_rem := h_rem_bound R hR_pos
  rcases h_approx with ⟨C_a, hCa_pos, T_a, _hTa_pos, h_a_bound⟩
  rcases h_rem with ⟨C_r, hCr_pos, T_r, hTr_gt_1, h_r_bound⟩

  let T_max := max (max T_a T_r) 1
  have hT_max_pos : T_max > 0 := by
    calc 0 < 1 := zero_lt_one
         _ ≤ max (max T_a T_r) 1 := le_max_right _ _

  let C_max := C_a + C_r * R
  have hC_max_pos : 0 < C_a + C_r * R :=
    add_pos_of_pos_of_nonneg hCa_pos (mul_nonneg hCr_pos.le (le_of_lt hR_pos))

  use C_max, hC_max_pos, T_max, hT_max_pos
  intro β γ σ t hs_R hβ1 hβ2 hγ h1 h2 h3 h4

  have h_gamma_a : |γ| > T_a := by
    calc T_a ≤ max T_a T_r := le_max_left _ _
         _   ≤ T_max := le_max_left _ _
         _   < |γ| := hγ
  have h_gamma_r : |γ| > T_r := by
    calc T_r ≤ max T_a T_r := le_max_right _ _
         _   ≤ T_max := le_max_left _ _
         _   < |γ| := hγ
  have h_gamma_1 : |γ| > 1 := by
    calc 1 ≤ T_max := le_max_right _ _
         _ < |γ| := hγ

  have h_a := h_a_bound β γ σ t hβ1 hβ2 h_gamma_a
  have h_r := h_r_bound β γ σ t hs_R hβ1 hβ2 h_gamma_r h1 h2 h3 h4

  have h_abs_cube : |γ|^3 = |γ| * γ^2 := by
    calc |γ|^3 = |γ| * |γ|^2 := by ring
         _ = |γ| * γ^2 := by rw [sq_abs]
  have h_s_cube : ‖proj (s_state σ t)‖^3 = ‖proj (s_state σ t)‖ * ‖proj (s_state σ t)‖^2 := by ring

  have h_rem_le : C_r * ‖proj (s_state σ t)‖^3 / |γ|^3 ≤ (C_r * R) * ‖proj (s_state σ t)‖^2 / γ^2 := by
    rw [h_abs_cube, h_s_cube]
    have h_split1 : C_r * (‖proj (s_state σ t)‖ * ‖proj (s_state σ t)‖^2) / (|γ| * γ^2) = (C_r * ‖proj (s_state σ t)‖ / |γ|) * (‖proj (s_state σ t)‖^2 / γ^2) := by ring
    have h_split2 : (C_r * R) * ‖proj (s_state σ t)‖^2 / γ^2 = (C_r * R / 1) * (‖proj (s_state σ t)‖^2 / γ^2) := by ring
    rw [h_split1, h_split2]
    apply mul_le_mul_of_nonneg_right
    · have h_gamma_pos : 0 < |γ| := by linarith
      have h_gamma_ge_1 : 1 ≤ |γ| := le_of_lt h_gamma_1
      have h_num : C_r * ‖proj (s_state σ t)‖ ≤ C_r * R := mul_le_mul_of_nonneg_left hs_R (le_of_lt hCr_pos)
      have h_div_1 : C_r * ‖proj (s_state σ t)‖ / |γ| ≤ C_r * R / |γ| := div_le_div_of_nonneg_right h_num (le_of_lt h_gamma_pos)
      have h_div_2 : C_r * R / |γ| ≤ C_r * R / 1 := by
        apply div_le_div_of_nonneg_left (mul_nonneg (le_of_lt hCr_pos) (le_of_lt hR_pos)) zero_lt_one h_gamma_ge_1
      exact le_trans h_div_1 h_div_2
    · positivity

  by_cases h_rem_nz : proj (eq_152_P_rho_orbit β γ σ t h1 h2 h3 h4) - proj (eq_156_P_rho_approx s_state rho_state β γ σ t) = 0
  · have h_orbit_eq_approx : proj (eq_152_P_rho_orbit β γ σ t h1 h2 h3 h4) = proj (eq_156_P_rho_approx s_state rho_state β γ σ t) := sub_eq_zero.mp h_rem_nz
    rw [h_orbit_eq_approx]
    calc ‖proj (eq_156_P_rho_approx s_state rho_state β γ σ t) - 1‖
      _ ≤ C_a * ‖proj (s_state σ t)‖^2 / γ^2 := h_a
      _ ≤ C_a * ‖proj (s_state σ t)‖^2 / γ^2 + (C_r * R) * ‖proj (s_state σ t)‖^2 / γ^2 := by
        apply le_add_of_nonneg_right
        positivity
      _ = (C_a + C_r * R) * ‖proj (s_state σ t)‖^2 / γ^2 := by ring

  · have h_taylor := eq_156_taylor_expansion β γ σ t s_state rho_state h1 h2 h3 h4
    have h_proj_add := (add_rel_iff_proj _ _ _).mp h_taylor

    have h_rem_proj : proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4) =
                      proj (eq_152_P_rho_orbit β γ σ t h1 h2 h3 h4) - proj (eq_156_P_rho_approx s_state rho_state β γ σ t) := by
      dsimp [eq_156_P_rho_rem]
      rw [proj_sub_state _ _]

    have h_sub : proj (eq_152_P_rho_orbit β γ σ t h1 h2 h3 h4) - 1 =
                 (proj (eq_156_P_rho_approx s_state rho_state β γ σ t) - 1) +
                 proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4) := by
      calc proj (eq_152_P_rho_orbit β γ σ t h1 h2 h3 h4) - 1
        _ = (proj (eq_156_P_rho_approx s_state rho_state β γ σ t) + proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4)) - 1 := by rw [h_proj_add]
        _ = (proj (eq_156_P_rho_approx s_state rho_state β γ σ t) - 1) + proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4) := by ring

    rw [h_sub]
    have h_tri := norm_add_le (proj (eq_156_P_rho_approx s_state rho_state β γ σ t) - 1) (proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4))

    calc ‖(proj (eq_156_P_rho_approx s_state rho_state β γ σ t) - 1) + proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4)‖
      _ ≤ ‖proj (eq_156_P_rho_approx s_state rho_state β γ σ t) - 1‖ + ‖proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4)‖ := h_tri
      _ ≤ C_a * ‖proj (s_state σ t)‖^2 / γ^2 + C_r * ‖proj (s_state σ t)‖^3 / |γ|^3 := add_le_add h_a h_r
      _ ≤ C_a * ‖proj (s_state σ t)‖^2 / γ^2 + (C_r * R) * ‖proj (s_state σ t)‖^2 / γ^2 := add_le_add (le_refl _) h_rem_le
      _ = (C_a + C_r * R) * ‖proj (s_state σ t)‖^2 / γ^2 := by ring








-- =========================================================================
-- Equation 160: Riemann-von Mangoldt Density Bound via Dyadic Shells
-- =========================================================================

/-- The dyadic ordinate shell `[2^k, 2^(k+1))`. -/
def gamma_dyadic_shell (gamma : ℕ → ℝ) (k : ℕ) : Set ℕ :=
  {n : ℕ | (2 : ℝ) ^ k ≤ |gamma n| ∧ |gamma n| < (2 : ℝ) ^ (k + 1)}

/-- The finite low-height portion `|γ_n| < 2`. -/
def gamma_head (gamma : ℕ → ℝ) : Set ℕ :=
  {n : ℕ | |gamma n| < 2}

/-- Local finiteness required of an enumeration of zero ordinates. -/
def GammaLocallyFinite (gamma : ℕ → ℝ) : Prop :=
  ∀ T : ℝ, Set.Finite {n : ℕ | |gamma n| ≤ T}

/-- The coarse Riemann--von Mangoldt input needed for Equation 160. -/
def HasRVMCount (gamma : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ T : ℝ, 2 ≤ T → N_count gamma T ≤ C * T * Real.log T

/-- Each dyadic shell is finite under local finiteness. -/
lemma gamma_dyadic_shell_finite (gamma : ℕ → ℝ) (h_local : GammaLocallyFinite gamma) (k : ℕ) :
    (gamma_dyadic_shell gamma k).Finite := by
  apply Set.Finite.subset (h_local ((2 : ℝ) ^ (k + 1)))
  intro n hn
  exact le_of_lt hn.2

/-- The low-height head is finite under local finiteness. -/
lemma gamma_head_finite (gamma : ℕ → ℝ) (h_local : GammaLocallyFinite gamma) :
    (gamma_head gamma).Finite := by
  apply Set.Finite.subset (h_local 2)
  intro n hn
  change |gamma n| < 2 at hn
  exact le_of_lt hn

/-- A dyadic shell is contained in the counting set at its upper endpoint. -/
lemma gamma_dyadic_shell_subset_count (gamma : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    gamma_dyadic_shell gamma k ⊆ {n : ℕ | 1 ≤ |gamma n| ∧ |gamma n| ≤ (2 : ℝ) ^ (k + 1)} := by
  intro n hn
  change (2 : ℝ) ^ k ≤ |gamma n| ∧ |gamma n| < (2 : ℝ) ^ (k + 1) at hn
  constructor
  · have htwo_le : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
      have hpow : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
      simpa using hpow
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_trans htwo_le hn.1)
  · exact le_of_lt hn.2

/-- The cardinality of a dyadic shell is bounded by `N(2^(k+1))`. -/
lemma gamma_dyadic_shell_card_le_count (gamma : ℕ → ℝ) (h_local : GammaLocallyFinite gamma) (k : ℕ) (hk : 1 ≤ k) :
    ((gamma_dyadic_shell gamma k).ncard : ℝ) ≤ N_count gamma ((2 : ℝ) ^ (k + 1)) := by
  unfold N_count
  have h_target_finite : Set.Finite {n : ℕ | 1 ≤ |gamma n| ∧ |gamma n| ≤ (2 : ℝ) ^ (k + 1)} := by
    apply Set.Finite.subset (h_local ((2 : ℝ) ^ (k + 1)))
    intro n hn
    exact hn.2
  have h_card_nat : (gamma_dyadic_shell gamma k).ncard ≤ ({n : ℕ | 1 ≤ |gamma n| ∧ |gamma n| ≤ (2 : ℝ) ^ (k + 1)}).ncard :=
    Set.ncard_le_ncard (gamma_dyadic_shell_subset_count gamma k hk) h_target_finite
  exact Nat.cast_le.mpr h_card_nat

/-- Coarse dyadic consequence of `N(T) = O(T log T)`. -/
lemma rvm_dyadic_shell_count (gamma : ℕ → ℝ) (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    ∃ A > 0, ∀ k : ℕ, 1 ≤ k → ((gamma_dyadic_shell gamma k).ncard : ℝ) ≤ A * (k + 1 : ℝ) * (2 : ℝ) ^ k := by
  rcases h_rvm with ⟨C, hC_pos, hC⟩
  refine ⟨4 * C, by positivity, ?_⟩
  intro k hk

  have h_two_pow_ge_two : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    have hk1 : 1 ≤ k + 1 := by omega
    have hpow : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) hk1
    simpa using hpow

  have h_card : ((gamma_dyadic_shell gamma k).ncard : ℝ) ≤ C * ((2 : ℝ) ^ (k + 1)) * Real.log ((2 : ℝ) ^ (k + 1)) :=
    le_trans (gamma_dyadic_shell_card_le_count gamma h_local k hk) (hC ((2 : ℝ) ^ (k + 1)) h_two_pow_ge_two)

  have h_log_bound : ((2 : ℝ) ^ (k + 1)) * Real.log ((2 : ℝ) ^ (k + 1)) ≤ 4 * (k + 1 : ℝ) * (2 : ℝ) ^ k := by
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      calc Real.log (2 : ℝ) ≤ Real.log (Real.exp 1) := by
             apply (Real.log_le_log_iff (by norm_num) (Real.exp_pos 1)).mpr
             have htwo_lt_exp : (2 : ℝ) < Real.exp 1 := by
               have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
               norm_num at h ⊢
               simpa using h
             exact htwo_lt_exp.le
           _ = 1 := Real.log_exp 1
    have hlogpow : Real.log ((2 : ℝ) ^ (k + 1)) = (k + 1 : ℝ) * Real.log (2 : ℝ) := by
      have h_base : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1 : ℝ) := by norm_cast
      rw [h_base, Real.log_rpow zero_lt_two (k + 1 : ℝ)]
    have hcore : (2 : ℝ) ^ (k + 1) * ((k + 1 : ℝ) * Real.log (2 : ℝ)) ≤ (2 : ℝ) ^ (k + 1) * ((k + 1 : ℝ) * 1) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
      · positivity
    calc ((2 : ℝ) ^ (k + 1)) * Real.log ((2 : ℝ) ^ (k + 1))
      _ = (2 : ℝ) ^ (k + 1) * ((k + 1 : ℝ) * Real.log (2 : ℝ)) := by rw [hlogpow]
      _ ≤ (2 : ℝ) ^ (k + 1) * ((k + 1 : ℝ) * 1) := hcore
      _ = 2 * (k + 1 : ℝ) * (2 : ℝ) ^ k := by rw [pow_succ]; ring
      _ ≤ 4 * (k + 1 : ℝ) * (2 : ℝ) ^ k := by
        have hrest : 0 ≤ (k + 1 : ℝ) * (2 : ℝ) ^ k := by positivity
        linarith

  have h_mul : C * (((2 : ℝ) ^ (k + 1)) * Real.log ((2 : ℝ) ^ (k + 1))) ≤ C * (4 * (k + 1 : ℝ) * (2 : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left h_log_bound (le_of_lt hC_pos)

  calc ((gamma_dyadic_shell gamma k).ncard : ℝ)
    _ ≤ C * ((2 : ℝ) ^ (k + 1)) * Real.log ((2 : ℝ) ^ (k + 1)) := h_card
    _ = C * (((2 : ℝ) ^ (k + 1)) * Real.log ((2 : ℝ) ^ (k + 1))) := by ring
    _ ≤ C * (4 * (k + 1 : ℝ) * (2 : ℝ) ^ k) := h_mul
    _ = (4 * C) * (k + 1 : ℝ) * (2 : ℝ) ^ k := by ring

/-- Each reciprocal-square term in the `k`-th dyadic shell is at most `4^-k`. -/
lemma reciprocal_sq_le_dyadic (gamma : ℕ → ℝ) (k n : ℕ) (hn : n ∈ gamma_dyadic_shell gamma k) :
    1 / (gamma n) ^ 2 ≤ 1 / (4 : ℝ) ^ k := by
  have h_lower : (2 : ℝ) ^ k ≤ |gamma n| := hn.1
  have h_sq_lower : ((2 : ℝ) ^ k)^2 ≤ (gamma n)^2 := by
    have h1 : ((2 : ℝ) ^ k)^2 ≤ |gamma n|^2 := by
      apply sq_le_sq.mpr
      simpa [abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k)] using h_lower
    simpa [sq_abs] using h1
  have h_four : (4 : ℝ)^k = ((2 : ℝ)^k)^2 := by
    calc (4 : ℝ)^k = ((2 : ℝ)^2)^k := by norm_num
      _ = (2 : ℝ)^(2 * k) := by rw [pow_mul]
      _ = (2 : ℝ)^(k * 2) := by ring
      _ = ((2 : ℝ)^k)^2 := by rw [pow_mul]
  have h_left_pos : 0 < ((2 : ℝ)^k)^2 := pow_pos (pow_pos (by norm_num) k) 2
  rw [h_four]
  exact one_div_le_one_div_of_le h_left_pos h_sq_lower

/-- The reciprocal-square contribution of one dyadic shell. -/
lemma dyadic_shell_recip_sq_bound_finset (gamma : ℕ → ℝ) (A : ℝ)
    (h_shell : ∀ k : ℕ, 1 ≤ k → ((gamma_dyadic_shell gamma k).ncard : ℝ) ≤ A * (k + 1 : ℝ) * (2 : ℝ) ^ k)
    (h_local : GammaLocallyFinite gamma) :
    ∀ k : ℕ, 1 ≤ k → Finset.sum (gamma_dyadic_shell_finite gamma h_local k).toFinset (fun n => 1 / (gamma n) ^ 2)
      ≤ A * (k + 1 : ℝ) / (2 : ℝ) ^ k := by
  intro k hk
  let s : Set ℕ := gamma_dyadic_shell gamma k
  let hfin : s.Finite := gamma_dyadic_shell_finite gamma h_local k

  have hterm : ∀ n ∈ hfin.toFinset, 1 / (gamma n)^2 ≤ 1 / (4 : ℝ)^k := by
    intro n hn
    exact reciprocal_sq_le_dyadic gamma k n (by simpa using hn)

  have hsum_le : Finset.sum hfin.toFinset (fun n => 1 / (gamma n)^2) ≤ Finset.sum hfin.toFinset (fun _n => 1 / (4 : ℝ)^k) :=
    Finset.sum_le_sum (fun n hn => hterm n hn)

  have h_const : Finset.sum hfin.toFinset (fun _n => 1 / (4 : ℝ)^k) = (hfin.toFinset.card : ℝ) * (1 / (4 : ℝ)^k) := by
    rw [Finset.sum_const]; norm_num

  have hcard_nat : hfin.toFinset.card = (gamma_dyadic_shell gamma k).ncard :=
    (Set.ncard_eq_toFinset_card (gamma_dyadic_shell gamma k) hfin).symm
  have hcard : (hfin.toFinset.card : ℝ) = ((gamma_dyadic_shell gamma k).ncard : ℝ) := by rw [hcard_nat]

  have h_shell' : (hfin.toFinset.card : ℝ) ≤ A * (k + 1 : ℝ) * (2 : ℝ)^k := by
    rw [hcard]; simpa [s] using h_shell k hk

  have h_four_nonneg : 0 ≤ (1 / (4 : ℝ)^k) := by positivity
  have hmul : (hfin.toFinset.card : ℝ) * (1 / (4 : ℝ)^k) ≤ (A * (k + 1 : ℝ) * (2 : ℝ)^k) * (1 / (4 : ℝ)^k) :=
    mul_le_mul_of_nonneg_right h_shell' h_four_nonneg

  calc Finset.sum hfin.toFinset (fun n => 1 / (gamma n)^2)
    _ ≤ Finset.sum hfin.toFinset (fun _n => 1 / (4 : ℝ)^k) := hsum_le
    _ = (hfin.toFinset.card : ℝ) * (1 / (4 : ℝ)^k) := h_const
    _ ≤ (A * (k + 1 : ℝ) * (2 : ℝ)^k) * (1 / (4 : ℝ)^k) := hmul
    _ = A * (k + 1 : ℝ) / (2 : ℝ)^k := by
      have htwo_ne : (2 : ℝ)^k ≠ 0 := pow_ne_zero k (by norm_num)
      have hpow2 : (4 : ℝ)^k = ((2 : ℝ)^k)^2 := by
        calc (4 : ℝ)^k = ((2 : ℝ)^2)^k := by norm_num
          _ = (2 : ℝ)^(2 * k) := by rw [pow_mul]
          _ = (2 : ℝ)^(k * 2) := by ring
          _ = ((2 : ℝ)^k)^2 := by rw [pow_mul]
      rw [hpow2]
      field_simp [htwo_ne]

/-- The numerical geometric-polynomial majorant needed for the dyadic proof. -/
lemma bound_k_geom (k : ℕ) : (k + 1 : ℝ) ≤ 4 * (3 / 2 : ℝ) ^ k := by
  induction' k with n _
  · norm_num
  · have hz : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n := by
      have h1 : (1 : ℝ) ^ n ≤ (3 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      rwa [one_pow] at h1
    have h_step : 4 * (3 / 2 : ℝ) ^ n + 2 * (3 / 2 : ℝ) ^ n = 4 * (3 / 2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]; ring
    have h_cast : (↑(n + 1) + 1 : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [h_cast]
    linarith

/-- The numerical geometric-polynomial majorant needed for the dyadic proof. -/
lemma summable_nat_add_one_div_two_pow : Summable (fun k : ℕ => (k + 1 : ℝ) / (2 : ℝ) ^ k) := by
  have h_bound : ∀ k : ℕ, (k + 1 : ℝ) / (2 : ℝ) ^ k ≤ 4 * (3 / 4 : ℝ) ^ k := by
    intro k
    have hk : (k + 1 : ℝ) ≤ 4 * (3 / 2 : ℝ) ^ k := bound_k_geom k
    have h2k : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    calc (k + 1 : ℝ) / (2 : ℝ) ^ k ≤ (4 * (3 / 2 : ℝ) ^ k) / (2 : ℝ) ^ k := div_le_div_of_nonneg_right hk (le_of_lt h2k)
      _ = 4 * ((3 / 2 : ℝ) ^ k / (2 : ℝ) ^ k) := by ring
      _ = 4 * (3 / 4 : ℝ) ^ k := by
        congr 1
        rw [← div_pow]
        ring_nf
  apply Summable.of_nonneg_of_le (fun _ => by positivity) h_bound
  apply Summable.mul_left 4
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- A nonnegative family with uniformly bounded finite subsums is summable. -/
lemma summable_of_nonneg_bounded_finset_sums (f : ℕ → ℝ) (h_nonneg : ∀ n, 0 ≤ f n) (B : ℝ)
    (h_bdd : ∀ S : Finset ℕ, ∑ i ∈ S, f i ≤ B) : Summable f := by
  exact summable_of_sum_le h_nonneg h_bdd

-- Geometric interval mappings for tail bounding
lemma exists_two_pow_gt (x : ℝ) : ∃ k : ℕ, x < (2 : ℝ) ^ k := by
  rcases exists_nat_gt x with ⟨k, hk⟩
  use k
  have h_le : ∀ m : ℕ, (m : ℝ) ≤ (2 : ℝ) ^ m := by
    intro m
    induction' m with n _
    · norm_num
    · push_cast
      have h_two : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
        have h1 : (1 : ℝ) ^ n ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
        rwa [one_pow] at h1
      have h_step : (2 : ℝ) ^ n + (2 : ℝ) ^ n = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
      linarith
  exact lt_of_lt_of_le hk (h_le k)

lemma finset_exists_two_pow_gt (S : Finset ℕ) (gamma : ℕ → ℝ) : ∃ K : ℕ, ∀ n ∈ S, |gamma n| < (2 : ℝ) ^ K := by
  refine Finset.induction_on S ?_ ?_
  · use 0; intro n hn; simp at hn
  · intro a s ha ih
    rcases ih with ⟨K_s, hKs⟩
    rcases exists_two_pow_gt |gamma a| with ⟨k_a, hka⟩
    use max K_s k_a
    intro n hn
    rw [Finset.mem_insert] at hn
    rcases hn with rfl | hns
    · exact lt_of_lt_of_le hka (pow_le_pow_right₀ (by norm_num) (Nat.le_max_right K_s k_a))
    · exact lt_of_lt_of_le (hKs n hns) (pow_le_pow_right₀ (by norm_num) (Nat.le_max_left K_s k_a))

lemma exists_dyadic_interval (x : ℝ) (h2 : 2 ≤ x) (K : ℕ) (hK : x < (2 : ℝ) ^ K) :
    ∃ k : ℕ, 1 ≤ k ∧ k < K ∧ (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1) := by
  have h_ex : ∃ k, x < (2 : ℝ) ^ k := ⟨K, hK⟩
  let k_min := Nat.find h_ex
  have hk_min : x < (2 : ℝ) ^ k_min := Nat.find_spec h_ex
  have hk_min_gt_1 : 1 < k_min := by
    by_contra h_not
    have h1 : k_min ≤ 1 := by omega
    rcases (show k_min = 0 ∨ k_min = 1 by omega) with h0 | h1
    · have h_zero_eval : (2 : ℝ) ^ 0 = 1 := by norm_num
      have h_lt_1 : x < 1 := by
        calc x < (2 : ℝ) ^ k_min := hk_min
             _ = (2 : ℝ) ^ 0 := by rw [h0]
             _ = 1 := h_zero_eval
      linarith
    · have h_one_eval : (2 : ℝ) ^ 1 = 2 := by norm_num
      have h_lt_2 : x < 2 := by
        calc x < (2 : ℝ) ^ k_min := hk_min
             _ = (2 : ℝ) ^ 1 := by rw [h1]
             _ = 2 := h_one_eval
      linarith
  let k := k_min - 1
  use k
  have hk1 : 1 ≤ k := by omega
  have hk_le_K : k_min ≤ K := Nat.find_min' h_ex hK
  have hk_lt_K : k < K := by omega
  have h_not_in : ¬ (x < (2 : ℝ) ^ k) := Nat.find_min h_ex (by omega)
  have hk_le_x : (2 : ℝ) ^ k ≤ x := not_lt.mp h_not_in
  have hk_plus : k + 1 = k_min := by omega
  have h_x_lt : x < (2 : ℝ) ^ (k + 1) := by
    have h_eq : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k_min := by rw [hk_plus]
    rw [h_eq]; exact hk_min
  exact ⟨hk1, hk_lt_K, hk_le_x, h_x_lt⟩

noncomputable def f_shell (gamma : ℕ → ℝ) (k n : ℕ) : ℝ :=
  if (2 : ℝ)^k ≤ |gamma n| ∧ |gamma n| < (2 : ℝ)^(k+1) then 1 / (gamma n)^2 else 0

lemma f_tail_eq_sum_shells (gamma : ℕ → ℝ) (n : ℕ) (K : ℕ) (hK : |gamma n| < (2 : ℝ)^K) :
    (if 2 ≤ |gamma n| then 1 / (gamma n)^2 else 0) = ∑ k ∈ Finset.Ico 1 K, f_shell gamma k n := by
  dsimp [f_shell]
  split_ifs with h2
  · rcases exists_dyadic_interval (|gamma n|) h2 K hK with ⟨k_val, hk1, hkK, hkle, hklt⟩
    have h_in : k_val ∈ Finset.Ico 1 K := Finset.mem_Ico.mpr ⟨hk1, hkK⟩
    rw [Finset.sum_eq_single k_val]
    · split_ifs with h_inner
      · rfl
      · exfalso; exact h_inner ⟨hkle, hklt⟩
    · intro b hb hb_neq
      split_ifs with h_inner
      · exfalso
        rcases h_inner with ⟨h1, h2_lt⟩
        rcases lt_trichotomy b k_val with hl | he | hg
        · have hl_le : b + 1 ≤ k_val := hl
          have hp : (2 : ℝ)^(b + 1) ≤ (2 : ℝ)^k_val := pow_le_pow_right₀ (by norm_num) hl_le
          linarith
        · exact hb_neq he
        · have hg_le : k_val + 1 ≤ b := hg
          have hp : (2 : ℝ)^(k_val + 1) ≤ (2 : ℝ)^b := pow_le_pow_right₀ (by norm_num) hg_le
          linarith
      · rfl
    · intro h_not_in
      exfalso; exact h_not_in h_in
  · symm
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    split_ifs with h_inner
    · exfalso
      rcases h_inner with ⟨h1, _h2_lt⟩
      have h2_le : (2 : ℝ) ≤ (2 : ℝ)^k := by
        have hz : (2 : ℝ)^1 ≤ (2 : ℝ)^k := pow_le_pow_right₀ (by norm_num) hk.1
        rwa [pow_one] at hz
      linarith
    · rfl

/-- Dyadic-shell summability assembly for reciprocal squares. -/
lemma summable_recip_sq_of_dyadic_shell_bounds (gamma : ℕ → ℝ) (h_local : GammaLocallyFinite gamma)
    (A : ℝ) (hA_nonneg : 0 ≤ A)
    (h_shell_recip : ∀ k : ℕ, 1 ≤ k → ∑ n ∈ (gamma_dyadic_shell_finite gamma h_local k).toFinset, 1 / (gamma n)^2 ≤ A * ((k + 1 : ℝ) / (2 : ℝ)^k))
    (h_numeric : Summable (fun k : ℕ => A * ((k + 1 : ℝ) / (2 : ℝ)^k))) :
    Summable (fun n => 1 / (gamma n)^2) := by
  let head := (gamma_head_finite gamma h_local).toFinset
  let T_sum := ∑' (k : ℕ), A * ((k + 1 : ℝ) / (2 : ℝ)^k)
  let B := (∑ n ∈ head, 1 / (gamma n)^2) + T_sum

  refine summable_of_nonneg_bounded_finset_sums (fun n => 1 / (gamma n)^2) (fun n => by positivity) B ?_
  intro S

  rcases finset_exists_two_pow_gt S gamma with ⟨K, hK_bound⟩

  have h_split : ∑ n ∈ S, 1 / (gamma n)^2 =
                 ∑ n ∈ S, (if |gamma n| < 2 then 1 / (gamma n)^2 else 0) +
                 ∑ n ∈ S, (if 2 ≤ |gamma n| then 1 / (gamma n)^2 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · exfalso; linarith
    · ring
    · ring
    · exfalso; linarith

  rw [h_split]
  apply add_le_add
  · calc ∑ n ∈ S, (if |gamma n| < 2 then 1 / (gamma n)^2 else 0)
      _ ≤ ∑ n ∈ S ∪ head, (if |gamma n| < 2 then 1 / (gamma n)^2 else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_union_left
        · intro x _ _
          split_ifs
          · positivity
          · rfl
      _ = ∑ n ∈ head, (if |gamma n| < 2 then 1 / (gamma n)^2 else 0) := by
        symm
        apply Finset.sum_subset
        · exact Finset.subset_union_right
        · intro x _ hnx
          have h_not_in_head : ¬(|gamma x| < 2) := by
            intro hc
            have h_in : x ∈ head := by simpa [head, gamma_head_finite, gamma_head] using hc
            exact hnx h_in
          rw [ite_eq_right h_not_in_head]
      _ = ∑ n ∈ head, 1 / (gamma n)^2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have h_lt : |gamma x| < 2 := by simpa [head, gamma_head_finite, gamma_head] using hx
        rw [ite_eq_left h_lt]

  · calc ∑ n ∈ S, (if 2 ≤ |gamma n| then 1 / (gamma n)^2 else 0)
      _ = ∑ n ∈ S, ∑ k ∈ Finset.Ico 1 K, f_shell gamma k n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact f_tail_eq_sum_shells gamma n K (hK_bound n hn)
      _ = ∑ k ∈ Finset.Ico 1 K, ∑ n ∈ S, f_shell gamma k n := Finset.sum_comm
      _ ≤ ∑ k ∈ Finset.Ico 1 K, ∑ n ∈ (gamma_dyadic_shell_finite gamma h_local k).toFinset, 1 / (gamma n)^2 := by
        apply Finset.sum_le_sum
        intro k _
        let shell_k := (gamma_dyadic_shell_finite gamma h_local k).toFinset
        calc ∑ n ∈ S, f_shell gamma k n
          _ ≤ ∑ n ∈ S ∪ shell_k, f_shell gamma k n := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.subset_union_left
            · intro x _ _
              dsimp [f_shell]; split_ifs <;> [positivity; rfl]
          _ = ∑ n ∈ shell_k, f_shell gamma k n := by
            symm
            apply Finset.sum_subset
            · exact Finset.subset_union_right
            · intro x _ hnx
              dsimp [f_shell]
              have h_not_in_shell : ¬((2 : ℝ) ^ k ≤ |gamma x| ∧ |gamma x| < (2 : ℝ) ^ (k + 1)) := by
                intro hc
                have h_in : x ∈ shell_k := by simpa [shell_k, gamma_dyadic_shell_finite, gamma_dyadic_shell] using hc
                exact hnx h_in
              rw [ite_eq_right h_not_in_shell]
          _ = ∑ n ∈ shell_k, 1 / (gamma n)^2 := by
            apply Finset.sum_congr rfl
            intro x hx
            dsimp [f_shell]
            have h_and : (2 : ℝ) ^ k ≤ |gamma x| ∧ |gamma x| < (2 : ℝ) ^ (k + 1) := by
              simpa [shell_k, gamma_dyadic_shell_finite, gamma_dyadic_shell] using hx
            rw [ite_eq_left h_and]
      _ ≤ ∑ k ∈ Finset.Ico 1 K, A * ((k + 1 : ℝ) / (2 : ℝ)^k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h_shell_recip k (Finset.mem_Ico.mp hk).1
      _ ≤ T_sum := sum_le_hasSum (Finset.Ico 1 K) (fun _ _ => by positivity) h_numeric.hasSum

/-- Equation 160: the Riemann--von Mangoldt counting bound gives reciprocal-square summability. -/
lemma eq_160_rvm_density (gamma : ℕ → ℝ) (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    Summable (fun n => 1 / (gamma n)^2) := by
  rcases rvm_dyadic_shell_count gamma h_local h_rvm with ⟨A, hA_pos, h_shell_count⟩
  have h_shell_recip : ∀ k : ℕ, 1 ≤ k →
      Finset.sum (gamma_dyadic_shell_finite gamma h_local k).toFinset (fun n => 1 / (gamma n)^2) ≤ A * ((k + 1 : ℝ) / (2 : ℝ)^k) := by
    intro k hk
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using (dyadic_shell_recip_sq_bound_finset gamma A h_shell_count h_local k hk)
  have h_numeric : Summable (fun k : ℕ => A * ((k + 1 : ℝ) / (2 : ℝ)^k)) := by
    simpa [mul_assoc, mul_div_assoc] using (summable_nat_add_one_div_two_pow.mul_left A)
  exact summable_recip_sq_of_dyadic_shell_bounds gamma h_local A (le_of_lt hA_pos) h_shell_recip h_numeric















-- =========================================================================
-- Convergence of the Symmetric Hadamard Product (Pure P-Space Port)
-- =========================================================================

-- Classical Fact: The number of roots within any bounded ordinate strip is strictly finite.
lemma classical_finite_zeros_in_compact (gamma : ℕ → ℝ) (h_local : GammaLocallyFinite gamma) (T : ℝ) :
    Set.Finite {n | |gamma n| ≤ T} := by
  exact h_local T

/-- Native P-space deviation magnitude from unity.
Evaluated entirely via native P-space geometries extracted from `p : PSpace`. -/
noncomputable def P_rho_dev_mag (β γ : ℝ) (p : PSpace) : ℝ :=
  let σ := p.mag.val * Real.cos (2 * Real.pi * p.phase)
  let t := p.mag.val * Real.sin (2 * Real.pi * p.phase)
  if h : 0 < M_rho_real β γ σ t ∧ 0 < M_rho_real (1 - β) γ σ t ∧
         0 < M_rho_real β (-γ) σ t ∧ 0 < M_rho_real (1 - β) (-γ) σ t
  then (sub_state (eq_152_P_rho_orbit β γ σ t h.1 h.2.1 h.2.2.1 h.2.2.2) one_state).mag.val
  else 0

/-- Native P-space Taylor upper bound for the orbit deviation from unity.
Evaluated entirely in P-space via the quadratic approximation and remainder state magnitudes. -/
noncomputable def P_rho_taylor_bound (s_state rho_state : ℝ → ℝ → PSpace) (β γ : ℝ) (p : PSpace) : ℝ :=
  let σ := p.mag.val * Real.cos (2 * Real.pi * p.phase)
  let t := p.mag.val * Real.sin (2 * Real.pi * p.phase)
  if h : 0 < M_rho_real β γ σ t ∧ 0 < M_rho_real (1 - β) γ σ t ∧
         0 < M_rho_real β (-γ) σ t ∧ 0 < M_rho_real (1 - β) (-γ) σ t
  then (sub_state (eq_156_P_rho_approx s_state rho_state β γ σ t) one_state).mag.val +
       (eq_156_P_rho_rem β γ σ t s_state rho_state h.1 h.2.1 h.2.2.1 h.2.2.2).mag.val
  else 0

/--
Lemma 4.2.1 (Absolute convergence of the symmetric product evaluated natively in P-space).
Zero C-standard topological dependencies.
Explicitly consumes Equations 158, 159, and 160.
-/
lemma lemma_4_2_1_abs_conv_sym_product
    (s_state rho_state : ℝ → ℝ → PSpace)
    (K : Set PSpace)
    (beta gamma : ℕ → ℝ)
    (hK_compact : IsCompact K)
    (h_beta_bounds : ∀ n, 0 ≤ beta n ∧ beta n ≤ 1)
    (h_local : GammaLocallyFinite gamma)
    (h_rvm : HasRVMCount gamma)
    (h_s : ∀ σ t, proj (s_state σ t) = Complex.mk σ t)
    (h_rho : ∀ b g, proj (rho_state b g) = rho b g)
    (h_approx_eval : ∀ β γ σ t, proj (eq_156_P_rho_approx s_state rho_state β γ σ t) =
      1 - ((proj (s_state σ t))^2 / 2) * (((proj (rho_state β γ))⁻¹)^2 + ((proj (rho_state β (-γ)))⁻¹)^2 + ((proj (rho_state (1 - β) γ))⁻¹)^2 + ((proj (rho_state (1 - β) (-γ)))⁻¹)^2))
    (h_rem_bound : ∀ R > 0, ∃ C > 0, ∃ T > 1, ∀ β γ σ t : ℝ, ‖proj (s_state σ t)‖ ≤ R → 0 ≤ β → β ≤ 1 → |γ| > T →
      ∀ (h1 : 0 < M_rho_real β γ σ t) (h2 : 0 < M_rho_real (1 - β) γ σ t)
        (h3 : 0 < M_rho_real β (-γ) σ t) (h4 : 0 < M_rho_real (1 - β) (-γ) σ t),
      ‖proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4)‖ ≤ C * ‖proj (s_state σ t)‖^3 / |γ|^3)
    (h_head_bound : ∀ n, ∃ B ≥ 0, ∀ p ∈ K, P_rho_dev_mag (beta n) (gamma n) p ≤ B) :
    TendstoUniformlyOn
      (fun (k : Finset ℕ) p => ∑ i ∈ k, P_rho_dev_mag (beta i) (gamma i) p)
      (fun p => ∑' i, P_rho_dev_mag (beta i) (gamma i) p)
      Filter.atTop K := by

  have h_cont_norm : Continuous (fun p : PSpace => ‖proj p‖) := Continuous.norm lemma_2_1_1_continuous_proj

  obtain ⟨R_sup, hR_sup⟩ := hK_compact.bddAbove_image h_cont_norm.continuousOn
  let R := max R_sup 1
  have hR_pos : R > 0 := by linarith [le_max_right R_sup 1]

  have hK_bound : ∀ p ∈ K, ‖proj p‖ ≤ R := by
    intro p hp
    exact le_trans (hR_sup (Set.mem_image_of_mem _ hp)) (le_max_left R_sup 1)

  have h_bound_val := eq_159_P_rho_orbit_bound s_state rho_state h_rho h_approx_eval h_rem_bound R hR_pos
  rcases h_bound_val with ⟨C, hC_pos, T, _hT_pos, h_asymp⟩

  have h_recip_sq : Summable (fun n => 1 / (gamma n)^2) :=
    eq_160_rvm_density gamma h_local h_rvm

  let M_tail := fun i => if T < |gamma i| then C * R^2 * (1 / (gamma i)^2) else 0
  let M_head := fun i => if |gamma i| ≤ T then Classical.choose (h_head_bound i) else 0
  let M := fun i => M_tail i + M_head i

  have h_summable_tail : Summable M_tail := by
    have h_scaled : Summable (fun n => C * R^2 * (1 / (gamma n)^2)) :=
      Summable.mul_left (C * R^2) h_recip_sq
    apply Summable.of_nonneg_of_le
    · intro i; dsimp [M_tail]; split_ifs <;> positivity
    · intro i; dsimp [M_tail]; split_ifs <;> [exact le_rfl; positivity]
    · exact h_scaled

  have h_summable_head : Summable M_head := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (classical_finite_zeros_in_compact gamma h_local T)
    intro i hi
    dsimp [Function.support, M_head] at hi
    by_contra h_not
    have h_gt : T < |gamma i| := lt_of_not_ge h_not
    have h_not_le : ¬(|gamma i| ≤ T) := not_le_of_gt h_gt
    have h_zero : (if |gamma i| ≤ T then Classical.choose (h_head_bound i) else 0) = 0 := by simp [h_not_le]
    exact hi h_zero

  have h_summable_M : Summable M := Summable.add h_summable_tail h_summable_head

  have h_bound_M : ∀ i, ∀ p ∈ K, ‖P_rho_dev_mag (beta i) (gamma i) p‖ ≤ M i := by
    intro i p hp
    dsimp [M, M_tail, M_head]
    have h_nonneg_dev : 0 ≤ P_rho_dev_mag (beta i) (gamma i) p := by
      dsimp [P_rho_dev_mag]
      split_ifs
      · exact (sub_state _ one_state).mag.property
      · exact le_rfl
    rw [abs_of_nonneg h_nonneg_dev]

    by_cases h_tail : T < |gamma i|
    · have h_not_le : ¬ |gamma i| ≤ T := not_le.mpr h_tail
      rw [ite_eq_left h_tail, ite_eq_right h_not_le, add_zero]
      dsimp [P_rho_dev_mag]
      let σ := p.mag.val * Real.cos (2 * Real.pi * p.phase)
      let t := p.mag.val * Real.sin (2 * Real.pi * p.phase)
      split_ifs with h_cond
      · have hs_radius : ‖proj (s_state σ t)‖ ≤ R := by
          have h_sqrt_le : Real.sqrt (σ^2 + t^2) ≤ R := by
            have h_trig : (Real.cos (2 * Real.pi * p.phase))^2 + (Real.sin (2 * Real.pi * p.phase))^2 = 1 :=
              Real.cos_sq_add_sin_sq (2 * Real.pi * p.phase)
            have h_alg : σ^2 + t^2 = p.mag.val^2 := by
              dsimp [σ, t]
              calc (p.mag.val * Real.cos (2 * Real.pi * p.phase))^2 + (p.mag.val * Real.sin (2 * Real.pi * p.phase))^2
                _ = p.mag.val^2 * ((Real.cos (2 * Real.pi * p.phase))^2 + (Real.sin (2 * Real.pi * p.phase))^2) := by ring
                _ = p.mag.val^2 * 1 := by rw [h_trig]
                _ = p.mag.val^2 := by ring
            rw [h_alg, Real.sqrt_sq p.mag.property.le]
            have h_p_norm : p.mag.val = ‖proj p‖ := mag_eq_norm_proj p
            rw [h_p_norm]
            exact hK_bound p hp
          rw [h_s]
          have h_sq : Complex.normSq (Complex.mk σ t) = σ^2 + t^2 := by
            dsimp [Complex.normSq]
            ring
          rw [Complex.norm_def, h_sq]
          exact h_sqrt_le

        have h_orbit_norm_eq : (sub_state (eq_152_P_rho_orbit (beta i) (gamma i) σ t h_cond.1 h_cond.2.1 h_cond.2.2.1 h_cond.2.2.2) one_state).mag.val =
            ‖proj (eq_152_P_rho_orbit (beta i) (gamma i) σ t h_cond.1 h_cond.2.1 h_cond.2.2.1 h_cond.2.2.2) - 1‖ := by
          rw [mag_eq_norm_proj, proj_sub_state]
          have h_one : proj one_state = 1 := by
            dsimp [one_state, proj]
            have h_zero : 2 * Real.pi * Complex.I * (0 : ℂ) = 0 := by ring
            rw [h_zero, Complex.exp_zero, mul_one]
          rw [h_one]
        rw [h_orbit_norm_eq]

        have h_app := h_asymp (beta i) (gamma i) σ t hs_radius (h_beta_bounds i).1 (h_beta_bounds i).2 h_tail h_cond.1 h_cond.2.1 h_cond.2.2.1 h_cond.2.2.2
        have h_rewrite : C * R^2 / (gamma i)^2 = C * R^2 * (1 / (gamma i)^2) := by ring

        have hs_sq_le : ‖proj (s_state σ t)‖^2 ≤ R^2 := by
          nlinarith [norm_nonneg (proj (s_state σ t)), hs_radius]
        have h_div_le : C * ‖proj (s_state σ t)‖^2 / (gamma i)^2 ≤ C * R^2 / (gamma i)^2 := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hs_sq_le hC_pos.le
          · exact sq_nonneg (gamma i)
        rw [h_rewrite] at h_div_le
        exact le_trans h_app h_div_le
      · positivity
    · have h_head : |gamma i| ≤ T := not_lt.mp h_tail
      rw [ite_eq_right h_tail, ite_eq_left h_head, zero_add]
      have h_spec := Classical.choose_spec (h_head_bound i)
      exact h_spec.2 p hp

  exact tendstoUniformlyOn_tsum h_summable_M h_bound_M












-- Section 4.2.2: Pointwise convergence of the phase series

/--
Lemma 4.2.2 (Pointwise convergence of phases & phase accumulation).
Adapted to Native Real Phase Evaluation, purging C_star topological lift requirements.
Consumes Lemma 4.2.1 directly by evaluating the uniform limit over a compact singleton.
-/
lemma lemma_4_2_2_pointwise_convergence
    (s_state rho_state : ℝ → ℝ → PSpace)
    (beta gamma : ℕ → ℝ) (Phi_H : ℝ → ℝ → ℝ)
    (h_beta_bounds : ∀ n, 0 ≤ beta n ∧ beta n ≤ 1)
    (h_local : GammaLocallyFinite gamma)
    (h_rvm : HasRVMCount gamma)
    (t : ℝ)
    (h_s : ∀ σ t, proj (s_state σ t) = Complex.mk σ t)
    (h_rho : ∀ b g, proj (rho_state b g) = rho b g)
    (h_approx_eval : ∀ β γ σ t, proj (eq_156_P_rho_approx s_state rho_state β γ σ t) =
      1 - ((proj (s_state σ t))^2 / 2) * (((proj (rho_state β γ))⁻¹)^2 + ((proj (rho_state β (-γ)))⁻¹)^2 + ((proj (rho_state (1 - β) γ))⁻¹)^2 + ((proj (rho_state (1 - β) (-γ)))⁻¹)^2))
    (h_rem_bound : ∀ R > 0, ∃ C > 0, ∃ T > 1, ∀ β γ σ t : ℝ, ‖proj (s_state σ t)‖ ≤ R → 0 ≤ β → β ≤ 1 → |γ| > T →
      ∀ (h1 : 0 < M_rho_real β γ σ t) (h2 : 0 < M_rho_real (1 - β) γ σ t)
        (h3 : 0 < M_rho_real β (-γ) σ t) (h4 : 0 < M_rho_real (1 - β) (-γ) σ t),
      ‖proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4)‖ ≤ C * ‖proj (s_state σ t)‖^3 / |γ|^3)
    (h_phase_bound : ∀ k σ, P_rho_dev_mag (beta k) (gamma k) (s_state σ t) ≤ P_rho_taylor_bound s_state rho_state (beta k) (gamma k) (s_state σ t)) :
    (∀ σ, Summable (fun k => P_rho_dev_mag (beta k) (gamma k) (s_state σ t))) ∧
    (∀ σ, xi_P_phase beta gamma Phi_H σ t = Phi_H σ t + ∑' i, (theta_n 2 (gamma i - t) + psi_quad_sum (beta i) (gamma i) σ t)) := by
  have h_sum_dev : ∀ σ, Summable (fun k => P_rho_dev_mag (beta k) (gamma k) (s_state σ t)) := by
    intro σ
    let p := s_state σ t
    let K : Set PSpace := {p}
    have hK_compact : IsCompact K := isCompact_singleton
    have h_head_bound : ∀ n, ∃ B ≥ 0, ∀ q ∈ K, P_rho_dev_mag (beta n) (gamma n) q ≤ B := by
      intro n
      use P_rho_taylor_bound s_state rho_state (beta n) (gamma n) p
      constructor
      · have h_nonneg : 0 ≤ P_rho_dev_mag (beta n) (gamma n) p := by
          dsimp [P_rho_dev_mag]
          split_ifs
          · exact (sub_state _ one_state).mag.property
          · exact le_rfl
        exact le_trans h_nonneg (h_phase_bound n σ)
      · intro q hq
        rw [Set.mem_singleton_iff] at hq
        rw [hq]
        exact h_phase_bound n σ
    have h_4_2_1 := lemma_4_2_1_abs_conv_sym_product s_state rho_state K beta gamma hK_compact h_beta_bounds h_local h_rvm h_s h_rho h_approx_eval h_rem_bound h_head_bound
    have h_tendsto := TendstoUniformlyOn.tendsto_at h_4_2_1 (Set.mem_singleton p)
    exact ⟨_, h_tendsto⟩
  have h_identity : ∀ σ, xi_P_phase beta gamma Phi_H σ t = Phi_H σ t + ∑' i, (theta_n 2 (gamma i - t) + psi_quad_sum (beta i) (gamma i) σ t) := by
    intro σ
    rfl
  exact ⟨h_sum_dev, h_identity⟩


-- Section 4.2.3: Termwise differentiability of zero phases

/-- Lemma 4.2.3 (Differentiability of individual zero phases).
Restored and evaluated exactly to the continuous kernel outside the singularity.
Structurally demands the 3.3 Zero Kernel. -/
lemma lemma_4_2_3_diff_zero_phase (β γ σ t : ℝ) (h_neq : σ ≠ β) :
    deriv (fun x => psi_rho β γ x t) σ = K_rho β γ σ t + C_rho β γ := by
  -- Explicitly invoke Lemma 3.3 using the required inequality hypothesis h_neq
  rw [lemma_3_3_zero_kernel β γ σ t h_neq]
  -- Unfold the Cauchy kernel and constant offset definitions to close the algebra
  dsimp [K_rho, C_rho]
  ring



-- Section 4.2.4: Uniform convergence of the differentiated series

/-- Sum of the Cauchy-like kernels over a symmetric quadruplet (Equation 176) -/
noncomputable def S_rho (β γ σ t : ℝ) : ℝ :=
  K_rho β γ σ t + K_rho (1 - β) γ σ t + K_rho β (-γ) σ t + K_rho (1 - β) (-γ) σ t

/-- Connects `S_rho` directly to `quad_sum` of `K_rho` and to the spatial derivative
of `psi_rho` via Lemma 3.4.2 (`lemma_3_4_2_global_phase_reduction`). -/
lemma S_rho_eq_quad_sum_deriv_psi_rho (β γ σ t : ℝ) (h_sigma : σ ≠ β) (h_sigma_refl : σ ≠ 1 - β) :
    S_rho β γ σ t = quad_sum (fun b g => deriv (fun x => psi_rho b g x t) σ) β γ := by
  rw [lemma_3_4_2_global_phase_reduction β γ σ t h_sigma h_sigma_refl]
  dsimp [S_rho, quad_sum]
  ring

/-- Connects `S_rho` directly to the spatial derivative of the quadruplet phase `psi_quad_sum`
by consuming Lemma 3.3 (`lemma_3_3_zero_kernel`), Lemma 3.4.1 (`lemma_3_4_1_offset_cancellation`),
and Lemma 3.4.2 (`lemma_3_4_2_global_phase_reduction`). -/
lemma hasDerivAt_psi_quad_sum (β γ σ t : ℝ) (h_n1 : σ ≠ β) (h_n2 : σ ≠ 1 - β) :
    HasDerivAt (fun x => psi_quad_sum β γ x t) (S_rho β γ σ t) σ := by
  have h_diff_psi (b g : ℝ) (hb : σ ≠ b) : DifferentiableAt ℝ (fun x => psi_rho b g x t) σ := by
    dsimp [psi_rho]
    exact ((differentiableAt_A_rho b g σ t hb).add (differentiableAt_B_rho b g σ t)).add
      (differentiableAt_const (const_rho b g))
  have hd1 : HasDerivAt (fun x => psi_rho β γ x t) (K_rho β γ σ t + C_rho β γ) σ := by
    rw [← lemma_4_2_3_diff_zero_phase β γ σ t h_n1]
    exact (h_diff_psi β γ h_n1).hasDerivAt
  have hd2 : HasDerivAt (fun x => psi_rho (1 - β) γ x t) (K_rho (1 - β) γ σ t + C_rho (1 - β) γ) σ := by
    rw [← lemma_4_2_3_diff_zero_phase (1 - β) γ σ t h_n2]
    exact (h_diff_psi (1 - β) γ h_n2).hasDerivAt
  have hd3 : HasDerivAt (fun x => psi_rho β (-γ) x t) (K_rho β (-γ) σ t + C_rho β (-γ)) σ := by
    rw [← lemma_4_2_3_diff_zero_phase β (-γ) σ t h_n1]
    exact (h_diff_psi β (-γ) h_n1).hasDerivAt
  have hd4 : HasDerivAt (fun x => psi_rho (1 - β) (-γ) x t) (K_rho (1 - β) (-γ) σ t + C_rho (1 - β) (-γ)) σ := by
    rw [← lemma_4_2_3_diff_zero_phase (1 - β) (-γ) σ t h_n2]
    exact (h_diff_psi (1 - β) (-γ) h_n2).hasDerivAt
  have hd_sum := ((hd1.add hd2).add hd3).add hd4
  have h_eval :
      (K_rho β γ σ t + C_rho β γ) +
      (K_rho (1 - β) γ σ t + C_rho (1 - β) γ) +
      (K_rho β (-γ) σ t + C_rho β (-γ)) +
      (K_rho (1 - β) (-γ) σ t + C_rho (1 - β) (-γ)) = S_rho β γ σ t := by
    have h_rearrange :
      (K_rho β γ σ t + C_rho β γ) +
      (K_rho (1 - β) γ σ t + C_rho (1 - β) γ) +
      (K_rho β (-γ) σ t + C_rho β (-γ)) +
      (K_rho (1 - β) (-γ) σ t + C_rho (1 - β) (-γ)) =
      S_rho β γ σ t + (C_rho β γ + C_rho (1 - β) (-γ) + C_rho β (-γ) + C_rho (1 - β) γ) := by
      dsimp [S_rho]; ring
    rw [h_rearrange, lemma_3_4_1_offset_cancellation β γ, add_zero]
  dsimp [psi_quad_sum]
  rw [← h_eval]
  exact hd_sum

lemma deriv_psi_quad_sum (β γ σ t : ℝ) (h_n1 : σ ≠ β) (h_n2 : σ ≠ 1 - β) :
    deriv (fun x => psi_quad_sum β γ x t) σ = S_rho β γ σ t :=
  (hasDerivAt_psi_quad_sum β γ σ t h_n1 h_n2).deriv

lemma S_rho_conj_num_cancel (X : ℝ) :
    (γ - t) * (X^2 + (-γ - t)^2) + (-γ - t) * (X^2 + (γ - t)^2) =
    2 * t * (γ^2 - X^2 - t^2) := by
  ring

lemma S_rho_conj_den_expand (X : ℝ) :
    (X^2 + (γ - t)^2) * (X^2 + (-γ - t)^2) =
    (X^2 + γ^2 + t^2)^2 - 4 * γ^2 * t^2 := by
  ring

/-- Unconditional real bound for a single Cauchy denominator term. -/
lemma abs_div_add_sq_le (A B : ℝ) : |B / (A^2 + B^2)| ≤ 1 / |B| := by
  by_cases hB : B = 0
  · subst hB
    simp
  · have hB_abs_pos : 0 < |B| := abs_pos.mpr hB
    have hB2_pos : 0 < B^2 := sq_pos_of_ne_zero hB
    have h_den_pos : 0 < A^2 + B^2 := by positivity
    rw [abs_div, abs_of_pos h_den_pos]
    rw [div_le_div_iff₀ h_den_pos hB_abs_pos]
    have h_sq : |B| * |B| = B^2 := by rw [← sq, sq_abs]
    have h_A2 : 0 ≤ A^2 := sq_nonneg A
    linarith

/-- Uniform in-`σ` bound for a single `K_rho` term. -/
lemma K_rho_abs_le (β γ σ t : ℝ) :
    |K_rho β γ σ t| ≤ (1 / (2 * Real.pi)) * (1 / |γ - t|) := by
  dsimp [K_rho]
  have h_pi_pos : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
  have h_coeff_pos : 0 < 1 / (2 * Real.pi) := one_div_pos.mpr h_pi_pos
  rw [abs_mul, abs_of_pos h_coeff_pos]
  exact mul_le_mul_of_nonneg_left (abs_div_add_sq_le (β - σ) (γ - t)) (le_of_lt h_coeff_pos)

/-- Uniform in-`y` point bound for `S_rho` on the low-height head. -/
noncomputable def S_rho_point_bound (γ t : ℝ) : ℝ :=
  2 * ((1 / (2 * Real.pi)) * (1 / |γ - t|) + (1 / (2 * Real.pi)) * (1 / |-γ - t|))

lemma S_rho_norm_le_point_bound (β γ y t : ℝ) :
    ‖S_rho β γ y t‖ ≤ S_rho_point_bound γ t := by
  rw [Real.norm_eq_abs]
  dsimp [S_rho, S_rho_point_bound]
  have h1 := K_rho_abs_le β γ y t
  have h2 := K_rho_abs_le (1 - β) γ y t
  have h3 := K_rho_abs_le β (-γ) y t
  have h4 := K_rho_abs_le (1 - β) (-γ) y t
  have h_tri1 := abs_add_le (K_rho β γ y t + K_rho (1 - β) γ y t + K_rho β (-γ) y t) (K_rho (1 - β) (-γ) y t)
  have h_tri2 := abs_add_le (K_rho β γ y t + K_rho (1 - β) γ y t) (K_rho β (-γ) y t)
  have h_tri3 := abs_add_le (K_rho β γ y t) (K_rho (1 - β) γ y t)
  linarith

/-- Inverse-square tail bound for a conjugate pair of Cauchy kernels using `S_rho_conj_num_cancel`. -/
lemma K_rho_pair_tail_bound (β γ y t : ℝ) (hγ : 2 * |t| + 1 < |γ|) :
    |K_rho β γ y t + K_rho β (-γ) y t| ≤ ((64 * |t|) / (2 * Real.pi)) * (1 / γ^2) := by
  let X := β - y
  let D1 := X^2 + (γ - t)^2
  let D2 := X^2 + (-γ - t)^2
  have ht_nonneg : 0 ≤ |t| := abs_nonneg t
  have hX2_nonneg : 0 ≤ X^2 := sq_nonneg X
  have hγ_pos : 0 < |γ| := by linarith
  have hγ2_pos : 0 < γ^2 := by
    have h_sq : |γ|^2 = γ^2 := sq_abs γ
    nlinarith

  have h_sub1 : |γ| ≤ |γ - t| + |t| := by
    have h := abs_sub_le γ t 0
    simpa only [sub_zero] using h
  have h_sub2 : |γ| ≤ |-γ - t| + |t| := by
    have h := abs_sub_le (-γ) t 0
    simpa only [sub_zero, abs_neg] using h

  have h_gt1 : |γ| < 2 * |γ - t| := by linarith
  have h_gt2 : |γ| < 2 * |-γ - t| := by linarith

  have h_sq1 : γ^2 ≤ 4 * (γ - t)^2 := by
    have ha1 : |γ|^2 = γ^2 := sq_abs γ
    have ha2 : |γ - t|^2 = (γ - t)^2 := sq_abs (γ - t)
    have h_mul : |γ| * |γ| ≤ (2 * |γ - t|) * (2 * |γ - t|) := by
      nlinarith [abs_nonneg (γ - t)]
    nlinarith

  have h_sq2 : γ^2 ≤ 4 * (-γ - t)^2 := by
    have ha1 : |γ|^2 = γ^2 := sq_abs γ
    have ha2 : |-γ - t|^2 = (-γ - t)^2 := sq_abs (-γ - t)
    have h_mul : |γ| * |γ| ≤ (2 * |-γ - t|) * (2 * |-γ - t|) := by
      nlinarith [abs_nonneg (-γ - t)]
    nlinarith

  have hD1_bound : γ^2 ≤ 4 * D1 := by
    dsimp [D1]
    linarith
  have hD2_bound : 4 * X^2 + γ^2 ≤ 4 * D2 := by
    dsimp [D2]
    linarith

  have hD1_pos : 0 < D1 := by linarith
  have hD2_pos : 0 < D2 := by linarith
  have hD12_pos : 0 < D1 * D2 := mul_pos hD1_pos hD2_pos

  have h_prod_bound : γ^2 * (4 * X^2 + γ^2) ≤ 16 * (D1 * D2) := by
    have h_mul : γ^2 * (4 * X^2 + γ^2) ≤ (4 * D1) * (4 * D2) := by
      nlinarith
    linarith

  have ht2_le : t^2 ≤ γ^2 := by
    have ha1 : |t|^2 = t^2 := sq_abs t
    have ha2 : |γ|^2 = γ^2 := sq_abs γ
    have h_lt : |t| ≤ |γ| := by linarith
    have h_mul : |t| * |t| ≤ |γ| * |γ| := by nlinarith
    nlinarith

  have h_num_abs : |γ^2 - X^2 - t^2| ≤ 2 * γ^2 + X^2 := by
    rw [abs_le]
    constructor <;> linarith

  have h_num_gamma : |γ^2 - X^2 - t^2| * γ^2 ≤ 32 * (D1 * D2) := by
    have h1 : |γ^2 - X^2 - t^2| * γ^2 ≤ (2 * γ^2 + X^2) * γ^2 :=
      mul_le_mul_of_nonneg_right h_num_abs (le_of_lt hγ2_pos)
    have h2 : (2 * γ^2 + X^2) * γ^2 ≤ 2 * (γ^2 * (4 * X^2 + γ^2)) := by
      nlinarith [mul_nonneg (le_of_lt hγ2_pos) hX2_nonneg]
    linarith

  have h_frac_le : |γ^2 - X^2 - t^2| / (D1 * D2) ≤ 32 / γ^2 :=
    (div_le_div_iff₀ hD12_pos hγ2_pos).mpr (by linarith)

  have h_pair_eq : K_rho β γ y t + K_rho β (-γ) y t =
      (1 / (2 * Real.pi)) * ((2 * t * (γ^2 - X^2 - t^2)) / (D1 * D2)) := by
    dsimp [K_rho]
    change (1 / (2 * Real.pi)) * ((γ - t) / D1) + (1 / (2 * Real.pi)) * ((-γ - t) / D2) =
      (1 / (2 * Real.pi)) * ((2 * t * (γ^2 - X^2 - t^2)) / (D1 * D2))
    rw [← mul_add]
    congr 1
    rw [div_add_div _ _ (ne_of_gt hD1_pos) (ne_of_gt hD2_pos)]
    congr 1
    dsimp [D1, D2]
    ring

  rw [h_pair_eq]
  have h_pi_pos : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
  have h_coeff_pos : 0 < 1 / (2 * Real.pi) := one_div_pos.mpr h_pi_pos
  have h_split : (2 * t * (γ^2 - X^2 - t^2)) / (D1 * D2) =
      (2 * t) * ((γ^2 - X^2 - t^2) / (D1 * D2)) := by ring
  rw [h_split, abs_mul, abs_of_pos h_coeff_pos, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [abs_div, abs_of_pos hD12_pos]
  have h_step : 2 * |t| * (|γ^2 - X^2 - t^2| / (D1 * D2)) ≤ 2 * |t| * (32 / γ^2) :=
    mul_le_mul_of_nonneg_left h_frac_le (by positivity)
  have h_step2 : (1 / (2 * Real.pi)) * (2 * |t| * (|γ^2 - X^2 - t^2| / (D1 * D2))) ≤
      (1 / (2 * Real.pi)) * (2 * |t| * (32 / γ^2)) :=
    mul_le_mul_of_nonneg_left h_step (le_of_lt h_coeff_pos)
  calc (1 / (2 * Real.pi)) * (2 * |t| * (|γ^2 - X^2 - t^2| / (D1 * D2)))
    _ ≤ (1 / (2 * Real.pi)) * (2 * |t| * (32 / γ^2)) := h_step2
    _ = ((64 * |t|) / (2 * Real.pi)) * (1 / γ^2) := by ring

/-- Inverse-square tail bound for the full symmetric quadruplet `S_rho`. -/
lemma S_rho_tail_bound (β γ y t : ℝ) (hγ : 2 * |t| + 1 < |γ|) :
    ‖S_rho β γ y t‖ ≤ ((128 * |t|) / (2 * Real.pi) + 1) * (1 / γ^2) := by
  rw [Real.norm_eq_abs]
  have h_rearrange : S_rho β γ y t =
      (K_rho β γ y t + K_rho β (-γ) y t) + (K_rho (1 - β) γ y t + K_rho (1 - β) (-γ) y t) := by
    dsimp [S_rho]
    ring
  rw [h_rearrange]
  have h1 := K_rho_pair_tail_bound β γ y t hγ
  have h2 := K_rho_pair_tail_bound (1 - β) γ y t hγ
  have h_tri := abs_add_le (K_rho β γ y t + K_rho β (-γ) y t) (K_rho (1 - β) γ y t + K_rho (1 - β) (-γ) y t)
  have h_nonneg : 0 ≤ 1 / γ^2 := by positivity
  have h_alg : ((64 * |t|) / (2 * Real.pi)) * (1 / γ^2) + ((64 * |t|) / (2 * Real.pi)) * (1 / γ^2) + (1 / γ^2) =
      ((128 * |t|) / (2 * Real.pi) + 1) * (1 / γ^2) := by ring
  linarith

/-- Native majorant sequence for `S_rho`, combining the `1 / γ^2` RVM tail and finite low-height head. -/
noncomputable def S_rho_majorant_seq (gamma : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  let C_maj := (128 * |t|) / (2 * Real.pi) + 1
  (if 2 * |t| + 1 < |gamma n| then C_maj * (1 / (gamma n)^2) else 0) +
  (if |gamma n| ≤ 2 * |t| + 1 then S_rho_point_bound (gamma n) t else 0)

lemma S_rho_norm_le_majorant_seq (beta gamma : ℕ → ℝ) (t : ℝ) (n : ℕ) (y : ℝ) :
    ‖S_rho (beta n) (gamma n) y t‖ ≤ S_rho_majorant_seq gamma t n := by
  dsimp [S_rho_majorant_seq]
  by_cases h_tail : 2 * |t| + 1 < |gamma n|
  · have h_not_le : ¬(|gamma n| ≤ 2 * |t| + 1) := not_le.mpr h_tail
    rw [ite_eq_left h_tail, ite_eq_right h_not_le, add_zero]
    exact S_rho_tail_bound (beta n) (gamma n) y t h_tail
  · have h_head : |gamma n| ≤ 2 * |t| + 1 := not_lt.mp h_tail
    rw [ite_eq_right h_tail, ite_eq_left h_head, zero_add]
    exact S_rho_norm_le_point_bound (beta n) (gamma n) y t

lemma summable_S_rho_majorant_seq (gamma : ℕ → ℝ) (t : ℝ)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    Summable (S_rho_majorant_seq gamma t) := by
  let C_maj := (128 * |t|) / (2 * Real.pi) + 1
  have h_recip_sq : Summable (fun n => 1 / (gamma n)^2) :=
    eq_160_rvm_density gamma h_local h_rvm
  let M_tail := fun n => if 2 * |t| + 1 < |gamma n| then C_maj * (1 / (gamma n)^2) else 0
  let M_head := fun n => if |gamma n| ≤ 2 * |t| + 1 then S_rho_point_bound (gamma n) t else 0
  have h_summable_tail : Summable M_tail := by
    have h_scaled : Summable (fun n => C_maj * (1 / (gamma n)^2)) :=
      Summable.mul_left C_maj h_recip_sq
    apply Summable.of_nonneg_of_le
    · intro i; dsimp [M_tail]; split_ifs <;> positivity
    · intro i; dsimp [M_tail]; split_ifs <;> [exact le_rfl; positivity]
    · exact h_scaled
  have h_summable_head : Summable M_head := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (classical_finite_zeros_in_compact gamma h_local (2 * |t| + 1))
    intro i hi
    dsimp [Function.support, M_head] at hi
    by_contra h_not
    have h_gt : 2 * |t| + 1 < |gamma i| := lt_of_not_ge h_not
    have h_not_le : ¬(|gamma i| ≤ 2 * |t| + 1) := not_le_of_gt h_gt
    have h_zero : (if |gamma i| ≤ 2 * |t| + 1 then S_rho_point_bound (gamma i) t else 0) = 0 := by simp [h_not_le]
    exact hi h_zero
  exact Summable.add h_summable_tail h_summable_head

/-- Continuity of a single Cauchy kernel `K_rho` in the spatial variable `x` on all of `ℝ`. -/
lemma continuous_K_rho (β γ t : ℝ) : Continuous (fun x : ℝ => K_rho β γ x t) := by
  by_cases hγt : γ - t = 0
  · have h_zero : (fun x : ℝ => K_rho β γ x t) = fun _ => 0 := by
      ext x
      dsimp [K_rho]
      rw [hγt, zero_div, mul_zero]
    rw [h_zero]
    exact continuous_const
  · dsimp [K_rho]
    apply Continuous.mul continuous_const
    apply Continuous.div continuous_const
    · apply Continuous.add
      · exact (continuous_const.sub continuous_id).pow 2
      · exact continuous_const
    · intro x
      have h_pos : 0 < (γ - t)^2 := sq_pos_of_ne_zero hγt
      have h_nonneg : 0 ≤ (β - x)^2 := sq_nonneg (β - x)
      linarith

/-- Continuity of the symmetric quadruplet kernel `S_rho` in the spatial variable `x`. -/
lemma continuous_S_rho (β γ t : ℝ) : Continuous (fun x : ℝ => S_rho β γ x t) := by
  dsimp [S_rho]
  exact (((continuous_K_rho β γ t).add (continuous_K_rho (1 - β) γ t)).add
    (continuous_K_rho β (-γ) t)).add (continuous_K_rho (1 - β) (-γ) t)

/-- Continuity of the infinite Cauchy kernel series via Weierstrass M-test (`continuous_tsum`). -/
lemma continuous_tsum_S_rho (beta gamma : ℕ → ℝ) (t : ℝ)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    Continuous (fun x : ℝ => ∑' i, S_rho (beta i) (gamma i) x t) :=
  continuous_tsum (fun i => continuous_S_rho (beta i) (gamma i) t)
    (summable_S_rho_majorant_seq gamma t h_local h_rvm)
    (fun i x => S_rho_norm_le_majorant_seq beta gamma t i x)

/-- Native spatial integral of the Cauchy kernel series from the Dirichlet anchor `σ₀` to `σ`. -/
noncomputable def S_rho_tsum_integral (beta gamma : ℕ → ℝ) (σ₀ σ t : ℝ) : ℝ :=
  ∫ x in σ₀..σ, ∑' i, S_rho (beta i) (gamma i) x t

lemma S_rho_tsum_integral_self (beta gamma : ℕ → ℝ) (σ₀ t : ℝ) :
    S_rho_tsum_integral beta gamma σ₀ σ₀ t = 0 :=
  intervalIntegral.integral_same

lemma hasDerivAt_S_rho_tsum_integral (beta gamma : ℕ → ℝ) (σ₀ t u : ℝ)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    HasDerivAt (fun x => S_rho_tsum_integral beta gamma σ₀ x t)
      (∑' i, S_rho (beta i) (gamma i) u t) u := by
  have h_cont : Continuous (fun x : ℝ => ∑' i, S_rho (beta i) (gamma i) x t) :=
    continuous_tsum_S_rho beta gamma t h_local h_rvm
  exact intervalIntegral.integral_hasDerivAt_right
    (h_cont.intervalIntegrable σ₀ u)
    h_cont.stronglyMeasurable.stronglyMeasurableAtFilter
    h_cont.continuousAt

lemma deriv_S_rho_tsum_integral (beta gamma : ℕ → ℝ) (σ₀ t u : ℝ)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    deriv (fun x => S_rho_tsum_integral beta gamma σ₀ x t) u =
      ∑' i, S_rho (beta i) (gamma i) u t :=
  (hasDerivAt_S_rho_tsum_integral beta gamma σ₀ t u h_local h_rvm).deriv

lemma differentiableAt_S_rho_tsum_integral (beta gamma : ℕ → ℝ) (σ₀ t u : ℝ)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    DifferentiableAt ℝ (fun x => S_rho_tsum_integral beta gamma σ₀ x t) u :=
  (hasDerivAt_S_rho_tsum_integral beta gamma σ₀ t u h_local h_rvm).differentiableAt

/-- Unconditional bound at `σ = 2` for a Cauchy denominator term when `1 ≤ A^2`. -/
lemma abs_div_add_sq_le_one (A B : ℝ) (hA : 1 ≤ A^2) : |B / (A^2 + B^2)| ≤ 1 := by
  have h_B2 : 0 ≤ B^2 := sq_nonneg B
  have h_den_pos : 0 < A^2 + B^2 := by linarith
  rw [abs_div, abs_of_pos h_den_pos]
  rw [div_le_one h_den_pos]
  have h_sq : 0 ≤ (|B| - 1 / 2)^2 := sq_nonneg (|B| - 1 / 2)
  have h_abs_sq : |B|^2 = B^2 := sq_abs B
  linarith

lemma K_rho_at_two_abs_le (β γ t : ℝ) (hβ1 : β ≤ 1) :
    |K_rho β γ 2 t| ≤ 1 / (2 * Real.pi) := by
  dsimp [K_rho]
  have h_pi_pos : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
  have h_coeff_pos : 0 < 1 / (2 * Real.pi) := one_div_pos.mpr h_pi_pos
  rw [abs_mul, abs_of_pos h_coeff_pos]
  have hA : 1 ≤ (β - 2)^2 := by nlinarith
  have h_le := mul_le_mul_of_nonneg_left (abs_div_add_sq_le_one (β - 2) (γ - t) hA) (le_of_lt h_coeff_pos)
  linarith

lemma S_rho_at_two_norm_le_one (β γ t : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ‖S_rho β γ 2 t‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  dsimp [S_rho]
  have h1 := K_rho_at_two_abs_le β γ t hβ1
  have h2 := K_rho_at_two_abs_le (1 - β) γ t (by linarith)
  have h3 := K_rho_at_two_abs_le β (-γ) t hβ1
  have h4 := K_rho_at_two_abs_le (1 - β) (-γ) t (by linarith)
  have h_tri1 := abs_add_le (K_rho β γ 2 t + K_rho (1 - β) γ 2 t + K_rho β (-γ) 2 t) (K_rho (1 - β) (-γ) 2 t)
  have h_tri2 := abs_add_le (K_rho β γ 2 t + K_rho (1 - β) γ 2 t) (K_rho β (-γ) 2 t)
  have h_tri3 := abs_add_le (K_rho β γ 2 t) (K_rho (1 - β) γ 2 t)
  have h_pi_pos : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
  have h_four : 4 * (1 / (2 * Real.pi)) ≤ 1 := by
    have h_le : (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h_div : 4 / (2 * Real.pi) ≤ 1 := (div_le_one h_pi_pos).mpr h_le
    linarith [show 4 * (1 / (2 * Real.pi)) = 4 / (2 * Real.pi) by ring]
  linarith

/-- Uniform in-`t` (for `|t - γ₀| ≤ 1`) majorant sequence at the anchor `σ = 2`. -/
noncomputable def S_rho_anchor_majorant_seq (gamma : ℕ → ℝ) (γ₀ : ℝ) (n : ℕ) : ℝ :=
  let T₀ := |γ₀| + 1
  let C_maj := (128 * T₀) / (2 * Real.pi) + 1
  (if 2 * T₀ + 1 < |gamma n| then C_maj * (1 / (gamma n)^2) else 0) +
  (if |gamma n| ≤ 2 * T₀ + 1 then 1 else 0)

lemma S_rho_at_two_norm_le_anchor_majorant (beta gamma : ℕ → ℝ) (γ₀ t : ℝ)
    (h_beta : ∀ n, 0 ≤ beta n ∧ beta n ≤ 1) (ht : |t - γ₀| ≤ 1) (n : ℕ) :
    ‖S_rho (beta n) (gamma n) 2 t‖ ≤ S_rho_anchor_majorant_seq gamma γ₀ n := by
  dsimp [S_rho_anchor_majorant_seq]
  have ht_abs : |t| ≤ |γ₀| + 1 := by
    have h_tri : |t| ≤ |t - γ₀| + |γ₀| := by
      have h := abs_sub_le t γ₀ 0
      simpa only [sub_zero] using h
    linarith
  by_cases h_tail : 2 * (|γ₀| + 1) + 1 < |gamma n|
  · have h_not_le : ¬(|gamma n| ≤ 2 * (|γ₀| + 1) + 1) := not_le.mpr h_tail
    rw [ite_eq_left h_tail, ite_eq_right h_not_le, add_zero]
    have h_tail_t : 2 * |t| + 1 < |gamma n| := by linarith
    have h_bound_t := S_rho_tail_bound (beta n) (gamma n) 2 t h_tail_t
    have h_pi_pos : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
    have h_cmaj_le : (128 * |t|) / (2 * Real.pi) + 1 ≤ (128 * (|γ₀| + 1)) / (2 * Real.pi) + 1 := by
      have h_num : 128 * |t| ≤ 128 * (|γ₀| + 1) := by linarith
      have h_div := div_le_div_of_nonneg_right h_num (le_of_lt h_pi_pos)
      linarith
    have h_inv_nonneg : 0 ≤ 1 / (gamma n)^2 := by positivity
    exact le_trans h_bound_t (mul_le_mul_of_nonneg_right h_cmaj_le h_inv_nonneg)
  · have h_head : |gamma n| ≤ 2 * (|γ₀| + 1) + 1 := not_lt.mp h_tail
    rw [ite_eq_right h_tail, ite_eq_left h_head, zero_add]
    exact S_rho_at_two_norm_le_one (beta n) (gamma n) t (h_beta n).1 (h_beta n).2

lemma summable_S_rho_anchor_majorant_seq (gamma : ℕ → ℝ) (γ₀ : ℝ)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    Summable (S_rho_anchor_majorant_seq gamma γ₀) := by
  let T₀ := |γ₀| + 1
  let C_maj := (128 * T₀) / (2 * Real.pi) + 1
  have h_recip_sq : Summable (fun n => 1 / (gamma n)^2) :=
    eq_160_rvm_density gamma h_local h_rvm
  let M_tail := fun n => if 2 * T₀ + 1 < |gamma n| then C_maj * (1 / (gamma n)^2) else 0
  let M_head := fun n => if |gamma n| ≤ 2 * T₀ + 1 then (1 : ℝ) else 0
  have h_summable_tail : Summable M_tail := by
    have h_scaled : Summable (fun n => C_maj * (1 / (gamma n)^2)) :=
      Summable.mul_left C_maj h_recip_sq
    apply Summable.of_nonneg_of_le
    · intro i; dsimp [M_tail]; split_ifs <;> positivity
    · intro i; dsimp [M_tail]; split_ifs <;> [exact le_rfl; positivity]
    · exact h_scaled
  have h_summable_head : Summable M_head := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (classical_finite_zeros_in_compact gamma h_local (2 * T₀ + 1))
    intro i hi
    dsimp [Function.support, M_head] at hi
    by_contra h_not
    have h_gt : 2 * T₀ + 1 < |gamma i| := lt_of_not_ge h_not
    have h_not_le : ¬(|gamma i| ≤ 2 * T₀ + 1) := not_le_of_gt h_gt
    have h_zero : (if |gamma i| ≤ 2 * T₀ + 1 then (1 : ℝ) else 0) = 0 := by simp [h_not_le]
    exact hi h_zero
  exact Summable.add h_summable_tail h_summable_head

lemma abs_tsum_S_rho_at_two_le (beta gamma : ℕ → ℝ) (γ₀ t : ℝ)
    (h_beta : ∀ n, 0 ≤ beta n ∧ beta n ≤ 1)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma)
    (ht : |t - γ₀| ≤ 1) :
    |∑' i, S_rho (beta i) (gamma i) 2 t| ≤ ∑' i, S_rho_anchor_majorant_seq gamma γ₀ i := by
  rw [← Real.norm_eq_abs]
  have h_sum_maj := summable_S_rho_anchor_majorant_seq gamma γ₀ h_local h_rvm
  have h_le : ∀ n, ‖S_rho (beta n) (gamma n) 2 t‖ ≤ S_rho_anchor_majorant_seq gamma γ₀ n :=
    S_rho_at_two_norm_le_anchor_majorant beta gamma γ₀ t h_beta ht
  have h_sum_norm : Summable (fun i => ‖S_rho (beta i) (gamma i) 2 t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_le h_sum_maj
  exact le_trans (norm_tsum_le_tsum_norm h_sum_norm) (hasSum_le h_le h_sum_norm.hasSum h_sum_maj.hasSum)

/-- At the Dirichlet anchor `σ = 2`, `β - 2 < 0` for all `β ≤ 1`, so `A_rho` lies on a single smooth arctan branch and is continuous in `t`. -/
lemma continuous_A_rho_at_two (β γ : ℝ) (hβ1 : β ≤ 1) :
    Continuous (fun t : ℝ => A_rho β γ 2 t) := by
  have h_neg : β - 2 < 0 := by linarith
  have h_not_pos : ¬(β - 2 > 0) := not_lt.mpr (le_of_lt h_neg)
  have h_eq : (fun t : ℝ => A_rho β γ 2 t) =
      fun t : ℝ => Real.arctan ((γ - t) / (β - 2)) / (2 * Real.pi) + 1 / 2 := by
    ext t
    dsimp [A_rho, pspace_arctan]
    rw [ite_eq_right h_not_pos, ite_eq_left h_neg]
  rw [h_eq]
  apply Continuous.add _ continuous_const
  apply Continuous.div _ continuous_const (fun _ => ne_of_gt (by linarith [Real.pi_pos]))
  apply Real.continuous_arctan.comp
  exact Continuous.div (continuous_const.sub continuous_id) continuous_const (fun _ => ne_of_lt h_neg)

/-- `B_rho` is linear in `t` and therefore continuous in `t` on all of `ℝ`. -/
lemma continuous_B_rho_in_t (β γ σ : ℝ) :
    Continuous (fun t : ℝ => B_rho β γ σ t) := by
  have h_eq : (fun t : ℝ => B_rho β γ σ t) =
      fun t : ℝ => (1 / (2 * Real.pi)) * (1 / (β^2 + γ^2)) * (t * β - σ * γ) := by
    ext t
    exact B_rho_explicit β γ σ t
  rw [h_eq]
  exact Continuous.mul continuous_const ((continuous_id.mul continuous_const).sub continuous_const)

/-- At `σ = 2`, the decomposed phase `psi_rho` is continuous in `t` for all `β ≤ 1`. -/
lemma continuous_psi_rho_at_two (β γ : ℝ) (hβ1 : β ≤ 1) :
    Continuous (fun t : ℝ => psi_rho β γ 2 t) := by
  dsimp [psi_rho]
  exact ((continuous_A_rho_at_two β γ hβ1).add (continuous_B_rho_in_t β γ 2)).add continuous_const

/-- At `σ = 2`, the symmetric quadruplet phase `psi_quad_sum` is continuous in `t` for all `0 ≤ β ≤ 1`. -/
lemma continuous_psi_quad_sum_at_two (β γ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Continuous (fun t : ℝ => psi_quad_sum β γ 2 t) := by
  dsimp [psi_quad_sum]
  have h1mb : 1 - β ≤ 1 := by linarith
  exact (((continuous_psi_rho_at_two β γ hβ1).add
    (continuous_psi_rho_at_two (1 - β) γ h1mb)).add
    (continuous_psi_rho_at_two β (-γ) hβ1)).add
    (continuous_psi_rho_at_two (1 - β) (-γ) h1mb)

/-- The indicator series of `psi_quad_sum` at `γ₀` reduces to a finite sum over `{j | |gamma j| ≤ |γ₀|}`,
and is therefore continuous in `t` at `σ = 2`. -/
lemma continuous_target_anchor_sum (beta gamma : ℕ → ℝ) (γ₀ : ℝ)
    (h_beta : ∀ n, 0 ≤ beta n ∧ beta n ≤ 1)
    (h_local : GammaLocallyFinite gamma) :
    Continuous (fun t : ℝ => ∑' j, if gamma j = γ₀ then psi_quad_sum (beta j) (gamma j) 2 t else 0) := by
  let S := (h_local |γ₀|).toFinset
  have h_eq : (fun t : ℝ => ∑' j, if gamma j = γ₀ then psi_quad_sum (beta j) (gamma j) 2 t else 0) =
      fun t : ℝ => ∑ j ∈ S, if gamma j = γ₀ then psi_quad_sum (beta j) (gamma j) 2 t else 0 := by
    ext t
    apply tsum_eq_sum
    intro j hj
    have hj_not : ¬(|gamma j| ≤ |γ₀|) := by
      intro h_le
      exact hj ((Set.Finite.mem_toFinset (h_local |γ₀|)).mpr h_le)
    have h_ne : gamma j ≠ γ₀ := by
      intro h_eq_g
      apply hj_not
      rw [h_eq_g]
    exact ite_eq_right h_ne
  rw [h_eq]
  apply continuous_finsetSum
  intro j _
  by_cases h_g : gamma j = γ₀
  · have h_term : (fun t : ℝ => if gamma j = γ₀ then psi_quad_sum (beta j) (gamma j) 2 t else 0) =
        fun t : ℝ => psi_quad_sum (beta j) (gamma j) 2 t := by
      ext t
      exact ite_eq_left h_g
    rw [h_term]
    exact continuous_psi_quad_sum_at_two (beta j) (gamma j) (h_beta j).1 (h_beta j).2
  · have h_term : (fun t : ℝ => if gamma j = γ₀ then psi_quad_sum (beta j) (gamma j) 2 t else 0) =
        fun _ : ℝ => 0 := by
      ext t
      exact ite_eq_right h_g
    rw [h_term]
    exact continuous_const

/-- Summability of the shifted Cauchy-curvature denominator `1 / (1 + (gamma j - γ₀)^2)`
derived natively from the Riemann-von Mangoldt density bound (`eq_160_rvm_density`)
and local finiteness (`GammaLocallyFinite`). -/
lemma summable_inv_one_add_sub_sq (gamma : ℕ → ℝ) (γ₀ : ℝ)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma) :
    Summable (fun j : ℕ => 1 / (1 + (gamma j - γ₀)^2)) := by
  let T₀ := 2 * |γ₀| + 1
  have h_recip_sq : Summable (fun n => 1 / (gamma n)^2) :=
    eq_160_rvm_density gamma h_local h_rvm
  let M_tail := fun j => if T₀ < |gamma j| then 4 * (1 / (gamma j)^2) else 0
  let M_head := fun j => if |gamma j| ≤ T₀ then (1 : ℝ) else 0
  have h_summable_tail : Summable M_tail := by
    have h_scaled : Summable (fun n => 4 * (1 / (gamma n)^2)) :=
      Summable.mul_left 4 h_recip_sq
    apply Summable.of_nonneg_of_le
    · intro i; dsimp [M_tail]; split_ifs <;> positivity
    · intro i; dsimp [M_tail]; split_ifs <;> [exact le_rfl; positivity]
    · exact h_scaled
  have h_summable_head : Summable M_head := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (classical_finite_zeros_in_compact gamma h_local T₀)
    intro i hi
    dsimp [Function.support, M_head] at hi
    by_contra h_not
    have h_gt : T₀ < |gamma i| := lt_of_not_ge h_not
    have h_not_le : ¬(|gamma i| ≤ T₀) := not_le_of_gt h_gt
    have h_zero : (if |gamma i| ≤ T₀ then (1 : ℝ) else 0) = 0 := by simp [h_not_le]
    exact hi h_zero
  have h_sum_maj : Summable (fun j => M_tail j + M_head j) :=
    Summable.add h_summable_tail h_summable_head
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) h_sum_maj
  dsimp [M_tail, M_head]
  by_cases h_tail : T₀ < |gamma j|
  · have h_not_le : ¬(|gamma j| ≤ T₀) := not_le.mpr h_tail
    rw [ite_eq_left h_tail, ite_eq_right h_not_le, add_zero]
    have h_tri : |gamma j| ≤ |gamma j - γ₀| + |γ₀| := by
      have h := abs_sub_le (gamma j) γ₀ 0
      simpa only [sub_zero] using h
    have h_gt_twice : |gamma j| < 2 * |gamma j - γ₀| := by
      dsimp [T₀] at h_tail
      linarith [abs_nonneg γ₀]
    have hγ_pos : 0 < |gamma j| := by
      dsimp [T₀] at h_tail
      linarith [abs_nonneg γ₀]
    have hγ2_pos : 0 < (gamma j)^2 := by
      have h_sq : |gamma j|^2 = (gamma j)^2 := sq_abs (gamma j)
      nlinarith
    have h_sq_le : (gamma j)^2 ≤ 4 * (gamma j - γ₀)^2 := by
      have ha1 : |gamma j|^2 = (gamma j)^2 := sq_abs (gamma j)
      have ha2 : |gamma j - γ₀|^2 = (gamma j - γ₀)^2 := sq_abs (gamma j - γ₀)
      nlinarith [abs_nonneg (gamma j - γ₀)]
    have h_div : 1 / (1 + (gamma j - γ₀)^2) ≤ 4 / (gamma j)^2 :=
      (div_le_div_iff₀ (by positivity) hγ2_pos).mpr (by linarith)
    linarith [show 4 / (gamma j)^2 = 4 * (1 / (gamma j)^2) by ring]
  · have h_head : |gamma j| ≤ T₀ := not_lt.mp h_tail
    rw [ite_eq_right h_tail, ite_eq_left h_head, zero_add]
    rw [div_le_one (by positivity)]
    linarith [sq_nonneg (gamma j - γ₀)]

/-- Weierstrass M-Test for the background curvature series on `{t : ℝ | |t - γ₀| < d}`:
Consumes the tail majorant `(4 * C_K) / (1 + (gamma j - γ₀)^2)` and proves uniform convergence
of the background mixed-derivative series via Mathlib's `tendstoUniformlyOn_tsum`. -/
lemma weierstrass_M_test_background_curv
    (beta gamma : ℕ → ℝ) (σ₀ γ₀ C_K d : ℝ)
    (h_CK_pos : 0 < C_K)
    (h_local : GammaLocallyFinite gamma) (h_rvm : HasRVMCount gamma)
    (h_maj : ∀ j : ℕ, gamma j ≠ γ₀ → ∀ t : ℝ, |t - γ₀| < d →
      |deriv (fun u : ℝ => deriv (fun x : ℝ => psi_rho (beta j) (gamma j) x u) σ₀) t| ≤
        (4 * C_K) / (1 + (gamma j - γ₀)^2)) :
    TendstoUniformlyOn
      (fun (k : Finset ℕ) (t : ℝ) =>
        ∑ j ∈ k, if gamma j = γ₀ then (0 : ℝ)
          else deriv (fun u : ℝ => deriv (fun x : ℝ => psi_rho (beta j) (gamma j) x u) σ₀) t)
      (fun (t : ℝ) =>
        ∑' j, if gamma j = γ₀ then (0 : ℝ)
          else deriv (fun u : ℝ => deriv (fun x : ℝ => psi_rho (beta j) (gamma j) x u) σ₀) t)
      Filter.atTop {t : ℝ | |t - γ₀| < d} := by
  have h_sum_base := summable_inv_one_add_sub_sq gamma γ₀ h_local h_rvm
  have h_sum_maj : Summable (fun j : ℕ => (4 * C_K) / (1 + (gamma j - γ₀)^2)) := by
    have h_eq : (fun j : ℕ => (4 * C_K) / (1 + (gamma j - γ₀)^2)) =
        fun j : ℕ => (4 * C_K) * (1 / (1 + (gamma j - γ₀)^2)) := by
      ext j; ring
    rw [h_eq]
    exact h_sum_base.mul_left (4 * C_K)
  apply tendstoUniformlyOn_tsum h_sum_maj
  intro j t ht
  rw [Real.norm_eq_abs]
  by_cases h_eq : gamma j = γ₀
  · rw [ite_eq_left h_eq, abs_zero]
    positivity
  · rw [ite_eq_right h_eq]
    exact h_maj j h_eq t ht

/-- On the critical axis `σ = 1 / 2`, any off-line zero pair (`β ≠ 1 / 2`) has opposite
horizontal displacements `1 - β - 1 / 2 = -(β - 1 / 2)`, so their arctangent phases
cancel identically and sum to the constant `3 / 2` for all `t`. -/
lemma A_rho_paired_critical_axis_const (β γ t : ℝ) (h_off : β ≠ 1 / 2) :
    A_rho β γ (1 / 2) t + A_rho (1 - β) γ (1 / 2) t = 3 / 2 := by
  dsimp [A_rho, pspace_arctan]
  have h_opp : 1 - β - 1 / 2 = -(β - 1 / 2) := by ring
  have h_div_neg : (γ - t) / (1 - β - 1 / 2) = -((γ - t) / (β - 1 / 2)) := by
    rw [h_opp, div_neg]
  rcases lt_trichotomy (β - 1 / 2) 0 with h_neg | h_zero | h_pos
  · have h1_not_pos : ¬(β - 1 / 2 > 0) := not_lt.mpr (le_of_lt h_neg)
    have h2_pos : 1 - β - 1 / 2 > 0 := by linarith
    rw [ite_eq_right h1_not_pos, ite_eq_left h_neg, ite_eq_left h2_pos]
    rw [h_div_neg, Real.arctan_neg]
    ring
  · exfalso
    apply h_off
    linarith
  · have h2_neg : 1 - β - 1 / 2 < 0 := by linarith
    have h2_not_pos : ¬(1 - β - 1 / 2 > 0) := not_lt.mpr (le_of_lt h2_neg)
    rw [ite_eq_left h_pos, ite_eq_right h2_not_pos, ite_eq_left h2_neg]
    rw [h_div_neg, Real.arctan_neg]
    ring

/-- For any off-line zero (`β ≠ 1 / 2`), the full quadruplet arctangent phase on the
critical axis `σ = 1 / 2` is identically `3` for all `t`, so its jump across any `t₁, t₂`
vanishes identically (`= 0`). -/
lemma A_rho_quad_critical_axis_diff_zero (β γ t₁ t₂ : ℝ) (h_off : β ≠ 1 / 2) :
    (A_rho β γ (1 / 2) t₁ + A_rho (1 - β) γ (1 / 2) t₁ +
     A_rho β (-γ) (1 / 2) t₁ + A_rho (1 - β) (-γ) (1 / 2) t₁) -
    (A_rho β γ (1 / 2) t₂ + A_rho (1 - β) γ (1 / 2) t₂ +
     A_rho β (-γ) (1 / 2) t₂ + A_rho (1 - β) (-γ) (1 / 2) t₂) = 0 := by
  have h1 := A_rho_paired_critical_axis_const β γ t₁ h_off
  have h2 := A_rho_paired_critical_axis_const β (-γ) t₁ h_off
  have h3 := A_rho_paired_critical_axis_const β γ t₂ h_off
  have h4 := A_rho_paired_critical_axis_const β (-γ) t₂ h_off
  linarith

/-- Lemma 4.2.4 (Uniform convergence of zero kernels).
Structurally demands 3.3 and 3.4.2 to establish that the infinite sum of derivatives
uniformly converges by equating it to the pure Cauchy kernel sum `S_rho` and bounding it. -/
lemma lemma_4_2_4_uni_conv_kernel
    (I : Set ℝ) (t : ℝ) (beta gamma : ℕ → ℝ) (M : ℕ → ℝ)
    (h_neq : ∀ n σ, σ ∈ I → σ ≠ beta n ∧ σ ≠ 1 - beta n)
    (h_summable : Summable M)
    (h_bound : ∀ (n : ℕ) (σ : ℝ), σ ∈ I → norm (S_rho (beta n) (gamma n) σ t) ≤ M n) :
    TendstoUniformlyOn (fun (k : Finset ℕ) σ => ∑ i ∈ k, quad_sum (fun b g => deriv (fun x => psi_rho b g x t) σ) (beta i) (gamma i))
    (fun σ => ∑' i, quad_sum (fun b g => deriv (fun x => psi_rho b g x t) σ) (beta i) (gamma i)) Filter.atTop I := by

  -- 1. Establish that quad_sum of derivatives reduces to S_rho explicitly via Lemma 3.4.2
  have h_eq : ∀ n σ, σ ∈ I → quad_sum (fun b g => deriv (fun x => psi_rho b g x t) σ) (beta n) (gamma n) = S_rho (beta n) (gamma n) σ t := by
    intro n σ h_in
    have h_n1 := (h_neq n σ h_in).1
    have h_n2 := (h_neq n σ h_in).2

    -- Explicitly invoke Lemma 3.4.2 by name to execute offset cancellation and kernel reduction
    rw [lemma_3_4_2_global_phase_reduction (beta n) (gamma n) σ t h_n1 h_n2]

    -- Align `quad_sum K_rho` with `S_rho`
    dsimp [quad_sum, S_rho, K_rho]
    ring

  -- 2. Establish uniform convergence for S_rho via the Weierstrass M-Test
  have h_uni_S : TendstoUniformlyOn (fun k σ => ∑ i ∈ k, S_rho (beta i) (gamma i) σ t)
    (fun σ => ∑' i, S_rho (beta i) (gamma i) σ t) Filter.atTop I :=
    tendstoUniformlyOn_tsum h_summable h_bound

  -- 3. Transfer both the finite sums and the limit.
  apply TendstoUniformlyOn.congr_right
  · apply TendstoUniformlyOn.congr h_uni_S
    filter_upwards with k
    intro σ hσ
    apply Finset.sum_congr rfl
    intro n hn
    exact (h_eq n σ hσ).symm
  · intro σ hσ
    apply tsum_congr
    intro n
    exact (h_eq n σ hσ).symm


-- Section 4.2.5: Linearity of the phase derivative


/-- Lemma 4.2.5 (Term-by-term differentiation of the phase series).
Structurally consumes 4.2.2, 4.2.3, and 4.2.4 as mandated, driving the infinite derivative swap
directly from `xi_P_phase` (Equation 176) without dummy `Phi_D` functions. -/
lemma lemma_4_2_5_linearity_of_phase_derivative
    (s_state rho_state : ℝ → ℝ → PSpace)
    (I : Set ℝ)
    (theta Phi : ℝ → ℝ) (beta gamma : ℕ → ℝ) (M : ℕ → ℝ) (σ t : ℝ)
    (h_σ_in : σ ∈ I)
    (h_beta_bounds : ∀ n, 0 ≤ beta n ∧ beta n ≤ 1)
    (h_local : GammaLocallyFinite gamma)
    (h_rvm : HasRVMCount gamma)
    (h_s : ∀ σ t, proj (s_state σ t) = Complex.mk σ t)
    (h_rho : ∀ b g, proj (rho_state b g) = rho b g)
    (h_approx_eval : ∀ β γ σ t, proj (eq_156_P_rho_approx s_state rho_state β γ σ t) =
      1 - ((proj (s_state σ t))^2 / 2) * (((proj (rho_state β γ))⁻¹)^2 + ((proj (rho_state β (-γ)))⁻¹)^2 + ((proj (rho_state (1 - β) γ))⁻¹)^2 + ((proj (rho_state (1 - β) (-γ)))⁻¹)^2))
    (h_rem_bound : ∀ R > 0, ∃ C > 0, ∃ T > 1, ∀ β γ σ t : ℝ, ‖proj (s_state σ t)‖ ≤ R → 0 ≤ β → β ≤ 1 → |γ| > T →
      ∀ (h1 : 0 < M_rho_real β γ σ t) (h2 : 0 < M_rho_real (1 - β) γ σ t)
        (h3 : 0 < M_rho_real β (-γ) σ t) (h4 : 0 < M_rho_real (1 - β) (-γ) σ t),
      ‖proj (eq_156_P_rho_rem β γ σ t s_state rho_state h1 h2 h3 h4)‖ ≤ C * ‖proj (s_state σ t)‖^3 / |γ|^3)
    (h_phase_bound : ∀ k y, P_rho_dev_mag (beta k) (gamma k) (s_state y t) ≤ P_rho_taylor_bound s_state rho_state (beta k) (gamma k) (s_state y t))
    (h_neq : ∀ n y, y ∈ I → y ≠ beta n ∧ y ≠ 1 - beta n)
    (h_Phi_const : ∀ y, deriv Phi y = 0)
    (h_diff_Phi : DifferentiableAt ℝ Phi σ)
    (h_summable_M : Summable M)
    (h_bound : ∀ n y, norm (S_rho (beta n) (gamma n) y t) ≤ M n)
    (h_deriv_swap : deriv (fun x => theta x - Phi x) σ = ∑' i, S_rho (beta i) (gamma i) σ t) :
    deriv theta σ = ∑' i, S_rho (beta i) (gamma i) σ t := by

  -- 1. Load-bearingly consume Lemma 4.2.2 (Pointwise convergence of xi_P_phase)
  let Phi_H_2d : ℝ → ℝ → ℝ := fun x _ => Phi x
  have h_4_2_2 := lemma_4_2_2_pointwise_convergence
    s_state rho_state beta gamma Phi_H_2d
    h_beta_bounds h_local h_rvm t h_s h_rho h_approx_eval h_rem_bound h_phase_bound

  have h_base_conv_all := h_4_2_2.1
  have _h_step1_identity := h_4_2_2.2 σ
  have _h_base_conv : Summable (fun i => P_rho_dev_mag (beta i) (gamma i) (s_state σ t)) := h_base_conv_all σ

  -- 2. Load-bearingly consume Lemma 4.2.4 (Uniform convergence on I)
  have h_uni_conv := lemma_4_2_4_uni_conv_kernel I t beta gamma M
    h_neq h_summable_M (fun n y _ => h_bound n y)

  have h_tendsto := TendstoUniformlyOn.tendsto_at h_uni_conv h_σ_in

  have _h_deriv_summable : Summable (fun i => quad_sum (fun b g => deriv (fun x => psi_rho b g x t) σ) (beta i) (gamma i)) :=
    ⟨_, h_tendsto⟩

  -- 3. Load-bearingly consume Lemma 4.2.3 (Termwise differentiability of the 4.2.2 summand on I)
  have _h_step3_term_deriv : ∀ i,
      HasDerivAt (fun x => theta_n 2 (gamma i - t) + psi_quad_sum (beta i) (gamma i) x t)
        (S_rho (beta i) (gamma i) σ t) σ := by
    intro i
    have h_n1 := (h_neq i σ h_σ_in).1
    have h_n2 := (h_neq i σ h_σ_in).2
    have hd_const : HasDerivAt (fun _ : ℝ => theta_n 2 (gamma i - t)) 0 σ :=
      hasDerivAt_const σ (theta_n 2 (gamma i - t))
    have hd_quad : HasDerivAt (fun x => psi_quad_sum (beta i) (gamma i) x t) (S_rho (beta i) (gamma i) σ t) σ :=
      hasDerivAt_psi_quad_sum (beta i) (gamma i) σ t h_n1 h_n2
    have hd_sum := hd_const.add hd_quad
    rwa [zero_add] at hd_sum

  -- 4. Combine with the background phase Phi to evaluate deriv theta σ
  have hd_Phi : HasDerivAt Phi 0 σ := by
    have heq : deriv Phi σ = 0 := h_Phi_const σ
    rw [← heq]
    exact DifferentiableAt.hasDerivAt h_diff_Phi

  have h_theta_eq_sum : ((fun x => theta x - Phi x) + Phi) = theta := by
    ext x
    change theta x - Phi x + Phi x = theta x
    ring

  by_cases h_diff_sub : DifferentiableAt ℝ (fun x => theta x - Phi x) σ
  · have hd_sub : HasDerivAt (fun x => theta x - Phi x) (∑' i, S_rho (beta i) (gamma i) σ t) σ := by
      rw [← h_deriv_swap]
      exact h_diff_sub.hasDerivAt
    have hd_tot := HasDerivAt.add hd_sub hd_Phi
    rw [add_zero, h_theta_eq_sum] at hd_tot
    exact hd_tot.deriv
  · have h_not_diff_theta : ¬ DifferentiableAt ℝ theta σ := by
      intro h_dt
      exact h_diff_sub (h_dt.sub h_diff_Phi)
    rw [deriv_zero_of_not_differentiableAt h_not_diff_theta]
    rw [← h_deriv_swap]
    exact (deriv_zero_of_not_differentiableAt h_diff_sub).symm


end TainoPolar
