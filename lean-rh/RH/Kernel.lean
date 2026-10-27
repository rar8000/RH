/-
Copyright (c) 2026 Richard Andrew Rodriguez.
Released under the MIT license.
Manuscript DOI: 10.5281/zenodo.23692735
-/
import Mathlib
import RH.Axioms
import RH.Mappings

open Complex Filter Topology Set

namespace TainoPolar


-- =========================================================================
-- Calculus and Algebraic Reduction Proofs
-- =========================================================================

variable (β γ σ t : ℝ)

/-- Verifying the Cartesian expansion of the (1 - s/ρ) fraction (Equation 101) -/
lemma one_sub_s_div_rho (β γ σ t : ℝ) (h_rho_nz : rho β γ ≠ 0) :
    1 - (s_val σ t) / (rho β γ) = (Complex.mk (β - σ) (γ - t)) / (rho β γ) := by
  have h1 : (1 : ℂ) = (rho β γ) / (rho β γ) := (div_self h_rho_nz).symm
  rw [h1, ← sub_div]
  have h_num : rho β γ - s_val σ t = Complex.mk (β - σ) (γ - t) := by
    apply Complex.ext <;> simp [rho, s_val]
  rw [h_num]

/-- Algebraic reduction of the complex quotient (Equations 111, 112, 113) -/
lemma im_neg_inv_complex (X Y : ℝ) :
    (-1 / Complex.mk X Y).im = Y / (X^2 + Y^2) := by
  have h1 : (-1 : ℂ) / Complex.mk X Y = - (Complex.mk X Y)⁻¹ := by
    calc (-1 : ℂ) / Complex.mk X Y
      _ = (-1 : ℂ) * (Complex.mk X Y)⁻¹ := div_eq_mul_inv _ _
      _ = - (Complex.mk X Y)⁻¹ := neg_one_mul _
  rw [h1, Complex.neg_im, Complex.inv_im]
  dsimp [Complex.normSq]
  ring

/-- Mapping the quotient reduction strictly to our β, γ, σ, t coordinates -/
lemma im_neg_inv_A_rho (β γ σ t : ℝ) :
    (-1 / Complex.mk (β - σ) (γ - t)).im = (γ - t) / ((β - σ)^2 + (γ - t)^2) := by
  exact im_neg_inv_complex (β - σ) (γ - t)

/-- Expanding the complex quotient into real and imaginary parts (Equation 116) -/
lemma s_div_rho_im (β γ σ t : ℝ) :
    ((s_val σ t) / (rho β γ)).im = (t * β - σ * γ) / (β^2 + γ^2) := by
  dsimp [s_val, rho]
  rw [Complex.div_im]
  dsimp [Complex.normSq]
  ring

/-- Algebraic resolution of B_rho (Equations 117, 118) -/
lemma B_rho_explicit (β γ σ t : ℝ) :
    B_rho β γ σ t = (1 / (2 * Real.pi)) * (1 / (β^2 + γ^2)) * (t * β - σ * γ) := by
  dsimp [B_rho]
  rw [s_div_rho_im β γ σ t]
  ring

/-- Evaluating the partial differential in isolation (Equation 120) -/
lemma deriv_linear_term (β γ t σ : ℝ) :
    deriv (fun x => t * β - x * γ) σ = -γ := by
  simp

/-- Differentiating the full linear phase component (Equations 119, 122) -/
lemma deriv_B_rho_full (β γ σ t : ℝ) :
    deriv (fun x => B_rho β γ x t) σ = -(1 / (2 * Real.pi)) * (γ / (β^2 + γ^2)) := by
  have h_explicit : (fun x => B_rho β γ x t) = fun x => ((1 / (2 * Real.pi)) * (1 / (β^2 + γ^2))) * (t * β - x * γ) := by
    ext x
    exact B_rho_explicit β γ x t
  rw [h_explicit]
  simp
  ring

/-- Differentiability and derivative of A_rho (Equation 114). -/
lemma deriv_A_rho_full (β γ σ t : ℝ) (h_sigma : σ ≠ β) :
    deriv (fun x => A_rho β γ x t) σ = (1 / (2 * Real.pi)) * ((γ - t) / ((β - σ)^2 + (γ - t)^2)) := by
  dsimp [A_rho]
  -- Since h_sigma : σ ≠ β, we split strictly on the sign of the real Cartesian component β - σ
  rcases lt_trichotomy (β - σ) 0 with h_neg | h_zero | h_pos
  · -- Case: β - σ < 0 (i.e. x < 0 in pspace_arctan)
    have h_nhds : ∀ᶠ x in 𝓝 σ, β - x < 0 :=
      (continuous_const.sub continuous_id).continuousAt.eventually_lt tendsto_const_nhds h_neg
    have h_evt_eq : (fun x : ℝ => pspace_arctan (γ - t) (β - x)) =ᶠ[𝓝 σ] (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1 / 2) := by
      filter_upwards [h_nhds] with x hx
      dsimp [pspace_arctan]
      have h_not_pos : ¬(β - x > 0) := not_lt.mpr (le_of_lt hx)
      simp [hx, h_not_pos]

    have h_deriv_eq : deriv (fun x : ℝ => pspace_arctan (γ - t) (β - x)) σ = deriv (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1 / 2) σ :=
      Filter.EventuallyEq.deriv_eq h_evt_eq
    rw [h_deriv_eq]

    -- Inner derivative of (γ - t) / (β - x)
    have hd_num : HasDerivAt (fun _ : ℝ => γ - t) 0 σ := hasDerivAt_const _ _
    have hd_den : HasDerivAt (fun x : ℝ => β - x) (-1) σ := (hasDerivAt_id σ).const_sub β
    have hd_div : HasDerivAt (fun x : ℝ => (γ - t) / (β - x)) ((0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2) σ :=
      hd_num.div hd_den (ne_of_lt h_neg)
    have hd_div_simp : HasDerivAt (fun x : ℝ => (γ - t) / (β - x)) ((γ - t) / (β - σ)^2) σ := by
      have h_alg : (0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2 = (γ - t) / (β - σ)^2 := by ring
      exact h_alg ▸ hd_div

    -- Outer composition with Arctangent via explicit substitution
    have h_comp : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x))) ((1 / (1 + ((γ - t) / (β - σ))^2)) * ((γ - t) / (β - σ)^2)) σ := by
      have h_raw := HasDerivAt.comp σ (Real.hasDerivAt_arctan ((γ - t) / (β - σ))) hd_div_simp
      have h_eq : (Real.arctan ∘ fun x : ℝ => (γ - t) / (β - x)) = fun x : ℝ => Real.arctan ((γ - t) / (β - x)) := rfl
      exact h_eq ▸ h_raw

    -- Algebraic reduction of the Cartesian kernel
    have h_simp : (1 / (1 + ((γ - t) / (β - σ))^2)) * ((γ - t) / (β - σ)^2) = (γ - t) / ((β - σ)^2 + (γ - t)^2) := by
      have hX : (β - σ)^2 ≠ 0 := pow_ne_zero 2 (ne_of_lt h_neg)
      have hd1 : 1 + ((γ - t) / (β - σ))^2 = ((β - σ)^2 + (γ - t)^2) / (β - σ)^2 := by
        rw [div_pow, add_div_eq_mul_add_div 1 ((γ - t)^2) hX, one_mul]
      rw [hd1, one_div, inv_div]
      calc (β - σ)^2 / ((β - σ)^2 + (γ - t)^2) * ((γ - t) / (β - σ)^2)
        _ = ((β - σ)^2 / (β - σ)^2) * ((γ - t) / ((β - σ)^2 + (γ - t)^2)) := by ring
        _ = 1 * ((γ - t) / ((β - σ)^2 + (γ - t)^2)) := by rw [div_self hX]
        _ = (γ - t) / ((β - σ)^2 + (γ - t)^2) := by ring

    have h_comp_simp : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x))) ((γ - t) / ((β - σ)^2 + (γ - t)^2)) σ :=
      h_simp ▸ h_comp

    have h_final : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1 / 2)
                              (((γ - t) / ((β - σ)^2 + (γ - t)^2)) / (2 * Real.pi)) σ :=
      (h_comp_simp.div_const _).add_const _

    have h_scale : (((γ - t) / ((β - σ)^2 + (γ - t)^2)) / (2 * Real.pi)) = (1 / (2 * Real.pi)) * ((γ - t) / ((β - σ)^2 + (γ - t)^2)) := by ring

    exact (h_scale ▸ h_final).deriv

  · -- Case β - σ = 0
    exfalso
    exact h_sigma (sub_eq_zero.mp h_zero).symm

  · -- Case β - σ > 0 (i.e. x > 0 in pspace_arctan)
    have h_nhds : ∀ᶠ x in 𝓝 σ, 0 < β - x :=
      tendsto_const_nhds.eventually_lt (continuous_const.sub continuous_id).continuousAt h_pos
    have h_evt_eq : (fun x : ℝ => pspace_arctan (γ - t) (β - x)) =ᶠ[𝓝 σ] (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1) := by
      filter_upwards [h_nhds] with x hx
      dsimp [pspace_arctan]
      simp [hx]

    have h_deriv_eq : deriv (fun x : ℝ => pspace_arctan (γ - t) (β - x)) σ = deriv (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1) σ :=
      Filter.EventuallyEq.deriv_eq h_evt_eq
    rw [h_deriv_eq]

    have hd_num : HasDerivAt (fun _ : ℝ => γ - t) 0 σ := hasDerivAt_const _ _
    have hd_den : HasDerivAt (fun x : ℝ => β - x) (-1) σ := (hasDerivAt_id σ).const_sub β
    have hd_div : HasDerivAt (fun x : ℝ => (γ - t) / (β - x)) ((0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2) σ :=
      hd_num.div hd_den (ne_of_gt h_pos)
    have hd_div_simp : HasDerivAt (fun x : ℝ => (γ - t) / (β - x)) ((γ - t) / (β - σ)^2) σ := by
      have h_alg : (0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2 = (γ - t) / (β - σ)^2 := by ring
      exact h_alg ▸ hd_div

    have h_comp : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x))) ((1 / (1 + ((γ - t) / (β - σ))^2)) * ((γ - t) / (β - σ)^2)) σ := by
      have h_raw := HasDerivAt.comp σ (Real.hasDerivAt_arctan ((γ - t) / (β - σ))) hd_div_simp
      have h_eq : (Real.arctan ∘ fun x : ℝ => (γ - t) / (β - x)) = fun x : ℝ => Real.arctan ((γ - t) / (β - x)) := rfl
      exact h_eq ▸ h_raw

    have h_simp : (1 / (1 + ((γ - t) / (β - σ))^2)) * ((γ - t) / (β - σ)^2) = (γ - t) / ((β - σ)^2 + (γ - t)^2) := by
      have hX : (β - σ)^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h_pos)
      have hd1 : 1 + ((γ - t) / (β - σ))^2 = ((β - σ)^2 + (γ - t)^2) / (β - σ)^2 := by
        rw [div_pow, add_div_eq_mul_add_div 1 ((γ - t)^2) hX, one_mul]
      rw [hd1, one_div, inv_div]
      calc (β - σ)^2 / ((β - σ)^2 + (γ - t)^2) * ((γ - t) / (β - σ)^2)
        _ = ((β - σ)^2 / (β - σ)^2) * ((γ - t) / ((β - σ)^2 + (γ - t)^2)) := by ring
        _ = 1 * ((γ - t) / ((β - σ)^2 + (γ - t)^2)) := by rw [div_self hX]
        _ = (γ - t) / ((β - σ)^2 + (γ - t)^2) := by ring

    have h_comp_simp : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x))) ((γ - t) / ((β - σ)^2 + (γ - t)^2)) σ :=
      h_simp ▸ h_comp

    have h_final : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1)
                              (((γ - t) / ((β - σ)^2 + (γ - t)^2)) / (2 * Real.pi)) σ :=
      (h_comp_simp.div_const _).add_const _

    have h_scale : (((γ - t) / ((β - σ)^2 + (γ - t)^2)) / (2 * Real.pi)) = (1 / (2 * Real.pi)) * ((γ - t) / ((β - σ)^2 + (γ - t)^2)) := by ring

    exact (h_scale ▸ h_final).deriv


/-- Differentiability of A_rho off-line -/
lemma differentiableAt_A_rho (β γ σ t : ℝ) (h_sigma : σ ≠ β) : DifferentiableAt ℝ (fun x => A_rho β γ x t) σ := by
  dsimp [A_rho]
  rcases lt_trichotomy (β - σ) 0 with h_neg | h_zero | h_pos
  · have h_nhds : ∀ᶠ x in 𝓝 σ, β - x < 0 :=
      (continuous_const.sub continuous_id).continuousAt.eventually_lt tendsto_const_nhds h_neg
    have h_evt_eq : (fun x : ℝ => pspace_arctan (γ - t) (β - x)) =ᶠ[𝓝 σ] (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1 / 2) := by
      filter_upwards [h_nhds] with x hx
      dsimp [pspace_arctan]
      have h_not_pos : ¬(β - x > 0) := not_lt.mpr (le_of_lt hx)
      simp [hx, h_not_pos]

    have hd_num : HasDerivAt (fun _ : ℝ => γ - t) 0 σ := hasDerivAt_const _ _
    have hd_den : HasDerivAt (fun x : ℝ => β - x) (-1) σ := (hasDerivAt_id σ).const_sub β
    have hd_div : HasDerivAt (fun x : ℝ => (γ - t) / (β - x)) ((0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2) σ :=
      hd_num.div hd_den (ne_of_lt h_neg)

    have h_comp : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x))) ((1 / (1 + ((γ - t) / (β - σ))^2)) * ((0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2)) σ := by
      have h_raw := HasDerivAt.comp σ (Real.hasDerivAt_arctan ((γ - t) / (β - σ))) hd_div
      have h_eq : (Real.arctan ∘ fun x : ℝ => (γ - t) / (β - x)) = fun x : ℝ => Real.arctan ((γ - t) / (β - x)) := rfl
      exact h_eq ▸ h_raw

    have h_final : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1 / 2)
                              (((1 / (1 + ((γ - t) / (β - σ))^2)) * ((0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2)) / (2 * Real.pi)) σ :=
      (h_comp.div_const _).add_const _

    exact h_evt_eq.differentiableAt_iff.mpr h_final.differentiableAt

  · exfalso
    exact h_sigma (sub_eq_zero.mp h_zero).symm

  · have h_nhds : ∀ᶠ x in 𝓝 σ, 0 < β - x :=
      tendsto_const_nhds.eventually_lt (continuous_const.sub continuous_id).continuousAt h_pos
    have h_evt_eq : (fun x : ℝ => pspace_arctan (γ - t) (β - x)) =ᶠ[𝓝 σ] (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1) := by
      filter_upwards [h_nhds] with x hx
      dsimp [pspace_arctan]
      simp [hx]

    have hd_num : HasDerivAt (fun _ : ℝ => γ - t) 0 σ := hasDerivAt_const _ _
    have hd_den : HasDerivAt (fun x : ℝ => β - x) (-1) σ := (hasDerivAt_id σ).const_sub β
    have hd_div : HasDerivAt (fun x : ℝ => (γ - t) / (β - x)) ((0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2) σ :=
      hd_num.div hd_den (ne_of_gt h_pos)

    have h_comp : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x))) ((1 / (1 + ((γ - t) / (β - σ))^2)) * ((0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2)) σ := by
      have h_raw := HasDerivAt.comp σ (Real.hasDerivAt_arctan ((γ - t) / (β - σ))) hd_div
      have h_eq : (Real.arctan ∘ fun x : ℝ => (γ - t) / (β - x)) = fun x : ℝ => Real.arctan ((γ - t) / (β - x)) := rfl
      exact h_eq ▸ h_raw

    have h_final : HasDerivAt (fun x : ℝ => Real.arctan ((γ - t) / (β - x)) / (2 * Real.pi) + 1)
                              (((1 / (1 + ((γ - t) / (β - σ))^2)) * ((0 * (β - σ) - (γ - t) * (-1)) / (β - σ)^2)) / (2 * Real.pi)) σ :=
      (h_comp.div_const _).add_const _

    exact h_evt_eq.differentiableAt_iff.mpr h_final.differentiableAt

/-- Differentiability of B_rho -/
lemma differentiableAt_B_rho (β γ σ t : ℝ) : DifferentiableAt ℝ (fun x => B_rho β γ x t) σ := by
  have h_explicit : (fun x => B_rho β γ x t) = fun x => ((1 / (2 * Real.pi)) * (1 / (β^2 + γ^2))) * (t * β - x * γ) := by
    ext x; exact B_rho_explicit β γ x t
  rw [h_explicit]
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub
  · exact differentiableAt_const _
  · exact DifferentiableAt.mul_const differentiableAt_id γ

/-- Differentiability and derivative of the constant term -/
lemma deriv_const_rho_full (β γ σ : ℝ) :
    deriv (fun _ => const_rho β γ) σ = 0 := by
  simp

/-- Linearity of the phase components. -/
lemma psi_rho_linearity (β γ σ t : ℝ) (h_sigma : σ ≠ β) :
    deriv (fun x => psi_rho β γ x t) σ =
    deriv (fun x => A_rho β γ x t) σ + deriv (fun x => B_rho β γ x t) σ + deriv (fun _ => const_rho β γ) σ := by
  have h_psi : (fun x => psi_rho β γ x t) = fun x => (A_rho β γ x t + B_rho β γ x t) + const_rho β γ := rfl
  rw [h_psi]
  have h_AB : DifferentiableAt ℝ (fun x => A_rho β γ x t + B_rho β γ x t) σ :=
    DifferentiableAt.add (differentiableAt_A_rho β γ σ t h_sigma) (differentiableAt_B_rho β γ σ t)
  have h_C : DifferentiableAt ℝ (fun _ => const_rho β γ) σ :=
    differentiableAt_const _
  have h_add1 : deriv (fun x => (A_rho β γ x t + B_rho β γ x t) + const_rho β γ) σ =
                deriv (fun x => A_rho β γ x t + B_rho β γ x t) σ + deriv (fun _ => const_rho β γ) σ :=
    deriv_add h_AB h_C
  rw [h_add1]
  have h_add2 : deriv (fun x => A_rho β γ x t + B_rho β γ x t) σ =
                deriv (fun x => A_rho β γ x t) σ + deriv (fun x => B_rho β γ x t) σ :=
    deriv_add (differentiableAt_A_rho β γ σ t h_sigma) (differentiableAt_B_rho β γ σ t)
  rw [h_add2]

/-- Lemma 3.3 (Zero kernel).
For ρ = β + iγ and s = σ + it, the σ-derivative of the zero phase ψ_ρ(σ,t). -/
lemma lemma_3_3_zero_kernel (β γ σ t : ℝ) (h_sigma : σ ≠ β) :
    deriv (fun x => psi_rho β γ x t) σ =
    (1 / (2 * Real.pi)) * (((γ - t) / ((β - σ)^2 + (γ - t)^2)) - (γ / (β^2 + γ^2))) := by
  rw [psi_rho_linearity β γ σ t h_sigma]
  rw [deriv_A_rho_full β γ σ t h_sigma]
  rw [deriv_B_rho_full β γ σ t]
  rw [deriv_const_rho_full β γ σ]
  ring

-- Section 3.4: Symmetry, pairing, and the constant offset

/-- The variable Cauchy-like term of the zero kernel (Equation 130) -/
noncomputable def K_rho (β γ σ t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ((γ - t) / ((β - σ)^2 + (γ - t)^2))

/-- The constant offset of the zero kernel (Equation 130) -/
noncomputable def C_rho (β γ : ℝ) : ℝ :=
  -(1 / (2 * Real.pi)) * (γ / (β^2 + γ^2))

/-- The kernel decomposes into the variable term and constant offset (Equation 129) -/
lemma psi_rho_deriv_decomp (β γ σ t : ℝ) (h_sigma : σ ≠ β) :
    deriv (fun x => psi_rho β γ x t) σ = K_rho β γ σ t + C_rho β γ := by
  rw [lemma_3_3_zero_kernel β γ σ t h_sigma]
  dsimp [K_rho, C_rho]
  ring

/-- Lemma 3.4.1 (Cancellation of the constant offset). -/
lemma lemma_3_4_1_offset_cancellation (β γ : ℝ) :
    C_rho β γ + C_rho (1 - β) (-γ) + C_rho β (-γ) + C_rho (1 - β) γ = 0 := by
  have h_pair1 : C_rho β γ + C_rho β (-γ) = 0 := by
    dsimp [C_rho]; ring
  have h_pair2 : C_rho (1 - β) (-γ) + C_rho (1 - β) γ = 0 := by
    dsimp [C_rho]; ring
  have h_rearrange : C_rho β γ + C_rho (1 - β) (-γ) + C_rho β (-γ) + C_rho (1 - β) γ =
                     (C_rho β γ + C_rho β (-γ)) + (C_rho (1 - β) (-γ) + C_rho (1 - β) γ) := by ring
  rw [h_rearrange, h_pair1, h_pair2]
  ring

/-- Sum of a function over the standard symmetric quadruplet {ρ, 1-ρ, ρ̄, 1-ρ̄} -/
noncomputable def quad_sum (f : ℝ → ℝ → ℝ) (β γ : ℝ) : ℝ :=
  f β γ + f (1 - β) (-γ) + f β (-γ) + f (1 - β) γ

/-- Lemma 3.4.2 (Global phase derivative reduction). -/
lemma lemma_3_4_2_global_phase_reduction (β γ σ t : ℝ) (h_sigma : σ ≠ β) (h_sigma_refl : σ ≠ 1 - β) :
    quad_sum (fun b g => deriv (fun x => psi_rho b g x t) σ) β γ =
    quad_sum (fun b g => K_rho b g σ t) β γ := by
  dsimp [quad_sum]
  rw [psi_rho_deriv_decomp β γ σ t h_sigma]
  rw [psi_rho_deriv_decomp (1 - β) (-γ) σ t h_sigma_refl]
  rw [psi_rho_deriv_decomp β (-γ) σ t h_sigma]
  rw [psi_rho_deriv_decomp (1 - β) γ σ t h_sigma_refl]
  have h_group :
    (K_rho β γ σ t + C_rho β γ) +
    (K_rho (1 - β) (-γ) σ t + C_rho (1 - β) (-γ)) +
    (K_rho β (-γ) σ t + C_rho β (-γ)) +
    (K_rho (1 - β) γ σ t + C_rho (1 - β) γ) =
    (K_rho β γ σ t + K_rho (1 - β) (-γ) σ t + K_rho β (-γ) σ t + K_rho (1 - β) γ σ t) +
    (C_rho β γ + C_rho (1 - β) (-γ) + C_rho β (-γ) + C_rho (1 - β) γ) := by ring
  rw [h_group]
  rw [lemma_3_4_1_offset_cancellation β γ]
  ring

/-- Connects K_rho directly to the complex Cauchy quotient (Equations 111–113 & 130). -/
lemma K_rho_eq_im_neg_inv (β γ σ t : ℝ) :
    K_rho β γ σ t = (1 / (2 * Real.pi)) * (-1 / Complex.mk (β - σ) (γ - t)).im := by
  dsimp [K_rho]
  rw [im_neg_inv_A_rho β γ σ t]

/-- Connects K_rho directly to the spatial derivative of A_rho (Equation 114). -/
lemma K_rho_eq_deriv_A_rho (β γ σ t : ℝ) (h_sigma : σ ≠ β) :
    K_rho β γ σ t = deriv (fun x => A_rho β γ x t) σ := by
  rw [deriv_A_rho_full β γ σ t h_sigma]
  rfl

/-- Connects C_rho directly to the spatial derivative of B_rho (Equation 122). -/
lemma C_rho_eq_deriv_B_rho (β γ σ t : ℝ) :
    C_rho β γ = deriv (fun x => B_rho β γ x t) σ := by
  rw [deriv_B_rho_full β γ σ t]
  rfl

end TainoPolar
