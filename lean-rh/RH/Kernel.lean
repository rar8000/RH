/-
Copyright (c) 2026 Richard Andrew Rodriguez.
Released under the MIT license.
Manuscript DOI: 10.5281/zenodo.22559147
-/
import Mathlib

open Complex

namespace TainoPolar

-- Section 3: The Hadamard phase of a single zero
variable (β γ σ t : ℝ)

/-- The zero ρ = β + iγ -/
noncomputable def rho := Complex.mk β γ

/-- The evaluation coordinate s = σ + it -/
noncomputable def s_val := Complex.mk σ t

/-- The Local Hadamard Factor F_ρ(s) = (1 - s/ρ) * exp(s/ρ) -/
noncomputable def F_rho : ℂ :=
  (1 - (s_val σ t) / (rho β γ)) * Complex.exp ((s_val σ t) / (rho β γ))


-- Section 3.1: Explicit formula for the zero phase

/-- The arctangent term A_ρ(σ, t).
Redefined using the rigorous real-analytic arctangent mapping to naturally
represent the continuous unwrapped phase along the spatial line, natively
avoiding the Complex.arg branch cuts. -/
noncomputable def A_rho : ℝ :=
  (1 / (2 * Real.pi)) * Real.arctan ((σ - β) / (γ - t))

/-- The linear exponential term B_ρ(σ, t) -/
noncomputable def B_rho : ℝ :=
  (1 / (2 * Real.pi)) * ((s_val σ t) / (rho β γ)).im

/-- The constant background offset from the denominator's phase -/
noncomputable def const_rho : ℝ :=
  -(1 / (2 * Real.pi)) * Complex.arg (rho β γ)

/-- The total decomposed phase ψ_ρ(σ, t) -/
noncomputable def psi_rho : ℝ :=
  A_rho β γ σ t + B_rho β γ σ t + const_rho β γ

/-- Verifying the Cartesian expansion of the (1 - s/ρ) fraction (Equation 101) -/
lemma one_sub_s_div_rho (h_rho_nz : rho β γ ≠ 0) :
    1 - (s_val σ t) / (rho β γ) = (Complex.mk (β - σ) (γ - t)) / (rho β γ) := by
  have h1 : (1 : ℂ) = (rho β γ) / (rho β γ) := (div_self h_rho_nz).symm
  rw [h1]
  rw [← sub_div]
  have h_num : rho β γ - s_val σ t = Complex.mk (β - σ) (γ - t) := by
    apply Complex.ext
    · simp [rho, s_val]
    · simp [rho, s_val]
  rw [h_num]


-- Section 3.2.1: Derivative of the arctangent term A_rho

/-- Algebraic reduction of the complex quotient (Equations 111, 112, 113) -/
lemma im_neg_inv_complex (X Y : ℝ) :
    (-1 / Complex.mk X Y).im = Y / (X^2 + Y^2) := by
  have h1 : (-1 : ℂ) / Complex.mk X Y = - (Complex.mk X Y)⁻¹ := by
    calc (-1 : ℂ) / Complex.mk X Y
      _ = (-1 : ℂ) * (Complex.mk X Y)⁻¹ := div_eq_mul_inv _ _
      _ = - (Complex.mk X Y)⁻¹ := neg_one_mul _
  rw [h1]
  rw [Complex.neg_im, Complex.inv_im]
  dsimp [Complex.normSq]
  ring

/-- Mapping the quotient reduction strictly to our β, γ, σ, t coordinates -/
lemma im_neg_inv_A_rho :
    (-1 / Complex.mk (β - σ) (γ - t)).im = (γ - t) / ((β - σ)^2 + (γ - t)^2) := by
  exact im_neg_inv_complex (β - σ) (γ - t)


-- Section 3.2.2: Derivative of the linear term B_rho

/-- Expanding the complex quotient into real and imaginary parts (Equation 116) -/
lemma s_div_rho_im :
    ((s_val σ t) / (rho β γ)).im = (t * β - σ * γ) / (β^2 + γ^2) := by
  dsimp [s_val, rho]
  rw [Complex.div_im]
  dsimp [Complex.normSq]
  ring

/-- Algebraic resolution of B_rho (Equations 117, 118) -/
lemma B_rho_explicit :
    B_rho β γ σ t = (1 / (2 * Real.pi)) * (1 / (β^2 + γ^2)) * (t * β - σ * γ) := by
  dsimp [B_rho]
  rw [s_div_rho_im β γ σ t]
  ring

/-- Evaluating the partial differential in isolation (Equation 120) -/
lemma deriv_linear_term :
    deriv (fun x => t * β - x * γ) σ = -γ := by
  simp

/-- Differentiating the full linear phase component (Equations 119, 122) -/
lemma deriv_B_rho_full :
    deriv (fun x => B_rho β γ x t) σ = -(1 / (2 * Real.pi)) * (γ / (β^2 + γ^2)) := by
  have h_explicit : (fun x => B_rho β γ x t) = fun x => ((1 / (2 * Real.pi)) * (1 / (β^2 + γ^2))) * (t * β - x * γ) := by
    ext x
    exact B_rho_explicit β γ x t
  rw [h_explicit]
  simp
  ring


-- Section 3.3: Exact kernel formula



/-- Differentiability and derivative of A_rho (Equation 114).
Proven natively using Mathlib's strict calculus engine without axioms.
The proof branches gracefully to handle evaluation exactly on the ordinate. -/
lemma deriv_A_rho_full :
    deriv (fun x => A_rho β γ x t) σ = (1 / (2 * Real.pi)) * ((γ - t) / ((β - σ)^2 + (γ - t)^2)) := by
  dsimp [A_rho]
  by_cases h_t : γ - t = 0
  · -- Case 1: On the ordinate (γ = t)
    rw [h_t]
    have h_rhs : (1 / (2 * Real.pi)) * (0 / ((β - σ)^2 + 0^2)) = 0 := by
      have hz : 0 / ((β - σ)^2 + 0^2) = 0 := zero_div _
      rw [hz, mul_zero]
    rw [h_rhs]
    have h_lhs : (fun x => (1 / (2 * Real.pi)) * Real.arctan ((x - β) / 0)) = fun x => 0 := by
      ext x
      rw [div_zero, Real.arctan_zero, mul_zero]
    rw [h_lhs]
    exact deriv_const σ 0
  · -- Case 2: Off the ordinate (γ ≠ t)
    have h_inner_diff : DifferentiableAt ℝ (fun x => (x - β) / (γ - t)) σ := by
      apply DifferentiableAt.div_const
      exact DifferentiableAt.sub_const differentiableAt_id β

    have h_arctan_deriv_at := Real.hasDerivAt_arctan ((σ - β) / (γ - t))
    have h_arctan_diff : DifferentiableAt ℝ Real.arctan ((σ - β) / (γ - t)) := h_arctan_deriv_at.differentiableAt

    have h_comp_diff : DifferentiableAt ℝ (fun x => Real.arctan ((x - β) / (γ - t))) σ := by
      change DifferentiableAt ℝ (Real.arctan ∘ fun x => (x - β) / (γ - t)) σ
      exact DifferentiableAt.comp σ h_arctan_diff h_inner_diff

    rw [deriv_const_mul (1 / (2 * Real.pi)) h_comp_diff]

    have hd1 : deriv (fun x => Real.arctan ((x - β) / (γ - t))) σ = (γ - t) / ((β - σ)^2 + (γ - t)^2) := by
      have h_comp_eq : (fun x => Real.arctan ((x - β) / (γ - t))) = Real.arctan ∘ (fun x => (x - β) / (γ - t)) := rfl
      rw [h_comp_eq]
      rw [deriv_comp]
      · have h_outer : deriv Real.arctan ((σ - β) / (γ - t)) = 1 / (1 + ((σ - β) / (γ - t))^2) := h_arctan_deriv_at.deriv
        have h_inner : deriv (fun x => (x - β) / (γ - t)) σ = 1 / (γ - t) := by
          have h_eq : (fun x => (x - β) / (γ - t)) = fun x => (1 / (γ - t)) * x - β / (γ - t) := by
            ext x; ring
          rw [h_eq]
          simp
        rw [h_outer, h_inner]

        -- The remaining block reduces the fraction algebraically using strictly non-zero bounds
        have hY2 : (γ - t)^2 ≠ 0 := pow_ne_zero 2 h_t
        have h1 : 1 + ((σ - β) / (γ - t))^2 = ((γ - t)^2 + (σ - β)^2) / (γ - t)^2 := by
          calc 1 + ((σ - β) / (γ - t))^2 = 1 + (σ - β)^2 / (γ - t)^2 := by rw [div_pow]
          _ = (γ - t)^2 / (γ - t)^2 + (σ - β)^2 / (γ - t)^2 := by rw [div_self hY2]
          _ = ((γ - t)^2 + (σ - β)^2) / (γ - t)^2 := by rw [add_div]
        rw [h1]

        -- SURGERY: explicitly chain one_div (inverse) and inv_div (fraction flip)
        have h2 : 1 / (((γ - t)^2 + (σ - β)^2) / (γ - t)^2) = (γ - t)^2 / ((γ - t)^2 + (σ - β)^2) := by
          rw [one_div, inv_div]

        rw [h2]
        calc (γ - t)^2 / ((γ - t)^2 + (σ - β)^2) * (1 / (γ - t))
          _ = ((γ - t) * (γ - t)) / ((γ - t)^2 + (σ - β)^2) * (1 / (γ - t)) := by rw [pow_two]
          _ = (γ - t) / ((γ - t)^2 + (σ - β)^2) * ((γ - t) * (1 / (γ - t))) := by ring
          _ = (γ - t) / ((γ - t)^2 + (σ - β)^2) * ((γ - t) / (γ - t)) := by ring
          _ = (γ - t) / ((γ - t)^2 + (σ - β)^2) * 1 := by rw [div_self h_t]
          _ = (γ - t) / ((β - σ)^2 + (γ - t)^2) := by
            have h_sq : (σ - β)^2 = (β - σ)^2 := by ring
            rw [h_sq, mul_one, add_comm ((γ - t)^2) ((β - σ)^2)]
      · exact h_arctan_diff
      · exact h_inner_diff
    rw [hd1]

/-- Differentiability of A_rho -/
lemma differentiableAt_A_rho : DifferentiableAt ℝ (fun x => A_rho β γ x t) σ := by
  dsimp [A_rho]
  by_cases h_t : γ - t = 0
  · rw [h_t]
    have h_fun : (fun x => (1 / (2 * Real.pi)) * Real.arctan ((x - β) / 0)) = fun x => 0 := by
      ext x; rw [div_zero, Real.arctan_zero, mul_zero]
    rw [h_fun]
    exact differentiableAt_const 0
  · have h_inner_diff : DifferentiableAt ℝ (fun x => (x - β) / (γ - t)) σ := by
      apply DifferentiableAt.div_const
      exact DifferentiableAt.sub_const differentiableAt_id β
    have h_arctan_diff : DifferentiableAt ℝ Real.arctan ((σ - β) / (γ - t)) := (Real.hasDerivAt_arctan _).differentiableAt
    have h_comp_diff : DifferentiableAt ℝ (fun x => Real.arctan ((x - β) / (γ - t))) σ := by
      change DifferentiableAt ℝ (Real.arctan ∘ fun x => (x - β) / (γ - t)) σ
      exact DifferentiableAt.comp σ h_arctan_diff h_inner_diff
    -- Use dot notation to natively apply the constant scalar multiplier
    exact h_comp_diff.const_mul (1 / (2 * Real.pi))

/-- Differentiability of B_rho -/
lemma differentiableAt_B_rho : DifferentiableAt ℝ (fun x => B_rho β γ x t) σ := by
  have h_explicit : (fun x => B_rho β γ x t) = fun x => ((1 / (2 * Real.pi)) * (1 / (β^2 + γ^2))) * (t * β - x * γ) := by
    ext x; exact B_rho_explicit β γ x t
  rw [h_explicit]
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub
  · exact differentiableAt_const _
  · exact DifferentiableAt.mul_const differentiableAt_id γ

/-- Differentiability and derivative of the constant term -/
lemma deriv_const_rho_full :
    deriv (fun _ => const_rho β γ) σ = 0 := by
  simp

/-- Linearity of the phase components.
Proven natively by distributing the derivative operator over the components. -/
lemma psi_rho_linearity :
    deriv (fun x => psi_rho β γ x t) σ =
    deriv (fun x => A_rho β γ x t) σ + deriv (fun x => B_rho β γ x t) σ + deriv (fun _ => const_rho β γ) σ := by
  have h_psi : (fun x => psi_rho β γ x t) = fun x => (A_rho β γ x t + B_rho β γ x t) + const_rho β γ := rfl
  rw [h_psi]

  -- 1. Bind the differentiability proofs
  have h_AB : DifferentiableAt ℝ (fun x => A_rho β γ x t + B_rho β γ x t) σ :=
    DifferentiableAt.add (differentiableAt_A_rho β γ σ t) (differentiableAt_B_rho β γ σ t)
  have h_C : DifferentiableAt ℝ (fun _ => const_rho β γ) σ :=
    differentiableAt_const _

  -- 2. Explicitly spell out the first distribution to bypass unification
  have h_add1 : deriv (fun x => (A_rho β γ x t + B_rho β γ x t) + const_rho β γ) σ =
                deriv (fun x => A_rho β γ x t + B_rho β γ x t) σ + deriv (fun _ => const_rho β γ) σ :=
    deriv_add h_AB h_C
  rw [h_add1]

  -- 3. Explicitly spell out the second distribution
  have h_add2 : deriv (fun x => A_rho β γ x t + B_rho β γ x t) σ =
                deriv (fun x => A_rho β γ x t) σ + deriv (fun x => B_rho β γ x t) σ :=
    deriv_add (differentiableAt_A_rho β γ σ t) (differentiableAt_B_rho β γ σ t)
  rw [h_add2]


/-- Lemma 3.3 (Zero kernel).
For ρ = β + iγ and s = σ + it, the σ-derivative of the zero phase ψ_ρ(σ,t). -/
lemma lemma_3_3_zero_kernel :
    deriv (fun x => psi_rho β γ x t) σ =
    (1 / (2 * Real.pi)) * (((γ - t) / ((β - σ)^2 + (γ - t)^2)) - (γ / (β^2 + γ^2))) := by
  rw [psi_rho_linearity β γ σ t]
  rw [deriv_A_rho_full β γ σ t]
  rw [deriv_B_rho_full β γ σ t]
  rw [deriv_const_rho_full β γ σ]
  ring


-- Section 3.4: Symmetry, pairing, and the constant offset

/-- The variable Cauchy-like term of the zero kernel (Equation 130) -/
noncomputable def K_rho : ℝ :=
  (1 / (2 * Real.pi)) * ((γ - t) / ((β - σ)^2 + (γ - t)^2))

/-- The constant offset of the zero kernel (Equation 130) -/
noncomputable def C_rho : ℝ :=
  -(1 / (2 * Real.pi)) * (γ / (β^2 + γ^2))

/-- The kernel decomposes into the variable term and constant offset (Equation 129) -/
lemma psi_rho_deriv_decomp :
    deriv (fun x => psi_rho β γ x t) σ = K_rho β γ σ t + C_rho β γ := by
  rw [lemma_3_3_zero_kernel β γ σ t]
  dsimp [K_rho, C_rho]
  ring

/-- Lemma 3.4.1 (Cancellation of the constant offset).
When non-trivial zeros are grouped into standard symmetric quadruplets Q = {ρ, 1-ρ, ρ̄, 1-ρ̄},
the sum of their constant offset terms vanishes identically (Equations 131, 135). -/
lemma lemma_3_4_1_offset_cancellation :
    C_rho β γ + C_rho (1 - β) (-γ) + C_rho β (-γ) + C_rho (1 - β) γ = 0 := by
  have h_pair1 : C_rho β γ + C_rho β (-γ) = 0 := by
    dsimp [C_rho]
    ring
  have h_pair2 : C_rho (1 - β) (-γ) + C_rho (1 - β) γ = 0 := by
    dsimp [C_rho]
    ring
  have h_rearrange : C_rho β γ + C_rho (1 - β) (-γ) + C_rho β (-γ) + C_rho (1 - β) γ =
                     (C_rho β γ + C_rho β (-γ)) + (C_rho (1 - β) (-γ) + C_rho (1 - β) γ) := by
    ring
  rw [h_rearrange]
  rw [h_pair1]
  rw [h_pair2]
  ring

/-- Sum of a function over the standard symmetric quadruplet {ρ, 1-ρ, ρ̄, 1-ρ̄} -/
noncomputable def quad_sum (f : ℝ → ℝ → ℝ) (β γ : ℝ) : ℝ :=
  f β γ + f (1 - β) (-γ) + f β (-γ) + f (1 - β) γ

/-- Lemma 3.4.2 (Global phase derivative reduction).
For the symmetric quadruplet, the constant offset terms cancel identically,
reducing the phase derivative sum strictly to the Cauchy-like kernels (Equations 137-143). -/
lemma lemma_3_4_2_global_phase_reduction :
    quad_sum (fun b g => deriv (fun x => psi_rho b g x t) σ) β γ =
    quad_sum (fun b g => K_rho b g σ t) β γ := by
  dsimp [quad_sum]
  rw [psi_rho_deriv_decomp β γ σ t]
  rw [psi_rho_deriv_decomp (1 - β) (-γ) σ t]
  rw [psi_rho_deriv_decomp β (-γ) σ t]
  rw [psi_rho_deriv_decomp (1 - β) γ σ t]
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

end TainoPolar
