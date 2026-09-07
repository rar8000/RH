/-
Copyright (c) 2026 Richard Andrew Rodriguez.
Released under the MIT license.
Manuscript DOI: 10.5281/zenodo.22559147
-/
import Mathlib
import RH.Axioms
import RH.Kernel

open Complex Filter Topology

namespace TainoPolar

-- Section 4: Linearity of the phase derivative over the zero sum
-- Section 4.1: The linearity question
-- Section 4.2.1: Absolute convergence of the symmetric Hadamard product

variable (β γ σ t : ℝ)

/-- The symmetric quadruplet product P_ρ(s) for an orbit representative -/
noncomputable def P_rho (β γ σ t : ℝ) : ℂ :=
  F_rho β γ σ t *
  F_rho (1 - β) γ σ t *
  F_rho β (-γ) σ t *
  F_rho (1 - β) (-γ) σ t

/-- Algebraic expansion of the sum of reciprocals of squared conjugate roots (Equation 157).
This proves exactly how the spatial denominators isolate the γ^-2 magnitude scaling. -/
lemma inv_sq_add_conj_sq :
    ((Complex.mk β γ)⁻¹)^2 + ((Complex.mk β (-γ))⁻¹)^2 =
    Complex.mk (2 * (β^2 - γ^2) / (β^2 + γ^2)^2) 0 := by
  have h1 : ((Complex.mk β γ)⁻¹)^2 = ((Complex.mk β γ)⁻¹) * ((Complex.mk β γ)⁻¹) := pow_two _
  have h2 : ((Complex.mk β (-γ))⁻¹)^2 = ((Complex.mk β (-γ))⁻¹) * ((Complex.mk β (-γ))⁻¹) := pow_two _
  rw [h1, h2]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq_mk]
    have h_neg : (-γ) * (-γ) = γ * γ := by ring
    rw [h_neg]
    have h_rhs : 2 * (β^2 - γ^2) / (β^2 + γ^2)^2 = 2 * (β^2 - γ^2) * ((β^2 + γ^2)⁻¹)^2 := by
      change 2 * (β^2 - γ^2) * ((β^2 + γ^2)^2)⁻¹ = _
      rw [pow_two (β^2 + γ^2)]
      have h_inv : ((β^2 + γ^2) * (β^2 + γ^2))⁻¹ = (β^2 + γ^2)⁻¹ * (β^2 + γ^2)⁻¹ := mul_inv (β^2 + γ^2) (β^2 + γ^2)
      rw [h_inv]
      rw [← pow_two ((β^2 + γ^2)⁻¹)]
    rw [h_rhs]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq_mk]
    have h_neg : (-γ) * (-γ) = γ * γ := by ring
    rw [h_neg]
    ring


/-- Full symmetric quadruplet reciprocal square sum (Equations 157, 158).
Proves the exact quadratic deviation denominator for the entire orbit. -/
lemma inv_sq_quad_sum :
    ((Complex.mk β γ)⁻¹)^2 + ((Complex.mk β (-γ))⁻¹)^2 +
    ((Complex.mk (1 - β) γ)⁻¹)^2 + ((Complex.mk (1 - β) (-γ))⁻¹)^2 =
    Complex.mk ((2 * (β^2 - γ^2) / (β^2 + γ^2)^2) + (2 * ((1 - β)^2 - γ^2) / ((1 - β)^2 + γ^2)^2)) 0 := by
  have h_group :
    ((Complex.mk β γ)⁻¹)^2 + ((Complex.mk β (-γ))⁻¹)^2 +
    ((Complex.mk (1 - β) γ)⁻¹)^2 + ((Complex.mk (1 - β) (-γ))⁻¹)^2 =
    (((Complex.mk β γ)⁻¹)^2 + ((Complex.mk β (-γ))⁻¹)^2) +
    (((Complex.mk (1 - β) γ)⁻¹)^2 + ((Complex.mk (1 - β) (-γ))⁻¹)^2) := by rw [add_assoc]
  rw [h_group]
  have h1 := inv_sq_add_conj_sq β γ
  have h2 := inv_sq_add_conj_sq (1 - β) γ
  rw [h1, h2]
  apply Complex.ext
  · simp only [Complex.add_re]
  · simp only [Complex.add_im, add_zero]


-- Section 4.2.1: Absolute convergence of the symmetric Hadamard product

/-- Sum of the native zero phase over the symmetric quadruplet -/
noncomputable def psi_quad_sum (β γ σ t : ℝ) : ℝ :=
  psi_rho β γ σ t + psi_rho (1 - β) γ σ t + psi_rho β (-γ) σ t + psi_rho (1 - β) (-γ) σ t

/-- Lemma 4.2.1 (Absolute convergence of the native phase).
We prove the topological uniform convergence limit by taking the classical analytic bounds
(Weierstrass magnitude bound and Riemann-von Mangoldt zero summability) as formal hypotheses.
By applying this directly to our native unwrapped phase `psi_quad_sum`, we completely
bypass the principal branch cuts of `Complex.log`. -/
lemma lemma_4_2_1_abs_conv_sym_product
    (I : Set ℝ)
    (beta gamma : ℕ → ℝ)
    (M : ℕ → ℝ)
    (h_summable : Summable M)
    (h_bound : ∀ (n : ℕ) (x : ℝ), x ∈ I → norm (psi_quad_sum (beta n) (gamma n) x t) ≤ M n) :
    TendstoUniformlyOn (fun (k : Finset ℕ) x => ∑ i ∈ k, psi_quad_sum (beta i) (gamma i) x t)
    (fun x => ∑' i, psi_quad_sum (beta i) (gamma i) x t) Filter.atTop I := by
  exact tendstoUniformlyOn_tsum h_summable h_bound


-- Section 4.2.2: Pointwise convergence of the phase series

/-- Lemma 4.2.2 (Pointwise convergence of phases).
Given the uniform convergence of the native phase sum (Lemma 4.2.1) and a fixed
point σ on the evaluation line, the sequence of partial phase sums converges pointwise
strictly to the infinite sum `tsum`. No complex branch cuts required. -/
lemma lemma_4_2_2_pointwise_convergence
    (I : Set ℝ)
    (beta gamma : ℕ → ℝ)
    (h_in : σ ∈ I)
    (h_uniform : TendstoUniformlyOn
      (fun (k : Finset ℕ) x => ∑ i ∈ k, psi_quad_sum (beta i) (gamma i) x t)
      (fun x => ∑' i, psi_quad_sum (beta i) (gamma i) x t) Filter.atTop I) :
    Tendsto (fun (k : Finset ℕ) => ∑ i ∈ k, psi_quad_sum (beta i) (gamma i) σ t)
      Filter.atTop (nhds (∑' i, psi_quad_sum (beta i) (gamma i) σ t)) := by
  exact TendstoUniformlyOn.tendsto_at h_uniform h_in


-- Section 4.2.3: Termwise differentiability of zero phases

/-- Lemma 4.2.3 (Differentiability of individual zero phases).
For a fixed zero ρ and ordinate t, the spatial derivative of the unwrapped phase
evaluates exactly to the continuous kernel outside the singularity (σ + it ≠ ρ).
This natively inherits the exact algebraic decomposition proven in Lemma 3.4. -/
lemma lemma_4_2_3_diff_zero_phase
    (_h_neq : Complex.mk σ t ≠ Complex.mk β γ) :
    deriv (fun x => psi_rho β γ x t) σ = K_rho β γ σ t + C_rho β γ := by
  exact psi_rho_deriv_decomp β γ σ t


-- Section 4.2.4: Uniform convergence of the differentiated series

/-- Sum of the Cauchy-like kernels over a symmetric quadruplet (Equation 176) -/
noncomputable def S_rho (β γ σ t : ℝ) : ℝ :=
  K_rho β γ σ t + K_rho (1 - β) γ σ t + K_rho β (-γ) σ t + K_rho (1 - β) (-γ) σ t

/-- Algebraic cancellation of the conjugate kernel sum (Equations 180, 181).
We prove the numerator of the combined fraction exactly isolates the O(1/γ^2) dependence
by completely canceling the O(1/γ) leading terms. X represents the real distance (β - σ). -/
lemma S_rho_conj_num_cancel (X : ℝ) :
    (γ - t) * (X^2 + (-γ - t)^2) + (-γ - t) * (X^2 + (γ - t)^2) =
    2 * t * (γ^2 - X^2 - t^2) := by
  ring

/-- Algebraic expansion of the combined conjugate denominator.
Demonstrates the denominator strictly scales as γ^4, which combined with the γ^2 numerator,
yields the exact O(1/γ^2) asymptotic decay bound (Equation 182). -/
lemma S_rho_conj_den_expand (X : ℝ) :
    (X^2 + (γ - t)^2) * (X^2 + (-γ - t)^2) =
    (X^2 + γ^2 + t^2)^2 - 4 * γ^2 * t^2 := by
  ring

/-- Lemma 4.2.4 (Uniform convergence of zero kernels).
We establish uniform convergence of the spatial derivative series over any compact
interval I, mapping the Riemann-von Mangoldt O(1/γ^2) summability strictly through
the Weierstrass M-test as formalized by Mathlib. -/
lemma lemma_4_2_4_uni_conv_kernel
    (I : Set ℝ)
    (beta gamma : ℕ → ℝ)
    (M : ℕ → ℝ)
    (h_summable : Summable M)
    (h_bound : ∀ (n : ℕ) (σ : ℝ), σ ∈ I → norm (S_rho (beta n) (gamma n) σ t) ≤ M n) :
    TendstoUniformlyOn (fun (k : Finset ℕ) σ => ∑ i ∈ k, S_rho (beta i) (gamma i) σ t)
    (fun σ => ∑' i, S_rho (beta i) (gamma i) σ t) Filter.atTop I := by
  exact tendstoUniformlyOn_tsum h_summable h_bound


-- Section 4.2.5: Linearity of the phase derivative

/-- Lemma 4.2.4b (Bridge to Section 3 Calculus).
Converts the algebraic derivative equality proven in Section 3 into the strict
HasDerivAt typeclass required by Mathlib's infinite summation theorems. -/
lemma lemma_4_2_4b_bridge_quadruplet_hasDerivAt
    (β γ y t : ℝ)
    (h_diff : DifferentiableAt ℝ (fun x => psi_quad_sum β γ x t) y)
    (h_deriv_eq : deriv (fun x => psi_quad_sum β γ x t) y = S_rho β γ y t) :
    HasDerivAt (fun x => psi_quad_sum β γ x t) (S_rho β γ y t) y := by
  -- Mathlib intrinsically links the evaluated derivative to the HasDerivAt typeclass
  -- as long as formal differentiability is established.
  rw [← h_deriv_eq]
  exact DifferentiableAt.hasDerivAt h_diff

/-- Lemma 4.2.5 (Term-by-term differentiation of the phase series).
We prove the spatial derivative of the global phase is exactly the sum of the spatial kernels.
By passing the exact Weierstrass M-test bounds and bridging the Section 3 kernel derivatives,
we natively invoke Mathlib's `hasDerivAt_tsum` to legally grant the infinite derivative swap. -/
lemma lemma_4_2_5_linearity_of_phase_derivative
    (theta Phi : ℝ → ℝ)
    (beta gamma : ℕ → ℝ)
    (M : ℕ → ℝ)
    (σ t : ℝ)
    (h_decomp : ∀ x, theta x = Phi x + ∑' i, psi_quad_sum (beta i) (gamma i) x t)
    (h_Phi_const : ∀ x, deriv Phi x = 0)
    (h_diff_Phi : DifferentiableAt ℝ Phi σ)
    (h_quad_diff : ∀ i y, DifferentiableAt ℝ (fun x => psi_quad_sum (beta i) (gamma i) x t) y)
    (h_quad_deriv_eq : ∀ i y, deriv (fun x => psi_quad_sum (beta i) (gamma i) x t) y = S_rho (beta i) (gamma i) y t)
    (h_summable_M : Summable M)
    (h_bound : ∀ i y, ‖S_rho (beta i) (gamma i) y t‖ ≤ M i)
    (h_base_conv : Summable (fun i => psi_quad_sum (beta i) (gamma i) σ t)) :
    deriv theta σ = ∑' i, S_rho (beta i) (gamma i) σ t := by

  -- 0. Bridge the Section 3 algebra into the Section 4 HasDerivAt typeclass
  have h_has_deriv : ∀ i y, HasDerivAt (fun x => psi_quad_sum (beta i) (gamma i) x t) (S_rho (beta i) (gamma i) y t) y := by
    intro i y
    exact lemma_4_2_4b_bridge_quadruplet_hasDerivAt (beta i) (gamma i) y t (h_quad_diff i y) (h_quad_deriv_eq i y)

  -- 1. Natively invoke Mathlib's infinite sum derivative swap (Rudin's Theorem)
  have h_rudin := hasDerivAt_tsum h_summable_M h_has_deriv h_bound h_base_conv

  -- Evaluate the universal quantifier at our specific spatial ordinate σ
  have h_rudin_sigma := h_rudin σ

  -- 2. Substitute the global phase decomposition using point-wise function addition
  have h_fun_eq : theta = Phi + fun x => ∑' i, psi_quad_sum (beta i) (gamma i) x t := by
    ext x
    exact h_decomp x
  rw [h_fun_eq]

  -- 3. Distribute the spatial derivative over the addition using the sum rule
  -- Mathlib extracts the DifferentiableAt proof directly from the evaluated HasDerivAt object
  rw [deriv_add h_diff_Phi h_rudin_sigma.differentiableAt]

  -- 4. Evaluate the derivatives using the proven infinite sum swap
  rw [h_Phi_const σ]
  rw [h_rudin_sigma.deriv]

  -- 5. Clean up the resulting 0 + X = X algebra
  rw [zero_add]
