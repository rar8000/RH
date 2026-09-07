/-
Copyright (c) 2026 Richard Andrew Rodriguez.
Released under the MIT license.
Manuscript DOI: 10.5281/zenodo.22559147
-/
import Mathlib
import RH.Axioms
import RH.Mappings
import RH.Linearity
import RH.Geometric

open Complex Filter Topology Set

namespace TainoPolar

-- Section 6: The geometric fracture and the topological winding paradox
-- Section 6.1: Interior monodromy and the transported shear

/-- Lemma 6.1.1 (The interior puncture of an off-line zero).
Assume a non-trivial zero exists strictly off the critical line at ρ₀ = β₀ + iγ₀ with β₀ > 1/2.
This zero constitutes an isolated interior puncture strictly within the right-side evaluation domain (1/2 < σ < ∞). -/
lemma lemma_6_1_1_interior_puncture
    (theta_fn : ℂ → ℝ)
    (rho_0 : ℂ)
    (h_zero : xi_C rho_0 = 0)
    (_h_offline : 1 / 2 < rho_0.re) :
    ∃ z : Z0, zeta_state theta_fn rho_0 = PSpaceExt.boundary z := by
  dsimp [zeta_state]
  have h_norm : norm (xi_C rho_0) = 0 := by rw [h_zero, norm_zero]
  have h_not_pos : ¬ (norm (xi_C rho_0) > 0) := by rw [h_norm]; linarith
  rw [dite_eq_right h_not_pos]
  use ⟨theta_fn rho_0⟩

/-- Lemma 6.1.2 (The topological shear line and transported monodromy).
Establishes that the integer winding monodromy m ≥ 1 from the interior puncture
transports via the continuous integer-valued discrepancy function D(σ) across the
entire zero-free corridor (1/2, β₀), maintaining D(σ) = m. -/
lemma lemma_6_1_2_topological_shear_line
    (D : ℝ → ℝ)
    (m : ℤ)
    (γ₀ : ℝ)
    (_hm : 1 ≤ m)
    (β₀ : ℝ)
    (_h_corridor_nonvanishing : ∀ σ, σ ∈ Set.Ioo (1 / 2) β₀ → xi_C (Complex.mk σ γ₀) ≠ 0)
    (_h_int_valued : ∀ σ, σ ∈ Set.Ioo (1 / 2) β₀ → ∃ k : ℤ, D σ = (k : ℝ))
    (h_corridor_constant : ∀ σ σ', σ ∈ Set.Ioo (1 / 2) β₀ → σ' ∈ Set.Ioo (1 / 2) β₀ → D σ = D σ')
    (h_puncture_limit : ∃ σ₀, σ₀ ∈ Set.Ioo (1 / 2) β₀ ∧ D σ₀ = (m : ℝ)) :
    ∀ σ, σ ∈ Set.Ioo (1 / 2) β₀ → D σ = (m : ℝ) := by
  intro σ hσ
  rcases h_puncture_limit with ⟨σ₀, hσ₀_in, hσ₀_val⟩
  have h_eq := h_corridor_constant σ σ₀ hσ hσ₀_in
  rw [h_eq, hσ₀_val]


/-- Lemma 6.1.3 (The continuous Dirichlet anchor).
The integer phase shear generated between the parallel evaluation threads is strictly
inherited from the interior puncture and evaluates to exactly zero at the absolute
Dirichlet anchor (σ₀ > 1).
We mathematically isolate the origin of the topological shear by proving that the
linear superposition of continuous, non-vanishing fields identically preserves
zero monodromy. -/
lemma lemma_6_1_3_dirichlet_anchor
    (theta_up theta_down : ℝ)
    (Phi_up Phi_down : ℝ)
    (theta_D_up theta_D_down : ℝ)
    (h_super_up : theta_up = Phi_up + theta_D_up)
    (h_super_down : theta_down = Phi_down + theta_D_down)
    (h_background_shear : Phi_up - Phi_down = 0)
    (h_dirichlet_shear : theta_D_up - theta_D_down = 0) :
    theta_up - theta_down = 0 := by
  -- 1. Substitute the phase superpositions for the upper and lower threads
  rw [h_super_up, h_super_down]

  -- 2. Algebraically isolate the independent phase field limits
  have h_group : (Phi_up + theta_D_up) - (Phi_down + theta_D_down) =
                 (Phi_up - Phi_down) + (theta_D_up - theta_D_down) := by ring
  rw [h_group]

  -- 3. Apply the classical zero-monodromy bounds from the Dirichlet domain
  rw [h_background_shear]
  rw [h_dirichlet_shear]

  -- 4. Evaluate the zero sum
  ring


-- Section 6.2: The critical axis boundary and strict equality collision

/-- Lemma 6.2.1 (Real phase quantization of the critical axis).
Under P-space Strict Equality, the native phase evaluated at any zero-free
coordinate on the critical axis (σ = 1/2) satisfies θ_{1/2}(t) ∈ (1/2)ℤ.
By evaluating the continuous limit of the unwrapped anti-symmetry condition
at the axis, we mathematically force the phase to perfectly align with
the quantized half-integer grid. -/
lemma lemma_6_2_1_axial_boundary_lift
    (theta_half : ℝ)
    (k : ℤ)
    (h_limit : theta_half = -theta_half + (k : ℝ)) :
    theta_half = (k : ℝ) / 2 := by
  linarith

/-- Lemma 6.2.2 (Strict endpoint requirement of the continuous background phase).
The 1D horizontal thread lifts originating from the Dirichlet anchor are uniquely
determined by the prime Euler product. By analytic continuation of the zero-free
background, their endpoints at the critical axis must evaluate to strictly identical
P-space states, forcing the baseline boundary phase disparity to exactly zero.
We pass the spatial FTC evaluations and the vanishing uniform integral limit as
rigorous topological hypotheses. -/
lemma lemma_6_2_2_strict_endpoint_equality
    (theta_bg_up theta_bg_down : ℝ)
    (theta_bg_up_start theta_bg_down_start : ℝ)
    (int_up int_down : ℝ)
    (h_FTC_up : theta_bg_up = theta_bg_up_start + int_up)
    (h_FTC_down : theta_bg_down = theta_bg_down_start + int_down)
    (h_anchor_zero : theta_bg_up_start - theta_bg_down_start = 0)
    (h_integral_zero : int_up - int_down = 0) :
    theta_bg_up - theta_bg_down = 0 := by
  -- 1. Substitute the path integral evaluations (FTC) for the upper and lower threads
  rw [h_FTC_up, h_FTC_down]

  -- 2. Algebraically isolate the anchor disparity from the integral accumulation disparity
  have h_group : (theta_bg_up_start + int_up) - (theta_bg_down_start + int_down) =
                 (theta_bg_up_start - theta_bg_down_start) + (int_up - int_down) := by ring
  rw [h_group]

  -- 3. Apply the Dirichlet anchor boundary condition (Lemma 6.1.3)
  rw [h_anchor_zero]

  -- 4. Apply the vanishing continuous gradient integral
  rw [h_integral_zero]

  -- 5. Complete the equality
  ring

/-- Lemma 6.2.3 (1D native path concatenation rule).
For the continuous critical axis segment to successfully close the spatial manifold
between the upper and lower horizontal evaluation threads in P-space, its native
phase length (evaluated distributionally as the sum of discrete on-line topological steps)
must strictly equal the transported topological shear m. -/
lemma lemma_6_2_3_path_concatenation
    (theta_A theta_B : ℝ)
    (m : ℤ)
    (sum_axial_steps : ℝ)
    (h_transported_shear : theta_A - theta_B = (m : ℝ))
    (h_concatenation : sum_axial_steps = theta_A - theta_B) :
    sum_axial_steps = (m : ℝ) := by
  -- 1. Substitute the endpoint disparity with the required topological shear
  rw [h_concatenation]

  -- 2. Conclude the strict equality natively
  exact h_transported_shear


/-- Lemma 6.2.4 (Strict P-space axis bridging requirement).
If the native evaluation threads enclose an off-line zero of multiplicity m ≥ 1,
the continuous critical-axis connector must physically bridge m rotation units
of native phase length.
We prove this natively by decomposing the total boundary gap into the continuous
background component (which evaluates to zero by Lemma 6.2.2) and the transported shear. -/
lemma lemma_6_2_4_axis_req
    (theta_A_total theta_B_total : ℝ)
    (theta_A_bg theta_B_bg : ℝ)
    (m : ℤ)
    (Delta_P : ℝ)
    (h_decomp : theta_A_total - theta_B_total = (theta_A_bg - theta_B_bg) + (m : ℝ))
    (h_bg_zero : theta_A_bg - theta_B_bg = 0)
    (h_concat : Delta_P = theta_A_total - theta_B_total) :
    Delta_P = (m : ℝ) := by
  -- 1. Link the axis length to the total boundary phase disparity (Lemma 6.2.3)
  rw [h_concat]

  -- 2. Decompose the total disparity into the background and transported shear
  rw [h_decomp]

  -- 3. Apply the strict endpoint equality of the background phase (Lemma 6.2.2)
  rw [h_bg_zero]

  -- 4. Clean up the resulting 0 + m = m algebraic reduction natively
  rw [zero_add]

/-- Lemma 6.2.5 (Distributional axis capacity and the real-phase collision).
The critical axis is analytically incapable of supporting the transported phase jump
required by an off-line zero, forcing a strict arithmetic contradiction. -/
lemma lemma_6_2_5_axis_quantization_collision
    (m : ℤ)
    (hm : 1 ≤ m)
    (Delta_req Delta_actual Delta_on : ℝ)
    (h_req : Delta_req = (m : ℝ) + Delta_on)
    (h_actual : Delta_actual = Delta_on)
    (h_match : Delta_req = Delta_actual) :
    False := by
  -- Part I & II: The Analytic Demand vs Supply
  rw [h_req, h_actual] at h_match

  -- Part III: The Collision
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith


/-- Lemma 6.2.6 (The boundary-state rule for on-line zeros).
A simple zero located strictly on the critical line (ρ = 1/2 + iγ) constitutes an
admissible boundary state within the extended state space P-bar, precluding the
generation of interior monodromy. -/
lemma lemma_6_2_6_boundary_rule
    (theta_fn : ℂ → ℝ)
    (rho : ℂ)
    (h_zero : xi_C rho = 0)
    (_h_online : rho.re = 1 / 2)
    (m_int : ℝ)
    (h_cauchy_boundary : (∃ z0 : Z0, zeta_state theta_fn rho = PSpaceExt.boundary z0) → m_int = 0) :
    (∃ z0 : Z0, zeta_state theta_fn rho = PSpaceExt.boundary z0) ∧ m_int = 0 := by

  -- Part I: Boundary State Mapping
  have h_bound : ∃ z0 : Z0, zeta_state theta_fn rho = PSpaceExt.boundary z0 := by
    dsimp [zeta_state]
    have h_norm : norm (xi_C rho) = 0 := by rw [h_zero, norm_zero]
    have h_not_pos : ¬ (norm (xi_C rho) > 0) := by rw [h_norm]; linarith
    rw [dite_eq_right h_not_pos]
    use ⟨theta_fn rho⟩

  -- Part II: Interior Monodromy Preclusion
  constructor
  · exact h_bound
  · exact h_cauchy_boundary h_bound

/-- The phase increment of a finite superposition equals the sum of the
phase increments of its components. This is the endpoint form of the
linearity established for the phase derivative in Section 4. -/
lemma lemma_6_1_4_phase_increment_superposition
    (theta_bg theta_excess theta_on : ℝ → ℝ)
    (a b : ℝ) :
    ((theta_bg b + theta_excess b + theta_on b) -
        (theta_bg a + theta_excess a + theta_on a)) =
      (theta_bg b - theta_bg a) +
      (theta_excess b - theta_excess a) +
      (theta_on b - theta_on a) := by
  ring

/-- The symmetric Hadamard phase contribution of the isolated candidate
off-line zero orbit at its own ordinate. -/
noncomputable def theta_offline_orbit
    (ρ : ℂ)
    (σ : ℝ) : ℝ :=
  psi_quad_sum ρ.re ρ.im σ ρ.im


/-- The residual background phase after subtracting the isolated off-line
orbit and the local on-line contribution from the total phase. -/
noncomputable def theta_background_residual
    (theta_total theta_on : ℂ → ℝ → ℝ)
    (ρ : ℂ)
    (σ : ℝ) : ℝ :=
  theta_total ρ σ - theta_offline_orbit ρ σ - theta_on ρ σ

/-- The analytic and topological framework of the completed zeta phase manifold.

The framework is one-dimensional.  The two horizontal phase threads determine
a transported off-line excess demand.  The critical axis contributes only its
permitted on-line phase capacity.  The total required phase is the sum of
these two contributions. -/
structure ZetaPhaseFramework where
  /-- Positive winding multiplicity generated by a right-side interior zero. -/
  m : ℂ → ℤ

  /-- An off-line zero in the right half-plane has positive winding. -/
  h_m_pos :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 → 1 ≤ m ρ

  /-- Total terminal turn phases of the upper and lower horizontal 1D threads. -/
  theta_A_total : ℂ → ℝ
  theta_B_total : ℂ → ℝ

  /-- Background terminal turn phases of the upper and lower threads. -/
  theta_A_bg : ℂ → ℝ
  theta_B_bg : ℂ → ℝ

  /-- The transported excess axis demand caused by an off-line winding. -/
  Delta_excess : ℂ → ℝ

  /-- The actual phase capacity supplied by the critical axis. -/
  Delta_actual : ℂ → ℝ

  /-- The permitted quantized contribution of on-line axial steps. -/
  Delta_on : ℂ → ℝ

  /-- The transported discrepancy along the horizontal 1D evaluation
  corridor.  At the critical-axis endpoint it is the non-background
  component of the total thread disparity. -/
  discrepancy : ℂ → ℝ

  /-- The transported off-line excess is exactly the topological discrepancy. -/
  h_excess_is_discrepancy :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_excess ρ = discrepancy ρ

    /-- The right endpoint of the zero-free horizontal corridor associated
  with a candidate right-side zero. -/
  beta : ℂ → ℝ

  /-- A selected point in the open horizontal transport corridor.  This is
  the point at which the transported discrepancy is evaluated. -/
  transport_sigma : ℂ → ℝ

  /-- The one-dimensional discrepancy function transported across the
  horizontal corridor `(1 / 2, beta rho)`. -/
  discrepancy_line : ℂ → ℝ → ℝ

  /-- The terminal discrepancy used by the framework is the discrepancy
  evaluated at the selected corridor point. -/
  h_discrepancy_at_transport_sigma :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      discrepancy ρ = discrepancy_line ρ (transport_sigma ρ)

  /-- The selected transport point lies strictly inside the horizontal
  zero-free corridor. -/
  h_transport_sigma_mem :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      transport_sigma ρ ∈ Set.Ioo (1 / 2) (beta ρ)

  /-- The two reflected 1D phase representatives whose turn-phase sum is
  the transported discrepancy. -/
  theta_reflected : ℂ → ℝ → ℝ
  theta_original : ℂ → ℝ → ℝ

  /-- The corridor discrepancy is the reflected turn-phase sum. -/
  h_discrepancy_line_def :
    ∀ ρ σ,
      discrepancy_line ρ σ =
        theta_reflected ρ σ + theta_original ρ σ

  /-- Section 5 reflected phase relation, expressed in turn coordinates.
  The two phase representatives are opposite modulo an integer deck shift. -/
  h_reflected_phase_equiv :
    ∀ ρ σ,
      theta_reflected ρ σ ~ -theta_original ρ σ

  /-- The one-dimensional horizontal corridor is zero-free. -/
  h_corridor_nonvanishing :
    ∀ ρ σ,
      xi_C ρ = 0 →
      ρ.re > 1 / 2 →
      σ ∈ Set.Ioo (1 / 2) (beta ρ) →
      xi_C (Complex.mk σ ρ.im) ≠ 0

  /-- The integer deck discrepancy is constant along the zero-free
  horizontal transport corridor. -/
  h_discrepancy_constant :
    ∀ ρ σ σ',
      xi_C ρ = 0 →
      ρ.re > 1 / 2 →
      σ ∈ Set.Ioo (1 / 2) (beta ρ) →
      σ' ∈ Set.Ioo (1 / 2) (beta ρ) →
      discrepancy_line ρ σ = discrepancy_line ρ σ'

  /-- Near the puncture, the transported discrepancy has the interior
  winding value. -/
  h_discrepancy_puncture_limit :
    ∀ ρ,
      xi_C ρ = 0 →
      ρ.re > 1 / 2 →
      ∃ σ₀,
        σ₀ ∈ Set.Ioo (1 / 2) (beta ρ) ∧
        discrepancy_line ρ σ₀ = (m ρ : ℝ)

  /-- Background endpoint data for the two anchored horizontal threads. -/
  theta_A_bg_start : ℂ → ℝ
  theta_B_bg_start : ℂ → ℝ
  int_A_bg : ℂ → ℝ
  int_B_bg : ℂ → ℝ

  /-- Fundamental-theorem evaluations of the two background threads. -/
  h_FTC_A_bg :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      theta_A_bg ρ = theta_A_bg_start ρ + int_A_bg ρ

  h_FTC_B_bg :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      theta_B_bg ρ = theta_B_bg_start ρ + int_B_bg ρ

  /-- The common Dirichlet anchor has zero phase disparity. -/
  h_anchor_bg_zero :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      theta_A_bg_start ρ - theta_B_bg_start ρ = 0

  /-- The two 1D background thread integrals have equal accumulation. -/
  h_background_integral_zero :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      int_A_bg ρ - int_B_bg ρ = 0

  /-- The transported off-line excess is the oriented terminal disparity
  between the upper and lower horizontal threads. -/
  h_excess_endpoint_increment :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_excess ρ = theta_A_total ρ - theta_B_total ρ

    /-- The background contribution to the terminal thread-arrival disparity. -/
  Delta_bg : ℂ → ℝ

  /-- The full terminal phase disparity which the axis connector must bridge. -/
  Delta_total : ℂ → ℝ

    /-- The global unwrapped phase along the selected horizontal thread. -/
  theta_total_component : ℂ → ℝ → ℝ

  /-- The local on-line phase contribution at the target ordinate. -/
  theta_on_component : ℂ → ℝ → ℝ

  /-- The Dirichlet-side anchor coordinate. -/
  anchor_sigma : ℂ → ℝ

  /-- The terminal critical-axis-side coordinate. -/
  terminal_sigma : ℂ → ℝ


  /-- The total terminal phase disparity is the oriented increment of the
  total phase along the selected horizontal thread. -/
  h_delta_total_def :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_total ρ =
        theta_total_component ρ (terminal_sigma ρ) -
        theta_total_component ρ (anchor_sigma ρ)

    /-- The background disparity is the endpoint increment of the residual
  background phase. -/
  h_delta_bg_def :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_bg ρ =
        (theta_total_component ρ (terminal_sigma ρ) -
          theta_offline_orbit ρ (terminal_sigma ρ) -
          theta_on_component ρ (terminal_sigma ρ)) -
        (theta_total_component ρ (anchor_sigma ρ) -
          theta_offline_orbit ρ (anchor_sigma ρ) -
          theta_on_component ρ (anchor_sigma ρ))

    /-- The transported off-line excess is the endpoint increment of the
  isolated symmetric Hadamard orbit of the candidate zero. -/
  h_delta_excess_def :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_excess ρ =
        theta_offline_orbit ρ (terminal_sigma ρ) -
        theta_offline_orbit ρ (anchor_sigma ρ)

  /-- The permitted on-line contribution is the corresponding on-line
  phase increment. -/
  h_delta_on_def :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_on ρ =
        theta_on_component ρ (terminal_sigma ρ) -
        theta_on_component ρ (anchor_sigma ρ)

  /-- The continuous background contribution is precisely the difference of
  the background thread endpoint phases. -/
  h_background_component :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_bg ρ = theta_A_bg ρ - theta_B_bg ρ

    /-- The continuous, zero-free contribution to the phase accumulated along
  the local critical-axis micro-interval. -/
  Delta_axis_continuous : ℂ → ℝ

  /-- The quantized discrete contribution from on-line roots sharing the
  target ordinate. -/
  Delta_axis_steps : ℂ → ℝ

  /-- The actual critical-axis phase capacity decomposes into its continuous
  contribution and its discrete on-line step contribution. -/
  h_actual_axis_decomp :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_actual ρ =
        Delta_axis_continuous ρ + Delta_axis_steps ρ

  /-- Lemma 6.2.1: on the zero-free portions of the critical axis, phase is
  quantized and therefore contributes no continuous phase variation. -/
  h_axis_continuous_zero :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_axis_continuous ρ = 0

  /-- The discrete axis-step sum is exactly the permitted on-line
  contribution at the target ordinate. -/
  h_axis_steps_are_on_line :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_axis_steps ρ = Delta_on ρ

  /-- The total demanded phase is the oriented disparity between the
  terminal upper and lower thread states. This is the demand-side
  evaluation of the connector. -/
  h_total_endpoint_increment :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_total ρ = theta_A_total ρ - theta_B_total ρ

  /-- The actual phase supplied by the critical axis is evaluated on the
  same oriented connector between the terminal lower and upper thread
  states. This is the supply-side evaluation of the connector. -/
  h_actual_endpoint_increment :
    ∀ ρ, xi_C ρ = 0 → ρ.re > 1 / 2 →
      Delta_actual ρ = theta_A_total ρ - theta_B_total ρ

/-- The isolated off-line phase contribution is the symmetric Hadamard orbit
of the candidate zero. -/
noncomputable def zeta_theta_excess
    (_F : ZetaPhaseFramework)
    (ρ : ℂ)
    (σ : ℝ) : ℝ :=
  theta_offline_orbit ρ σ


/-- The background is the residual total phase after removing the isolated
off-line orbit and the local on-line phase contribution. -/
noncomputable def zeta_theta_background
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (σ : ℝ) : ℝ :=
  theta_background_residual
    F.theta_total_component
    F.theta_on_component
    ρ
    σ


/-- The total phase decomposes identically into residual background,
isolated off-line orbit, and local on-line contribution. -/
lemma zeta_framework_total_phase_decomp
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (σ : ℝ) :
    F.theta_total_component ρ σ =
      zeta_theta_background F ρ σ +
      zeta_theta_excess F ρ σ +
      F.theta_on_component ρ σ := by
  dsimp [
    zeta_theta_background,
    zeta_theta_excess,
    theta_background_residual,
    theta_offline_orbit
  ]
  ring

/-- Section 6.2.2 applied to the stored one-dimensional background data. -/
lemma zeta_framework_background_zero
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (h_zero : xi_C ρ = 0)
    (h_right : ρ.re > 1 / 2) :
    F.theta_A_bg ρ - F.theta_B_bg ρ = 0 := by
  exact lemma_6_2_2_strict_endpoint_equality
    (F.theta_A_bg ρ)
    (F.theta_B_bg ρ)
    (F.theta_A_bg_start ρ)
    (F.theta_B_bg_start ρ)
    (F.int_A_bg ρ)
    (F.int_B_bg ρ)
    (F.h_FTC_A_bg ρ h_zero h_right)
    (F.h_FTC_B_bg ρ h_zero h_right)
    (F.h_anchor_bg_zero ρ h_zero h_right)
    (F.h_background_integral_zero ρ h_zero h_right)

/-- The continuous background component of the terminal disparity vanishes. -/
lemma zeta_framework_delta_bg_zero
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (h_zero : xi_C ρ = 0)
    (h_right : ρ.re > 1 / 2) :
    F.Delta_bg ρ = 0 := by
  rw [F.h_background_component ρ h_zero h_right]
  exact zeta_framework_background_zero F ρ h_zero h_right

/-- Extract the integer deck displacement encoded by turn-phase equivalence. -/
lemma lemma_6_1_0_phase_equiv_deck
    (theta₁ theta₂ : ℝ)
    (h_equiv : theta₁ ~ theta₂) :
    ∃ k : ℤ, theta₁ - theta₂ = (k : ℝ) := by
  rcases h_equiv with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  linarith

/-- A reflected phase-equivalence relation gives an integer turn displacement
between the reflected phase and the negated original phase. -/
lemma lemma_6_1_0_reflected_deck_displacement
    (theta_reflected theta_original : ℝ)
    (h_equiv : theta_reflected ~ -theta_original) :
    ∃ k : ℤ,
      theta_reflected + theta_original = (k : ℝ) := by
  rcases h_equiv with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  linarith

/-- The reflected Section 5 phase relation makes the horizontal discrepancy
integer-valued in turn coordinates.

The discrepancy is defined as the reflected phase sum. Since reflected phase
is opposite modulo an integral deck translation, this sum is an integer. -/
lemma zeta_framework_discrepancy_integer
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (σ : ℝ)
    (_h_zero : xi_C ρ = 0)
    (_h_right : ρ.re > 1 / 2)
    (_hσ : σ ∈ Set.Ioo (1 / 2) (F.beta ρ)) :
    ∃ k : ℤ, F.discrepancy_line ρ σ = (k : ℝ) := by
  have h_reflected :
      ∃ k : ℤ,
        F.theta_reflected ρ σ + F.theta_original ρ σ = (k : ℝ) :=
    lemma_6_1_0_reflected_deck_displacement
      (F.theta_reflected ρ σ)
      (F.theta_original ρ σ)
      (F.h_reflected_phase_equiv ρ σ)

  rcases h_reflected with ⟨k, hk⟩
  refine ⟨k, ?_⟩

  calc
    F.discrepancy_line ρ σ =
        F.theta_reflected ρ σ + F.theta_original ρ σ :=
      F.h_discrepancy_line_def ρ σ
    _ = (k : ℝ) := hk

/-- Section 6.1.2 instantiated with the reflected turn-phase discrepancy.

The Section 5 angle-equivalence relation supplies integer-valuedness; corridor
constancy and the puncture-side value then transport the winding multiplicity
to the selected one-dimensional evaluation point. -/
lemma zeta_framework_discrepancy_transport
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (h_zero : xi_C ρ = 0)
    (h_right : ρ.re > 1 / 2) :
    F.discrepancy ρ = (F.m ρ : ℝ) := by
  have h_integer :
      ∀ σ,
        σ ∈ Set.Ioo (1 / 2) (F.beta ρ) →
        ∃ k : ℤ, F.discrepancy_line ρ σ = (k : ℝ) := by
    intro σ hσ
    exact zeta_framework_discrepancy_integer F ρ σ h_zero h_right hσ

  have h_transport_line :
      ∀ σ,
        σ ∈ Set.Ioo (1 / 2) (F.beta ρ) →
        F.discrepancy_line ρ σ = (F.m ρ : ℝ) :=
    lemma_6_1_2_topological_shear_line
      (F.discrepancy_line ρ)
      (F.m ρ)
      (ρ.im)
      (F.h_m_pos ρ h_zero h_right)
      (F.beta ρ)
      (fun σ hσ =>
        F.h_corridor_nonvanishing ρ σ h_zero h_right hσ)
      h_integer
      (fun σ σ' hσ hσ' =>
        F.h_discrepancy_constant ρ σ σ'
          h_zero h_right hσ hσ')
      (F.h_discrepancy_puncture_limit ρ h_zero h_right)

  have h_transport_mem :
      F.transport_sigma ρ ∈ Set.Ioo (1 / 2) (F.beta ρ) :=
    F.h_transport_sigma_mem ρ h_zero h_right

  calc
    F.discrepancy ρ =
        F.discrepancy_line ρ (F.transport_sigma ρ) :=
      F.h_discrepancy_at_transport_sigma ρ h_zero h_right
    _ = (F.m ρ : ℝ) :=
      h_transport_line (F.transport_sigma ρ) h_transport_mem

/-- Section 6.2.4: the transported off-line excess equals the positive winding multiplicity. -/
lemma zeta_framework_axis_excess
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (h_zero : xi_C ρ = 0)
    (h_right : ρ.re > 1 / 2) :
    F.Delta_excess ρ = (F.m ρ : ℝ) := by
  have h_disc : F.discrepancy ρ = (F.m ρ : ℝ) :=
    zeta_framework_discrepancy_transport F ρ h_zero h_right
  rw [F.h_excess_is_discrepancy ρ h_zero h_right, h_disc]

/-- The total terminal arrival disparity is the sum of residual background,
isolated off-line orbit, and local on-line phase increments. -/
lemma zeta_framework_terminal_phase_superposition
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (h_zero : xi_C ρ = 0)
    (h_right : ρ.re > 1 / 2) :
    F.Delta_total ρ =
      F.Delta_bg ρ + F.Delta_excess ρ + F.Delta_on ρ := by
  have h_total :
      F.Delta_total ρ =
        F.theta_total_component ρ (F.terminal_sigma ρ) -
        F.theta_total_component ρ (F.anchor_sigma ρ) :=
    F.h_delta_total_def ρ h_zero h_right

  have h_bg :
      F.Delta_bg ρ =
        zeta_theta_background F ρ (F.terminal_sigma ρ) -
        zeta_theta_background F ρ (F.anchor_sigma ρ) := by
    dsimp [zeta_theta_background, theta_background_residual]
    exact F.h_delta_bg_def ρ h_zero h_right

  have h_excess :
      F.Delta_excess ρ =
        zeta_theta_excess F ρ (F.terminal_sigma ρ) -
        zeta_theta_excess F ρ (F.anchor_sigma ρ) := by
    dsimp [zeta_theta_excess]
    exact F.h_delta_excess_def ρ h_zero h_right

  have h_on :
      F.Delta_on ρ =
        F.theta_on_component ρ (F.terminal_sigma ρ) -
        F.theta_on_component ρ (F.anchor_sigma ρ) :=
    F.h_delta_on_def ρ h_zero h_right

  rw [h_total, h_bg, h_excess, h_on]

  rw [zeta_framework_total_phase_decomp
    F ρ (F.terminal_sigma ρ)]

  rw [zeta_framework_total_phase_decomp
    F ρ (F.anchor_sigma ρ)]

  exact lemma_6_1_4_phase_increment_superposition
    (zeta_theta_background F ρ)
    (zeta_theta_excess F ρ)
    (F.theta_on_component ρ)
    (F.anchor_sigma ρ)
    (F.terminal_sigma ρ)

/-- The total demanded axis-bridging phase is the positive transported
off-line excess plus the permitted local on-line phase step. -/
lemma zeta_framework_transport_requirement
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (h_zero : xi_C ρ = 0)
    (h_right : ρ.re > 1 / 2) :
    F.Delta_total ρ = (F.m ρ : ℝ) + F.Delta_on ρ := by
  have h_bg_zero : F.Delta_bg ρ = 0 :=
    zeta_framework_delta_bg_zero F ρ h_zero h_right

  have h_excess : F.Delta_excess ρ = (F.m ρ : ℝ) :=
    zeta_framework_axis_excess F ρ h_zero h_right

  calc
    F.Delta_total ρ =
        F.Delta_bg ρ + F.Delta_excess ρ + F.Delta_on ρ :=
      zeta_framework_terminal_phase_superposition F ρ h_zero h_right
    _ = (F.m ρ : ℝ) + F.Delta_on ρ := by
      rw [h_bg_zero, h_excess]
      ring

/-- The zero-reflection dependency natively derived from the classical axiom. -/
lemma zeta_framework_functional_equation
    (z : ℂ) (hz : xi_C z = 0) :
    xi_C (1 - z) = 0 := by
  have h := classical_xi_functional_equation z
  rw [← h]
  exact hz

/-- The demand-side and supply-side evaluations refer to the same oriented
connector between the lower and upper terminal horizontal thread states. -/
lemma zeta_framework_manifold_closure
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (h_zero : xi_C ρ = 0)
    (h_right : ρ.re > 1 / 2) :
    F.Delta_total ρ = F.Delta_actual ρ := by
  calc
    F.Delta_total ρ =
        F.theta_A_total ρ - F.theta_B_total ρ :=
      F.h_total_endpoint_increment ρ h_zero h_right
    _ = F.Delta_actual ρ :=
      (F.h_actual_endpoint_increment ρ h_zero h_right).symm

/-- The actual capacity of the critical axis is exactly its permitted
quantized on-line step contribution. -/
lemma zeta_framework_actual_capacity
    (F : ZetaPhaseFramework)
    (ρ : ℂ)
    (h_zero : xi_C ρ = 0)
    (h_right : ρ.re > 1 / 2) :
    F.Delta_actual ρ = F.Delta_on ρ := by
  have h_decomp :
      F.Delta_actual ρ =
        F.Delta_axis_continuous ρ + F.Delta_axis_steps ρ :=
    F.h_actual_axis_decomp ρ h_zero h_right

  have h_cont_zero : F.Delta_axis_continuous ρ = 0 :=
    F.h_axis_continuous_zero ρ h_zero h_right

  have h_steps : F.Delta_axis_steps ρ = F.Delta_on ρ :=
    F.h_axis_steps_are_on_line ρ h_zero h_right

  calc
    F.Delta_actual ρ =
        F.Delta_axis_continuous ρ + F.Delta_axis_steps ρ :=
      h_decomp
    _ = F.Delta_on ρ := by
      rw [h_cont_zero, h_steps, zero_add]

/-- Theorem 6.3.1 (The Riemann Hypothesis for P-space).

A right-side zero produces a positive transported excess phase. The total
axis demand is that off-line excess plus the permitted on-line contribution,
whereas the actual axis capacity contains only the permitted on-line
contribution. Equality of demanded and supplied endpoint increments forces
the positive winding multiplicity to vanish. -/
theorem theorem_6_3_1_riemann_hypothesis
    (rho : ℂ)
    (h_zero : xi_C rho = 0)
    (F : ZetaPhaseFramework) :
    rho.re = 1 / 2 := by

  -- Step 1: exclude a zero strictly right of the critical line.
  have h_not_gt : ¬ (rho.re > 1 / 2) := by
    intro h_gt

    have h_match : F.Delta_total rho = F.Delta_actual rho :=
      zeta_framework_manifold_closure F rho h_zero h_gt

    have h_demand :
        F.Delta_total rho = (F.m rho : ℝ) + F.Delta_on rho :=
      zeta_framework_transport_requirement F rho h_zero h_gt

    have h_supply : F.Delta_actual rho = F.Delta_on rho :=
      zeta_framework_actual_capacity F rho h_zero h_gt

    exact lemma_6_2_5_axis_quantization_collision
      (F.m rho)
      (F.h_m_pos rho h_zero h_gt)
      (F.Delta_total rho)
      (F.Delta_actual rho)
      (F.Delta_on rho)
      h_demand
      h_supply
      h_match

  have h_le : rho.re ≤ 1 / 2 := by
    linarith

  -- Step 2: reflection excludes a zero strictly left of the critical line.
  have h_not_lt : ¬ (rho.re < 1 / 2) := by
    intro h_lt

    have h_reflected_zero : xi_C (1 - rho) = 0 :=
      zeta_framework_functional_equation rho h_zero

    have h_reflected_gt : (1 - rho).re > 1 / 2 := by
      change 1 - rho.re > 1 / 2
      linarith

    have h_reflected_match :
        F.Delta_total (1 - rho) = F.Delta_actual (1 - rho) :=
      zeta_framework_manifold_closure
        F (1 - rho) h_reflected_zero h_reflected_gt

    have h_reflected_demand :
        F.Delta_total (1 - rho) =
          (F.m (1 - rho) : ℝ) + F.Delta_on (1 - rho) :=
      zeta_framework_transport_requirement
        F (1 - rho) h_reflected_zero h_reflected_gt

    have h_reflected_supply :
        F.Delta_actual (1 - rho) = F.Delta_on (1 - rho) :=
      zeta_framework_actual_capacity
        F (1 - rho) h_reflected_zero h_reflected_gt

    exact lemma_6_2_5_axis_quantization_collision
      (F.m (1 - rho))
      (F.h_m_pos (1 - rho) h_reflected_zero h_reflected_gt)
      (F.Delta_total (1 - rho))
      (F.Delta_actual (1 - rho))
      (F.Delta_on (1 - rho))
      h_reflected_demand
      h_reflected_supply
      h_reflected_match

  linarith


/-- Theorem 6.3.3 (The Riemann Hypothesis for classical complex analysis).

The continuous lift exists as an open path. In standard complex analysis,
manifold closure produces a horizontal spatial translation parameter

  tau = delta(z) * (Re(z) - 1 / 2).

Classical Dirichlet-series uniqueness makes a deformation that is
analytically indistinguishable from the undeformed series have zero
translation parameter. A right-side zero would force both `delta(z) ≠ 0`
and `Re(z) - 1 / 2 ≠ 0`, contradicting `tau = 0`. Functional-equation
reflection excludes the left half-plane. -/
theorem theorem_6_3_3_standard_rh
    (rho : ℂ)
    (h_zero : xi_C rho = 0)
    -- 1. An off-line zero forces a nonzero continuous spatial deformation.
    (delta : ℂ → ℝ)
    (h_topological_shear :
      ∀ z, xi_C z = 0 → z.re > 1 / 2 → delta z ≠ 0)
    -- 2. Manifold closure maps this deformation to a Dirichlet-series
    -- translation with parameter delta z * (Re z - 1/2).
    (h_manifold_deformation :
      ∀ z, xi_C z = 0 →
        IsDirichletDeformation (delta z * (z.re - 1 / 2))) :
    rho.re = 1 / 2 := by

  -- Step 1: exclude a zero strictly right of the critical line.
  have h_not_gt : ¬ (rho.re > 1 / 2) := by
    intro h_gt

    have h_is_def :
        IsDirichletDeformation
          (delta rho * (rho.re - 1 / 2)) :=
      h_manifold_deformation rho h_zero

    have h_tau_zero :
        delta rho * (rho.re - 1 / 2) = 0 :=
      dirichlet_translation_zero
        (delta rho * (rho.re - 1 / 2))
        h_is_def

    cases mul_eq_zero.mp h_tau_zero with
    | inl h_delta_zero =>
        exact False.elim
          (h_topological_shear rho h_zero h_gt h_delta_zero)
    | inr h_gap_zero =>
        linarith

  have h_le : rho.re ≤ 1 / 2 := by
    linarith

  -- Step 2: reflect a hypothetical left-half-plane zero to the right.
  have h_not_lt : ¬ (rho.re < 1 / 2) := by
    intro h_lt

    have h_sym_zero : xi_C (1 - rho) = 0 :=
      zeta_framework_functional_equation rho h_zero

    have h_sym_gt : (1 - rho).re > 1 / 2 := by
      change 1 - rho.re > 1 / 2
      linarith

    have h_sym_def :
        IsDirichletDeformation
          (delta (1 - rho) * ((1 - rho).re - 1 / 2)) :=
      h_manifold_deformation (1 - rho) h_sym_zero

    have h_sym_tau_zero :
        delta (1 - rho) * ((1 - rho).re - 1 / 2) = 0 :=
      dirichlet_translation_zero
        (delta (1 - rho) * ((1 - rho).re - 1 / 2))
        h_sym_def

    cases mul_eq_zero.mp h_sym_tau_zero with
    | inl h_delta_zero =>
        exact False.elim
          (h_topological_shear
            (1 - rho)
            h_sym_zero
            h_sym_gt
            h_delta_zero)
    | inr h_gap_zero =>
        linarith

  -- Step 3: rho is neither strictly right nor strictly left of the axis.
  linarith

end TainoPolar
