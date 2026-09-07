/-
Copyright (c) 2026 Richard Andrew Rodriguez.
Released under the MIT license.
Manuscript DOI: 10.5281/zenodo.22559147
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta


namespace TainoPolar


/--
Axiom 1.1: State space
The state space 𝒫 enforces strictly unsigned magnitude alongside continuous phase.
-/
structure PSpace where
  mag   : {a : ℝ // a > 0}
  phase : ℝ


/--
Axiom 1.1.1: Extended state space boundary 𝒵_0.
Restricted exclusively to states with exactly 0 magnitude.
-/
structure Z0 where
  phase : ℝ


inductive PSpaceExt where
  | interior (p : PSpace) : PSpaceExt
  | boundary (z : Z0) : PSpaceExt



/--
Axiom 1.2: Magnitude map
Negative phases enforce an inverse of the magnitude.


*NOTE: We will be staying in double bracket notation for the proof.
The single bracket notation map is just an evaluation convention.*
-/
noncomputable def singleBracket (a : {r : ℝ // r > 0}) (x : ℝ) : PSpace :=
  if 0 ≤ x then
    PSpace.mk a x
  else
    let inv_a : {r : ℝ // r > 0} := ⟨1 / a.val, div_pos zero_lt_one a.property⟩
    PSpace.mk inv_a x


/--
Axiom 1.3: Strict equality
Strict equality denotes when the magnitude and phase are the same.
-/
def StrictEq (p q : PSpace) : Prop :=
  p.mag = q.mag ∧ p.phase = q.phase


infix:50 " ≡ " => StrictEq


lemma StrictEq.refl (p : PSpace) : p ≡ p := ⟨rfl, rfl⟩
lemma StrictEq.symm {p q : PSpace} (h : p ≡ q) : q ≡ p := ⟨h.1.symm, h.2.symm⟩
lemma StrictEq.trans {p q r : PSpace} (h1 : p ≡ q) (h2 : q ≡ r) : p ≡ r :=
  ⟨Eq.trans h1.1 h2.1, Eq.trans h1.2 h2.2⟩


lemma strict_eq (p q : PSpace) : p = q ↔ p.mag = q.mag ∧ p.phase = q.phase := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    cases p
    cases q
    dsimp at h1 h2
    subst h1 h2
    rfl


/--
Axiom 1.4: Double bracket notation
-/
scoped notation "⟦" a ", " x "⟧" => PSpace.mk a x


def m_double (p : PSpace) : {r : ℝ // r > 0} := p.mag


/--
Axiom 1.5: Phase equivalence
x ∼ y ⟺ (x mod 1) = (y mod 1)
-/
noncomputable def angle_equiv (x y : ℝ) : Prop :=
  Int.fract x = Int.fract y


scoped infix:50 " ∼ " => angle_equiv


/--
Axiom 1.6: Polar equivalence
[a,x] ≈ [b,y] ⟺ a' = b' ∧ x ∼ y
-/
noncomputable def polar_equiv (p q : PSpace) : Prop :=
  p.mag = q.mag ∧ p.phase ∼ q.phase


scoped infix:50 " ≈ " => polar_equiv


/--
Axiom 1.7: Projection to standard form
π : 𝒫 → ℂ*
-/
noncomputable def proj (p : PSpace) : ℂ :=
  (p.mag.val : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (p.phase : ℂ))


/--
Axiom 1.17: Base-to-fiber gauge normalization
-/
noncomputable def gauge_theta (X Y : ℝ) : ℝ :=
  if X > 0 ∧ Y ≥ 0 then Real.arctan (Y / X)
  else if X < 0 then Real.arctan (Y / X) + Real.pi
  else if X > 0 ∧ Y < 0 then Real.arctan (Y / X) + 2 * Real.pi
  else if X = 0 ∧ Y > 0 then Real.pi / 2
  else if X = 0 ∧ Y < 0 then 3 * Real.pi / 2
  else 0


/--
Axiom 1.7: Base-to-fiber gauge projection
-/
noncomputable def gauge_projection (Z : ℂ) (n : ℤ) : PSpaceExt :=
  let X := Z.re
  let Y := Z.im
  let r := Real.sqrt (X^2 + Y^2)
  let θ := gauge_theta X Y
  let phase_val := (θ / (2 * Real.pi)) + (n : ℝ)

  if hr : r > 0 then
    PSpaceExt.interior ⟦⟨r, hr⟩, phase_val⟧
  else
    PSpaceExt.boundary { phase := phase_val }


scoped notation "π" => proj


/--
Axiom 1.8: Addition
-/
noncomputable def add_rel (p q r : PSpace) : Prop :=
  ∀ t : ℝ, p.mag.val * Real.sin (t + 2 * Real.pi * p.phase) +
           q.mag.val * Real.sin (t + 2 * Real.pi * q.phase) =
           r.mag.val * Real.sin (t + 2 * Real.pi * r.phase)


/--
Axiom 1.8.1: Negation
-/
noncomputable def neg_state (p : PSpace) : PSpace :=
  ⟦p.mag, p.phase + (1 / 2 : ℝ)⟧


/--
Axiom 1.8.2: Subtraction
-/
noncomputable def sub_rel (p q r : PSpace) : Prop :=
  add_rel p (neg_state q) r


/--
Axiom 1.9: Multiplication
-/
noncomputable def mul_state (p q : PSpace) : PSpace :=
  let new_mag : {r : ℝ // r > 0} :=
    ⟨p.mag.val * q.mag.val, mul_pos p.mag.property q.mag.property⟩
  ⟦new_mag, p.phase + q.phase⟧


/--
Axiom 1.9.1: Division
-/
noncomputable def div_state (p q : PSpace) : PSpace :=
  let new_mag : {r : ℝ // r > 0} :=
    ⟨p.mag.val / q.mag.val, div_pos p.mag.property q.mag.property⟩
  ⟦new_mag, p.phase - q.phase⟧


/--
Axiom 1.9.2: Inverse phase
-/
noncomputable def inv_phase_state (p : PSpace) : PSpace :=
  ⟦p.mag, - p.phase⟧

/-- Fundamental involution property of P-Space projection.
Proves natively that complex conjugation of the projected state perfectly
equals the projection of the phase-inverted state. -/
lemma pspace_involution (p : PSpace) : star (proj p) = proj (inv_phase_state p) := by
  dsimp [proj, inv_phase_state]

  -- 1. Align the exponents exactly into a single coerced real variable
  have h_exp1 : 2 * ↑Real.pi * Complex.I * ↑p.phase = ↑(2 * Real.pi * p.phase) * Complex.I := by
    push_cast
    ring
  have h_exp2 : 2 * ↑Real.pi * Complex.I * ↑(-p.phase) = ↑(- (2 * Real.pi * p.phase)) * Complex.I := by
    push_cast
    ring

  rw [h_exp1, h_exp2]

  -- 2. Expand strict complex equality into Real and Imaginary components
  apply Complex.ext
  · -- Real part: (star z).re is definitionally z.re
    change (↑p.mag.val * Complex.exp (↑(2 * Real.pi * p.phase) * Complex.I)).re =
           (↑p.mag.val * Complex.exp (↑(- (2 * Real.pi * p.phase)) * Complex.I)).re
    rw [Complex.exp_mul_I, Complex.exp_mul_I]

    -- Generalize the phase angle to completely lock the coercions safely inside θ
    generalize (2 * Real.pi * p.phase) = θ

    calc (↑p.mag.val * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I)).re
      _ = (↑p.mag.val : ℂ).re * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).re - (↑p.mag.val : ℂ).im * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).im := by rw [Complex.mul_re]
      _ = p.mag.val * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).re - 0 * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).im := by simp only [Complex.ofReal_re, Complex.ofReal_im]
      _ = p.mag.val * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).re := by ring
      _ = p.mag.val * ((Complex.cos ↑θ).re + (Complex.sin ↑θ * Complex.I).re) := by rw [Complex.add_re]
      _ = p.mag.val * ((Complex.cos ↑θ).re + ((Complex.sin ↑θ).re * Complex.I.re - (Complex.sin ↑θ).im * Complex.I.im)) := by rw [Complex.mul_re]
      _ = p.mag.val * ((Complex.cos ↑θ).re + ((Complex.sin ↑θ).re * 0 - (Complex.sin ↑θ).im * 1)) := by simp only [Complex.I_re, Complex.I_im]
      _ = p.mag.val * ((Complex.cos ↑θ).re - (Complex.sin ↑θ).im) := by ring
      _ = p.mag.val * Real.cos θ := by rw [Complex.cos_ofReal_re, Complex.sin_ofReal_im, sub_zero]
      _ = p.mag.val * Real.cos (-θ) := by rw [Real.cos_neg]
      _ = p.mag.val * ((Complex.cos ↑(-θ)).re - (Complex.sin ↑(-θ)).im) := by rw [Complex.cos_ofReal_re, Complex.sin_ofReal_im, sub_zero]
      _ = p.mag.val * ((Complex.cos ↑(-θ)).re + ((Complex.sin ↑(-θ)).re * 0 - (Complex.sin ↑(-θ)).im * 1)) := by ring
      _ = p.mag.val * ((Complex.cos ↑(-θ)).re + ((Complex.sin ↑(-θ)).re * Complex.I.re - (Complex.sin ↑(-θ)).im * Complex.I.im)) := by simp only [Complex.I_re, Complex.I_im]
      _ = p.mag.val * ((Complex.cos ↑(-θ)).re + (Complex.sin ↑(-θ) * Complex.I).re) := by rw [← Complex.mul_re]
      _ = p.mag.val * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).re := by rw [← Complex.add_re]
      _ = p.mag.val * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).re - 0 * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).im := by ring
      _ = (↑p.mag.val : ℂ).re * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).re - (↑p.mag.val : ℂ).im * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).im := by simp only [Complex.ofReal_re, Complex.ofReal_im]
      _ = (↑p.mag.val * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I)).re := by rw [← Complex.mul_re]

  · -- Imaginary part: (star z).im is definitionally -z.im
    change -(↑p.mag.val * Complex.exp (↑(2 * Real.pi * p.phase) * Complex.I)).im =
           (↑p.mag.val * Complex.exp (↑(- (2 * Real.pi * p.phase)) * Complex.I)).im
    rw [Complex.exp_mul_I, Complex.exp_mul_I]

    generalize (2 * Real.pi * p.phase) = θ

    calc -(↑p.mag.val * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I)).im
      _ = -((↑p.mag.val : ℂ).re * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).im + (↑p.mag.val : ℂ).im * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).re) := by rw [Complex.mul_im]
      _ = -(p.mag.val * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).im + 0 * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).re) := by simp only [Complex.ofReal_re, Complex.ofReal_im]
      _ = -(p.mag.val * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).im) := by ring
      _ = -(p.mag.val * ((Complex.cos ↑θ).im + (Complex.sin ↑θ * Complex.I).im)) := by rw [Complex.add_im]
      _ = -(p.mag.val * ((Complex.cos ↑θ).im + ((Complex.sin ↑θ).re * Complex.I.im + (Complex.sin ↑θ).im * Complex.I.re))) := by rw [Complex.mul_im]
      _ = -(p.mag.val * ((Complex.cos ↑θ).im + ((Complex.sin ↑θ).re * 1 + (Complex.sin ↑θ).im * 0))) := by simp only [Complex.I_re, Complex.I_im]
      _ = -(p.mag.val * ((Complex.cos ↑θ).im + (Complex.sin ↑θ).re)) := by ring
      _ = -(p.mag.val * (0 + Real.sin θ)) := by rw [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
      _ = p.mag.val * -Real.sin θ := by ring
      _ = p.mag.val * Real.sin (-θ) := by rw [Real.sin_neg]
      _ = p.mag.val * (0 + Real.sin (-θ)) := by ring
      _ = p.mag.val * ((Complex.cos ↑(-θ)).im + (Complex.sin ↑(-θ)).re) := by rw [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
      _ = p.mag.val * ((Complex.cos ↑(-θ)).im + ((Complex.sin ↑(-θ)).re * 1 + (Complex.sin ↑(-θ)).im * 0)) := by ring
      _ = p.mag.val * ((Complex.cos ↑(-θ)).im + ((Complex.sin ↑(-θ)).re * Complex.I.im + (Complex.sin ↑(-θ)).im * Complex.I.re)) := by simp only [Complex.I_re, Complex.I_im]
      _ = p.mag.val * ((Complex.cos ↑(-θ)).im + (Complex.sin ↑(-θ) * Complex.I).im) := by rw [← Complex.mul_im]
      _ = p.mag.val * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).im := by rw [← Complex.add_im]
      _ = p.mag.val * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).im + 0 * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).re := by ring
      _ = (↑p.mag.val : ℂ).re * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).im + (↑p.mag.val : ℂ).im * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I).re := by simp only [Complex.ofReal_re, Complex.ofReal_im]
      _ = (↑p.mag.val * (Complex.cos ↑(-θ) + Complex.sin ↑(-θ) * Complex.I)).im := by rw [← Complex.mul_im]

/--
Axiom 1.10: Exponentiation
-/
noncomputable def exp_state (p q : PSpace) : PSpace :=
  have new_mag_pos : p.mag.val ^ q.mag.val > 0 :=
    Real.rpow_pos_of_pos p.mag.property q.mag.val
  let new_mag : {r : ℝ // r > 0} := ⟨p.mag.val ^ q.mag.val, new_mag_pos⟩
  ⟦new_mag, q.mag.val * q.phase * p.phase⟧


/--
Axiom 1.11: Topology
𝒫 is equipped with the product topology from ℝ_{>0} × ℝ.
-/
noncomputable instance : TopologicalSpace PSpace :=
  TopologicalSpace.induced (fun p => (p.mag, p.phase)) inferInstance


universe u


/--
Axiom 1.13 & 1.14: Covering map condition & Evenly covered neighborhood
-/
def IsEvenlyCovered {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (U : Set B) : Prop :=
  IsOpen U ∧ ∃ (ι : Type u) (V : ι → Set E),
    (∀ i, IsOpen (V i)) ∧
    (Pairwise (fun i j => Disjoint (V i) (V j))) ∧
    (p ⁻¹' U = ⋃ i, V i) ∧
    (∀ i, ∃ f : V i ≃ U, Continuous f ∧ Continuous f.symm ∧
      ∀ x : V i, p x.val = (f x).val)


def IsCoveringMap_manual {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) : Prop :=
  Continuous p ∧ Function.Surjective p ∧
    ∀ b : B, ∃ U : Set B, b ∈ U ∧ IsEvenlyCovered p U


/--
Axiom 1.15: Lift condition
-/
def IsLift {X E B : Type*} (p : E → B) (f : X → B) (f_tilde : X → E) : Prop :=
  p ∘ f_tilde = f

/--
Axiom 1.16: Uniqueness of lift

Hatcher, *Algebraic Topology*, Proposition 1.34 (Unique Lifting Property).

Let `p : E → B` be a covering map and let `f : X → B` be continuous.
If two continuous lifts of `f` through `p` agree at one point of the
connected domain `X`, then they agree everywhere on `X`.

This theorem is imported as an external covering-space fact for the
project's manual interface `IsCoveringMap_manual`.
-/
axiom unique_lift {X E B : Type u} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace B] [ConnectedSpace X]
  (p : E → B) (f : X → B) (f_tilde1 f_tilde2 : X → E)
  (hp : IsCoveringMap_manual p)
  (hlift1 : IsLift p f f_tilde1)
  (hlift2 : IsLift p f f_tilde2)
  (hcont1 : Continuous f_tilde1)
  (hcont2 : Continuous f_tilde2)
  (x0 : X)
  (h_base : f_tilde1 x0 = f_tilde2 x0) :
  f_tilde1 = f_tilde2



/--
CLASSICAL ANALYTIC FOUNDATIONS

Classical Riemann zeta function.

The Dirichlet series `∑ n ≥ 1, n⁻ˢ` converges absolutely exactly when
`Re(s) > 1`.
See, e.g., Titchmarsh, *The Theory of the Riemann Zeta-Function*, Ch. II.

The ordinary Riemann zeta function, implemented by Mathlib.
-/
noncomputable def zeta_C : ℂ → ℂ :=
  riemannZeta

/--
Mathlib's auxiliary pole-removed completed Riemann zeta function variant (completedRiemannZeta₀).
-/
noncomputable def xi_C : ℂ → ℂ :=
  completedRiemannZeta₀


/--
Absolute convergence of the ordinary Riemann zeta Dirichlet series.
Defined natively via Mathlib's Summable property on the shifted natural sequence.
-/
def IsAbsolutelyConvergentZeta (s : ℂ) : Prop :=
  Summable (fun (n : ℕ) => ‖((n + 1 : ℂ) ^ (-s))‖)


/--
Classical abscissa-of-absolute-convergence theorem for the Riemann zeta
Dirichlet series. See Titchmarsh, *The Theory of the Riemann Zeta-Function*,
Ch. II.
-/
axiom classical_zeta_convergence (s : ℂ) :
  IsAbsolutelyConvergentZeta s ↔ 1 < s.re


theorem classical_xi_functional_equation (s : ℂ) :
    xi_C s = xi_C (1 - s) := by
  simpa [xi_C] using (completedRiemannZeta₀_one_sub s).symm

/--
Classical Schwarz reflection principle for the completed Riemann zeta function.

Because ξ(s) is entire and strictly real-valued on the real axis, the Schwarz
reflection principle rigorously guarantees ξ(s̅) = ξ(s)̅.
See E.C. Titchmarsh, "The Theory of the Riemann Zeta-Function" (1986), Section 2.1.
-/
axiom classical_xi_schwarz (s : ℂ) : xi_C (star s) = star (xi_C s)

/--
Classical Zeta Lower Bound (Euler Product Estimate).
For `Re(s) = σ₀ > 1`, the absolutely convergent Euler product establishes a
strictly positive uniform lower bound independent of `t`
(e.g., via `|ζ(σ+it)| ≥ ζ(2σ)/ζ(σ) > 0`).
-/
axiom classical_zeta_lower_bound (σ₀ : ℝ) (h_gt : 1 < σ₀) :
  ∃ m > 0, ∀ t : ℝ,
    m ≤ norm (zeta_C (Complex.mk σ₀ t))

/--
Classical Zeta Derivative Upper Bound.
For `Re(s) = σ₀ > 1`, the termwise differentiated Dirichlet series
`-∑ (log n) n^{-s}` converges absolutely and uniformly, establishing a finite
global upper bound `M` for the spatial derivative along the vertical line.
-/
axiom classical_zeta_deriv_upper_bound (σ₀ : ℝ) (h_gt : 1 < σ₀) :
  ∃ M > 0, ∀ t : ℝ,
    norm (deriv zeta_C (Complex.mk σ₀ t)) ≤ M

/--
Classical strict bounds of the real Riemann zeta function.
For evaluation lines σ₀ ≥ 2, the real zeta function is strictly bounded:
1 < ζ(σ₀) < 2. Therefore, the geometric Dirichlet disk radius (ζ(σ₀) - 1)
is strictly positive and strictly less than 1, allowing proper arcsin bounding.
-/
axiom classical_zeta_real_bounds (σ₀ : ℝ) (h_ge : 2 ≤ σ₀) :
  (0 < (zeta_C σ₀).re - 1) ∧ ((zeta_C σ₀).re - 1 < 1)

/-- Classical strict upper bound for the arcsin function. -/
lemma classical_arcsin_strict (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) : Real.arcsin x < Real.pi / 2 := by
  -- 1. Mathlib's universal upper bound for arcsin is π / 2
  have h_bound : Real.arcsin x ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x

  -- 2. Proceed by contradiction: assume arcsin x is NOT strictly less than π / 2
  by_contra h_not_lt

  -- 3. If it is bounded by π / 2 but not less than it, it must be exactly equal
  have h_eq : Real.arcsin x = Real.pi / 2 := by linarith

  -- 4. Take the sine of both sides of the false equality
  have h_sin : Real.sin (Real.arcsin x) = Real.sin (Real.pi / 2) := by rw [h_eq]

  -- 5. Evaluate the right side natively: sin(π/2) = 1
  have h_sin_pi : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  rw [h_sin_pi] at h_sin

  -- 6. Evaluate the left side natively: sin(arcsin(x)) = x
  have h_sin_arcsin : Real.sin (Real.arcsin x) = x := by
    apply Real.sin_arcsin
    · linarith  -- Goal 1: Proves -1 ≤ x (since 0 ≤ x)
    · linarith  -- Goal 2: Proves x ≤ 1 (since x < 1)

  rw [h_sin_arcsin] at h_sin

  -- 7. The equality now explicitly states x = 1, violating hypothesis hx1 (x < 1).
  linarith

open Classical

/--
Classical uniqueness theorem for ordinary Dirichlet series.

If a real translation `tau` leaves the Dirichlet series analytically
indistinguishable from the original series in a common half-plane of
absolute convergence, then by the identity theorem for Dirichlet series,
every corresponding Dirichlet coefficient must remain strictly unchanged.
Specifically for the von Mangoldt function Λ(n), this requires:
Λ(n) * Real.exp(-tau * Real.log n) = Λ(n).

Citations:
1. G.H. Hardy and M. Riesz, "The General Theory of Dirichlet's Series" (1915).
   Theorem 4 establishes the fundamental uniqueness of Dirichlet coefficients:
   if two Dirichlet series converge to the same analytic function in a shared
   half-plane, their respective coefficients are identically equal.
2. E.C. Titchmarsh, "The Theory of the Riemann Zeta-Function" (1986), Section 2.1.
   Validates the analytical properties, half-plane absolute convergence constraints,
   and logarithmic derivative identities specific to the Riemann zeta function.


Native mathematical definition of the classical von Mangoldt function Λ(n).
For formal semantic completeness, this binds the symbol to its actual arithmetic
behavior (Λ(n) = log p if n = p^k, 0 otherwise), eradicating the 'opaque' keyword.
-/
noncomputable def vonMangoldt (n : ℕ) : ℝ :=
  if ∃ (p k : ℕ), Nat.Prime p ∧ k ≥ 1 ∧ n = p ^ k then
    Real.log (Nat.minFac n : ℝ)
  else
    0

/-- Classical special value: Λ(2) = log 2. -/
lemma classical_vonMangoldt_two : vonMangoldt 2 = Real.log 2 := by
  unfold vonMangoldt
  have h_exists : ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ 2 = p ^ k := by
    refine ⟨2, 1, Nat.prime_two, by norm_num, ?_⟩
    norm_num
  split
  · norm_num
  · contradiction

/-- Proven natively from the classical value. -/
lemma classical_vonMangoldt_two_ne_zero : vonMangoldt 2 ≠ 0 := by
  rw [classical_vonMangoldt_two]
  exact ne_of_gt (Real.log_pos (by norm_num))

noncomputable def dirichletTerm (a : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else a n * (n : ℂ) ^ (-s)

/--
Condition for Dirichlet series uniqueness:
Two Dirichlet series converge on a right half-plane and their sums are identically equal.
-/
def DirichletSeriesAgreeOnHalfPlane (a b : ℕ → ℂ) : Prop :=
  ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
    Summable (dirichletTerm a s) ∧
    Summable (dirichletTerm b s) ∧
    tsum (dirichletTerm a s) = tsum (dirichletTerm b s)

/--
Classical uniqueness theorem for ordinary Dirichlet series:
If two convergent Dirichlet series agree on a right half-plane,
their coefficients agree identically.
-/
axiom classical_dirichlet_series_uniqueness (a b : ℕ → ℂ)
    (h_agree : DirichletSeriesAgreeOnHalfPlane a b) :
    ∀ n : ℕ, 1 ≤ n → a n = b n

/-- Project Dirichlet series formed from the native von Mangoldt definition. -/
noncomputable def logZetaCoeff (n : ℕ) : ℂ :=
  if n = 0 then 0 else (vonMangoldt n : ℂ)

noncomputable def translatedLogZetaCoeff (tau : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (vonMangoldt n : ℂ) *
      ((Real.exp (-tau * Real.log (n : ℝ))) : ℂ)

/--
Project predicate for Dirichlet series invariance.
-/
def IsDirichletSeriesInvariantUnderTranslation (tau : ℝ) : Prop :=
  DirichletSeriesAgreeOnHalfPlane logZetaCoeff (translatedLogZetaCoeff tau)

/--
Project interface: Indicates that the n-th coefficient of the Dirichlet series is strictly non-zero.
We define this formally as the classical von Mangoldt function being non-zero for n ≥ 1.
-/
def HasNonZeroCoefficient (n : ℕ) : Prop := 1 ≤ n ∧ vonMangoldt n ≠ 0

/--
Project interface lemma: The coefficient for n = 2 is non-zero.
Proven natively from the classical fact that Λ(2) ≠ 0.
-/
lemma coefficient_two_non_zero : HasNonZeroCoefficient 2 :=
  ⟨by norm_num, classical_vonMangoldt_two_ne_zero⟩

/--
Project interface lemma: Translation invariance forces the multiplier to be 1 for non-zero coefficients.
Proven natively from the classical uniqueness theorem for Dirichlet series.
-/
lemma classical_dirichlet_translation_coefficients
    (tau : ℝ)
    (h_inv : IsDirichletSeriesInvariantUnderTranslation tau)
    (n : ℕ)
    (hn : HasNonZeroCoefficient n) :
    Real.exp (-tau * Real.log (n : ℝ)) = 1 := by
  have h_coeff :
      logZetaCoeff n =
        translatedLogZetaCoeff tau n :=
    classical_dirichlet_series_uniqueness
      logZetaCoeff
      (translatedLogZetaCoeff tau)
      h_inv
      n
      hn.1

  have hn0 : n ≠ 0 := Nat.ne_of_gt hn.1

  have h_left :
      logZetaCoeff n = (vonMangoldt n : ℂ) := by
    unfold logZetaCoeff
    simp [hn0]

  have h_right :
      translatedLogZetaCoeff tau n =
        (vonMangoldt n : ℂ) *
          (Real.exp (-tau * Real.log (n : ℝ)) : ℂ) := by
    unfold translatedLogZetaCoeff
    simp [hn0]

  have h_coeff_expanded :
      (vonMangoldt n : ℂ) =
        (vonMangoldt n : ℂ) *
          (Real.exp (-tau * Real.log (n : ℝ)) : ℂ) := by
    calc
      (vonMangoldt n : ℂ) = logZetaCoeff n := h_left.symm
      _ = translatedLogZetaCoeff tau n := h_coeff
      _ =
          (vonMangoldt n : ℂ) *
            (Real.exp (-tau * Real.log (n : ℝ)) : ℂ) := h_right

  have h_real :
      vonMangoldt n =
        vonMangoldt n *
          Real.exp (-tau * Real.log (n : ℝ)) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul]
    exact h_coeff_expanded

  have h_factor :
      vonMangoldt n *
        (Real.exp (-tau * Real.log (n : ℝ)) - 1) = 0 := by
    calc
      vonMangoldt n *
          (Real.exp (-tau * Real.log (n : ℝ)) - 1)
          =
        vonMangoldt n *
          Real.exp (-tau * Real.log (n : ℝ)) -
          vonMangoldt n := by
            ring
      _ = 0 := sub_eq_zero.mpr h_real.symm

  exact sub_eq_zero.mp
    ((mul_eq_zero.mp h_factor).resolve_left hn.2)

/--
A real translation leaving all Dirichlet coefficients unchanged strictly forces
the translation parameter tau to zero.
-/
theorem dirichlet_translation_zero
    (tau : ℝ)
    (h_invariant : IsDirichletSeriesInvariantUnderTranslation tau) :
    tau = 0 := by
  have h_exp : Real.exp (-tau * Real.log (2 : ℝ)) = 1 :=
    classical_dirichlet_translation_coefficients tau h_invariant 2 coefficient_two_non_zero

  have h_arg : -tau * Real.log (2 : ℝ) = 0 := by
    apply Real.exp_injective
    simpa using h_exp

  have h_log2 : Real.log (2 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))

  have h_tau_zero : -tau = 0 := (mul_eq_zero.mp h_arg).resolve_right h_log2
  linarith

/--
The translation parameter `tau` induces the standard Dirichlet coefficient
multiplier `n⁻ᵗᵃᵘ = exp (-tau * log n)`.
-/
def IsDirichletDeformation (tau : ℝ) : Prop :=
  IsDirichletSeriesInvariantUnderTranslation tau

/--
Classical Dirichlet Series Bounds (Right Half-Plane).
For strictly real evaluation lines σ₀ > 1, the absolute convergence of the
Riemann zeta Dirichlet series guarantees it is bounded strictly within a
geometric disk of radius (ζ(σ₀) - 1) centered at 1.
See E.C. Titchmarsh, "The Theory of the Riemann Zeta-Function", Ch. II.
-/
axiom classical_zeta_dirichlet_disk (σ₀ : ℝ) (h_gt : 1 < σ₀) :
  ∀ t : ℝ, norm (zeta_C (Complex.mk σ₀ t) - 1) ≤ (zeta_C σ₀).re - 1

/--
Classical Cauchy-Riemann logarithmic-derivative extraction.
For evaluation lines strictly in the right half-plane (σ > 1), the
ordinary Riemann zeta function is zero-free and holomorphic. Thus,
any differentiable turn-valued phase representative satisfying the polar
identity obeys ∂σ theta_D = Im (zeta_C' / zeta_C) / (2π).
-/
axiom classical_zeta_phase_gradient
    (theta_D : ℝ → ℝ → ℝ)
    (σ : ℝ)
    (h_gt : 1 < σ)
    (h_phase_of_zeta :
      ∀ x t,
        zeta_C (Complex.mk x t) =
          (norm (zeta_C (Complex.mk x t)) : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * (theta_D x t : ℂ)))
    (h_theta_diff :
      ∀ t, DifferentiableAt ℝ (fun x => theta_D x t) σ) :
    ∀ t,
      deriv (fun x => theta_D x t) σ =
        ((deriv zeta_C (Complex.mk σ t) /
          zeta_C (Complex.mk σ t)).im) /
          (2 * Real.pi)

/--
Classical disk-to-principal-argument estimate.

For σ₀ ≥ 2, the radius r = ζ(σ₀) - 1 lies in (0,1). If
|ζ(σ₀ + it) - 1| ≤ r, then the principal argument satisfies
|Arg ζ(σ₀ + it)| ≤ arcsin r.

`theta_D` is measured in turns, so it equals Arg/(2π).
-/
axiom classical_zeta_phase_ceiling
    (theta_D : ℝ → ℝ → ℝ)
    (σ₀ : ℝ)
    (h_ge : 2 ≤ σ₀)
    (h_phase_is_principal :
      ∀ t,
        theta_D σ₀ t =
          Complex.arg (zeta_C (Complex.mk σ₀ t)) /
            (2 * Real.pi)) :
    ∀ t : ℝ,
      norm (zeta_C (Complex.mk σ₀ t) - 1) ≤
        (zeta_C σ₀).re - 1 →
      |theta_D σ₀ t| ≤
        Real.arcsin ((zeta_C σ₀).re - 1) /
          (2 * Real.pi)



/--
CLASSICAL INFINITE LIMITS
-/
noncomputable def inf_prod_mag {X : Type}
    (a : ℕ → X → {r : ℝ // r > 0})
    (s : X) : {r : ℝ // r > 0} :=
  ⟨Real.exp (∑' k, Real.log (a k s).val), Real.exp_pos _⟩


noncomputable def inf_sum_phase {ι : Type*} {X : Type}
    (x : ι → X → ℝ)
    (s : X) : ℝ :=
  ∑' i, x i s


def IsAbsolutelyConvergentProd {X : Type}
    (f : ℕ → X → {z : ℂ // z ≠ 0}) : Prop :=
  ∀ s : X, Summable (fun k => ‖(f k s : ℂ) - 1‖)


/-- Ahlfors guarantee linked via magnitude and phase (supporting non-unit moduli) -/
theorem ahlfors_phase_summable {X : Type}
    (f : ℕ → X → {z : ℂ // z ≠ 0})
    (a : ℕ → X → {r : ℝ // r > 0})
    (x : ℕ → X → ℝ)
    (s : X)
    (_h_link : ∀ k s,
      (f k s : ℂ) =
        (a k s).val *
          Complex.exp (2 * Real.pi * Complex.I * (x k s : ℂ)))
    (h_small : ∀ k s, |x k s| ≤ ‖(f k s : ℂ) - 1‖)
    (h_conv : IsAbsolutelyConvergentProd f) :
    Summable (fun k => x k s) := by
  apply Summable.of_norm_bounded (g := fun k => ‖(f k s : ℂ) - 1‖)
  · exact h_conv s
  · intro k
    rw [Real.norm_eq_abs]
    exact h_small k s


end TainoPolar
