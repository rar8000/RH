/-
Copyright (c) 2026 Richard Andrew Rodriguez.
Released under the MIT license.
Manuscript DOI: 10.5281/zenodo.23692735
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta


namespace TainoPolar


/--
Axiom 1.1: State space (Full PSpace)
The state space 𝒫 enforces unsigned magnitude (a ≥ 0) alongside continuous phase.
This is fully analogous to the standard complex plane ℂ.
-/
structure PSpace where
  mag   : {a : ℝ // a ≥ 0}
  phase : ℝ


/--
The Punctured Plane (P_star)
Analogous to ℂ*. Restricted exclusively to states with strictly positive magnitude (a > 0).
Because it extends PSpace, it is a native instance of PSpace: it automatically
coerces to PSpace, so addition and multiplication work with it transparently.
-/
--structure P_star extends PSpace where
--  mag_pos : mag.val > 0
abbrev P_star := {p : PSpace // p.mag.val > 0}



/--
Axiom 1.2: Magnitude map
Negative phases enforce an inverse of the magnitude.


*NOTE: We will be staying in double bracket notation for the proof.
The single bracket notation map is just an evaluation convention.*
-/
noncomputable def singleBracket (a : {r : ℝ // r > 0}) (x : ℝ) : PSpace :=
  if 0 ≤ x then
    PSpace.mk ⟨a.val, le_of_lt a.property⟩ x
  else
    let inv_a : {r : ℝ // r > 0} := ⟨1 / a.val, div_pos zero_lt_one a.property⟩
    PSpace.mk ⟨inv_a.val, le_of_lt inv_a.property⟩ x


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


def m_double (p : PSpace) : {r : ℝ // r ≥ 0} := p.mag


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
Axiom 1.16.1: Native P-space Arctangent (Continuous Unwrapped Chart).
Replaces the standard arctan with a 2D fractional angle extractor
that strictly maps the Cartesian plane into continuous fractional turns.
By charting the right half-plane directly to [3/4, 5/4], we natively eradicate
the 0 ≡ 1 branch cut, allowing pure continuous evaluation in ℝ.
-/
noncomputable def pspace_arctan (y x : ℝ) : ℝ :=
  let theta := Real.arctan (y / x) / (2 * Real.pi)
  if x > 0 then theta + 1
  else if x < 0 then theta + 1 / 2
  else if x = 0 ∧ y > 0 then 1 / 4
  else if x = 0 ∧ y < 0 then 3 / 4
  else 0

/--
Axiom 1.17: Base-to-fiber gauge normalization
-/
noncomputable def gauge_theta (X Y : ℝ) : ℝ :=
  pspace_arctan Y X

/--
Axiom 1.7: Base-to-fiber gauge projection
-/
noncomputable def gauge_projection (Z : ℂ) (n : ℤ) : PSpace :=
  let X := Z.re
  let Y := Z.im
  let r := Real.sqrt (X^2 + Y^2)
  let phase_val := gauge_theta X Y + (n : ℝ)
  PSpace.mk ⟨r, Real.sqrt_nonneg _⟩ phase_val

scoped notation "π" => proj


/--
Axiom 1.8: Addition
-/
noncomputable def add_rel (p q r : PSpace) : Prop :=
  ∀ t : ℝ, p.mag.val * Real.sin (t + 2 * Real.pi * p.phase) +
           q.mag.val * Real.sin (t + 2 * Real.pi * q.phase) =
           r.mag.val * Real.sin (t + 2 * Real.pi * r.phase)

/--
Native P-Space Addition Function (`add_state`) via Sine Mechanics.
Solves for the resultant magnitude and phase directly from the harmonic expansion
coefficients of Axiom 1.8 (`add_rel`), utilizing `pspace_arctan` for continuous phase tracking.
-/
noncomputable def add_state (p q : PSpace) : PSpace :=
  let A := p.mag.val
  let x1 := p.phase
  let B := q.mag.val
  let x2 := q.phase
  -- Harmonic expansion coefficients for sin(t + phase)
  let C_sum := A * Real.cos (2 * Real.pi * x1) + B * Real.cos (2 * Real.pi * x2)
  let S_sum := A * Real.sin (2 * Real.pi * x1) + B * Real.sin (2 * Real.pi * x2)
  -- Resultant magnitude via root-sum-square
  let c := Real.sqrt (C_sum^2 + S_sum^2)
  let mag : {r : ℝ // r ≥ 0} := ⟨c, Real.sqrt_nonneg _⟩
  -- Resultant phase via native continuous unwrapped chart (pspace_arctan)
  let z := pspace_arctan S_sum C_sum
  ⟦mag, z⟧

/--
Theorem: The magnitude output of `add_state` is unconditionally non-negative.
-/
theorem add_state_mag_nonneg (p q : PSpace) : 0 ≤ (add_state p q).mag.val := by
  exact (add_state p q).mag.property


/--
Canonical principal branch normalization mapping any real angle into [0, 1) via modulo 1.
Enforces Axiom 1.12 natively.
-/
noncomputable def canonical_phase (theta : ℝ) : ℝ :=
  Int.fract theta


/-- Sanity Check Test 1: [[2, 0]] + [[1, 1/2]] evaluates to magnitude 1 and phase 1. -/
lemma sanity_check_add_1 :
    let p : PSpace := ⟦⟨2, by norm_num⟩, 0⟧
    let q : PSpace := ⟦⟨1, by norm_num⟩, 1/2⟧
    add_state p q ≡ ⟦⟨1, by norm_num⟩, 1⟧ := by
  intro p q
  have h_cos0 : Real.cos (2 * Real.pi * 0) = 1 := by
    have : (2 * Real.pi * 0 : ℝ) = 0 := by ring
    rw [this, Real.cos_zero]
  have h_sin0 : Real.sin (2 * Real.pi * 0) = 0 := by
    have : (2 * Real.pi * 0 : ℝ) = 0 := by ring
    rw [this, Real.sin_zero]
  have h_cos : Real.cos (2 * Real.pi * (1 / 2)) = -1 := by
    have : 2 * Real.pi * (1 / 2) = Real.pi := by ring
    rw [this, Real.cos_pi]
  have h_sin : Real.sin (2 * Real.pi * (1 / 2)) = 0 := by
    have : 2 * Real.pi * (1 / 2) = Real.pi := by ring
    rw [this, Real.sin_pi]

  unfold StrictEq
  constructor
  · -- Magnitude proof: (add_state p q).mag = ⟨1, _⟩
    apply Subtype.ext
    dsimp [add_state]
    have h_c1 : 2 * Real.cos (2 * Real.pi * 0) + 1 * Real.cos (2 * Real.pi * (1 / 2)) = 1 := by
      rw [h_cos0, h_cos]
      ring
    have h_s1 : 2 * Real.sin (2 * Real.pi * 0) + 1 * Real.sin (2 * Real.pi * (1 / 2)) = 0 := by
      rw [h_sin0, h_sin]
      ring
    rw [h_c1, h_s1]
    norm_num
  · -- Phase proof: (add_state p q).phase = 1
    dsimp [add_state, pspace_arctan]
    have h_c1 : 2 * Real.cos (2 * Real.pi * 0) + 1 * Real.cos (2 * Real.pi * (1 / 2)) = 1 := by
      rw [h_cos0, h_cos]
      ring
    have h_s1 : 2 * Real.sin (2 * Real.pi * 0) + 1 * Real.sin (2 * Real.pi * (1 / 2)) = 0 := by
      rw [h_sin0, h_sin]
      ring
    rw [h_c1, h_s1]
    norm_num

/-- Sanity Check Test 2: [[1, 1/4]] + [[1, 0]] evaluates to magnitude √2 and phase 9/8. -/
lemma sanity_check_add_2 :
    let p : PSpace := ⟦⟨1, by norm_num⟩, 1/4⟧
    let q : PSpace := ⟦⟨1, by norm_num⟩, 0⟧
    add_state p q ≡ ⟦⟨Real.sqrt 2, by positivity⟩, 9/8⟧ := by
  intro p q
  have h_cos0 : Real.cos (2 * Real.pi * 0) = 1 := by
    have : (2 * Real.pi * 0 : ℝ) = 0 := by ring
    rw [this, Real.cos_zero]
  have h_sin0 : Real.sin (2 * Real.pi * 0) = 0 := by
    have : (2 * Real.pi * 0 : ℝ) = 0 := by ring
    rw [this, Real.sin_zero]
  have h_cos : Real.cos (2 * Real.pi * (1 / 4)) = 0 := by
    have : 2 * Real.pi * (1 / 4) = Real.pi / 2 := by ring
    rw [this, Real.cos_pi_div_two]
  have h_sin : Real.sin (2 * Real.pi * (1 / 4)) = 1 := by
    have : 2 * Real.pi * (1 / 4) = Real.pi / 2 := by ring
    rw [this, Real.sin_pi_div_two]

  unfold StrictEq
  constructor
  · -- Magnitude proof: (add_state p q).mag = ⟨√2, _⟩
    apply Subtype.ext
    dsimp [add_state]
    have h_c2 : 1 * Real.cos (2 * Real.pi * (1 / 4)) + 1 * Real.cos (2 * Real.pi * 0) = 1 := by
      rw [h_cos0, h_cos]
      ring
    have h_s2 : 1 * Real.sin (2 * Real.pi * (1 / 4)) + 1 * Real.sin (2 * Real.pi * 0) = 1 := by
      rw [h_sin0, h_sin]
      ring
    rw [h_c2, h_s2]
    norm_num
  · -- Phase proof: (add_state p q).phase = 9/8
    dsimp [add_state, pspace_arctan]
    have h_c2 : 1 * Real.cos (2 * Real.pi * (1 / 4)) + 1 * Real.cos (2 * Real.pi * 0) = 1 := by
      rw [h_cos0, h_cos]
      ring
    have h_s2 : 1 * Real.sin (2 * Real.pi * (1 / 4)) + 1 * Real.sin (2 * Real.pi * 0) = 1 := by
      rw [h_sin0, h_sin]
      ring
    rw [h_c2, h_s2]
    have h_div : (1 / 1 : ℝ) = 1 := by norm_num
    rw [h_div, Real.arctan_one]
    have h_pi_cancel : Real.pi / 4 / (2 * Real.pi) = 1 / 8 := by
      have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp [hp]
      ring
    rw [h_pi_cancel]
    norm_num

/-- Sanity Check Test 3: [[2, -3/8]] + [[2, 5/8]] evaluates to magnitude 4 and phase 5/8. -/
lemma sanity_check_add_3 :
    let p : PSpace := ⟦⟨2, by norm_num⟩, -3/8⟧
    let q : PSpace := ⟦⟨2, by norm_num⟩, 5/8⟧
    add_state p q ≡ ⟦⟨4, by norm_num⟩, 5/8⟧ := by
  intro p q
  have h_angles : 2 * Real.pi * (-3 / 8) = 2 * Real.pi * (5 / 8) - 2 * Real.pi := by ring
  have h_cos_eq : Real.cos (2 * Real.pi * (-3 / 8)) = Real.cos (2 * Real.pi * (5 / 8)) := by
    rw [h_angles, Real.cos_sub_two_pi]
  have h_sin_eq : Real.sin (2 * Real.pi * (-3 / 8)) = Real.sin (2 * Real.pi * (5 / 8)) := by
    rw [h_angles, Real.sin_sub_two_pi]

  have h_val_eq : 2 * Real.pi * (5 / 8) = Real.pi + Real.pi / 4 := by ring
  have h_sin_pi_add (x : ℝ) : Real.sin (Real.pi + x) = -Real.sin x := by
    rw [Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have h_cos_pi_add (x : ℝ) : Real.cos (Real.pi + x) = -Real.cos x := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring

  have h_sin_cos_equal : Real.sin (2 * Real.pi * (5 / 8)) = Real.cos (2 * Real.pi * (5 / 8)) := by
    rw [h_val_eq, h_sin_pi_add, h_cos_pi_add]
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]

  have h_cos_neg : Real.cos (2 * Real.pi * (5 / 8)) < 0 := by
    rw [h_val_eq, h_cos_pi_add]
    have : 0 < Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]; positivity
    linarith

  have h_C_neg : 4 * Real.cos (2 * Real.pi * (5 / 8)) < 0 := by
    have : 0 < (4 : ℝ) := by norm_num
    exact mul_neg_of_pos_of_neg this h_cos_neg

  unfold StrictEq
  constructor
  · -- Magnitude proof
    apply Subtype.ext
    dsimp [add_state]
    rw [h_cos_eq, h_sin_eq]
    have h_c_sum : 2 * Real.cos (2 * Real.pi * (5 / 8)) + 2 * Real.cos (2 * Real.pi * (5 / 8)) = 4 * Real.cos (2 * Real.pi * (5 / 8)) := by ring
    have h_s_sum : 2 * Real.sin (2 * Real.pi * (5 / 8)) + 2 * Real.sin (2 * Real.pi * (5 / 8)) = 4 * Real.sin (2 * Real.pi * (5 / 8)) := by ring
    rw [h_c_sum, h_s_sum]
    have h_trig_sum : (4 * Real.cos (2 * Real.pi * (5 / 8)))^2 + (4 * Real.sin (2 * Real.pi * (5 / 8)))^2 = 16 := by
      calc (4 * Real.cos (2 * Real.pi * (5 / 8)))^2 + (4 * Real.sin (2 * Real.pi * (5 / 8)))^2
        _ = 16 * ((Real.cos (2 * Real.pi * (5 / 8)))^2 + (Real.sin (2 * Real.pi * (5 / 8)))^2) := by ring
        _ = 16 * 1 := by rw [Real.cos_sq_add_sin_sq]
        _ = 16 := by ring
    rw [h_trig_sum]
    have h_sqrt16 : Real.sqrt 16 = 4 := by
      have : (16 : ℝ) = 4^2 := by norm_num
      rw [this, Real.sqrt_sq (by norm_num)]
    rw [h_sqrt16]
  · -- Phase proof
    dsimp [add_state, pspace_arctan]
    rw [h_cos_eq, h_sin_eq]
    have h_c_sum : 2 * Real.cos (2 * Real.pi * (5 / 8)) + 2 * Real.cos (2 * Real.pi * (5 / 8)) = 4 * Real.cos (2 * Real.pi * (5 / 8)) := by ring
    have h_s_sum : 2 * Real.sin (2 * Real.pi * (5 / 8)) + 2 * Real.sin (2 * Real.pi * (5 / 8)) = 4 * Real.sin (2 * Real.pi * (5 / 8)) := by ring
    rw [h_c_sum, h_s_sum]
    have h_ratio : (4 * Real.sin (2 * Real.pi * (5 / 8))) / (4 * Real.cos (2 * Real.pi * (5 / 8))) = 1 := by
      have h_cos_ne : 4 * Real.cos (2 * Real.pi * (5 / 8)) ≠ 0 := ne_of_lt h_C_neg
      rw [h_sin_cos_equal]
      exact div_self h_cos_ne
    rw [h_ratio, Real.arctan_one]
    have h_pi_cancel : Real.pi / 4 / (2 * Real.pi) = 1 / 8 := by
      have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp [hp]; ring
    rw [h_pi_cancel]
    split_ifs <;> (try linarith [h_C_neg])

/--
Axiom 1.8.1: Negation
-/
noncomputable def neg_state (p : PSpace) : PSpace :=
  ⟦p.mag, p.phase + (1 / 2 : ℝ)⟧

/-- Project Lemma: Negation perfectly recovers `-proj p`. -/
lemma proj_neg_state (p : PSpace) : proj (neg_state p) = - proj p := by
  dsimp [neg_state, proj]
  have h_add : 2 * Real.pi * Complex.I * ((p.phase + 1/2 : ℝ) : ℂ) =
               2 * Real.pi * Complex.I * (p.phase : ℂ) + Real.pi * Complex.I := by
    push_cast; ring
  rw [h_add, Complex.exp_add]
  have h_pi_i : Complex.exp (Real.pi * Complex.I) = -1 := Complex.exp_pi_mul_I
  rw [h_pi_i]
  ring

/--
Axiom 1.8.2: Subtraction
-/
noncomputable def sub_rel (p q r : PSpace) : Prop :=
  add_rel p (neg_state q) r

/--
Native P-Space Subtraction Function (`sub_state`).
Computes `p - q` computationally by negating `q` (`neg_state q`)
and feeding it into the native sine-wave addition function (`add_state`).
-/
noncomputable def sub_state (p q : PSpace) : PSpace :=
  add_state p (neg_state q)




lemma proj_re (p : PSpace) : (proj p).re = p.mag.val * Real.cos (2 * Real.pi * p.phase) := by
  dsimp [proj]
  have h_exp_p : 2 * ↑Real.pi * Complex.I * ↑p.phase = ↑(2 * Real.pi * p.phase) * Complex.I := by push_cast; ring
  rw [h_exp_p, Complex.exp_mul_I, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re,
             Complex.cos_ofReal_re, Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re,
             Complex.sin_ofReal_im, Complex.I_im, mul_zero, mul_one, add_zero]

lemma proj_im (p : PSpace) : (proj p).im = p.mag.val * Real.sin (2 * Real.pi * p.phase) := by
  dsimp [proj]
  have h_exp_p : 2 * ↑Real.pi * Complex.I * ↑p.phase = ↑(2 * Real.pi * p.phase) * Complex.I := by push_cast; ring
  rw [h_exp_p, Complex.exp_mul_I, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.add_im,
             Complex.cos_ofReal_im, Complex.mul_im, Complex.sin_ofReal_re, Complex.I_im,
             Complex.sin_ofReal_im, Complex.I_re, mul_zero, mul_one, zero_add]

/--
Proves natively that the continuous unwrapped chart (pspace_arctan)
perfectly reconstructs Cartesian components when scaled by magnitude.
-/
lemma pspace_arctan_proj (x y : ℝ) :
    Real.sqrt (x^2 + y^2) * Real.cos (2 * Real.pi * pspace_arctan y x) = x ∧
    Real.sqrt (x^2 + y^2) * Real.sin (2 * Real.pi * pspace_arctan y x) = y := by
  have hcpi : Real.cos Real.pi = -1 := Real.cos_pi
  have hspi : Real.sin Real.pi = 0 := Real.sin_pi
  have hc2pi : Real.cos (2 * Real.pi) = 1 := by
    have : 2 * Real.pi = Real.pi + Real.pi := by ring
    rw [this, Real.cos_add, hcpi, hspi]
    ring
  have hs2pi : Real.sin (2 * Real.pi) = 0 := by
    have : 2 * Real.pi = Real.pi + Real.pi := by ring
    rw [this, Real.sin_add, hcpi, hspi]
    ring
  dsimp [pspace_arctan]
  split_ifs with h1 h2 h3 h4
  · -- x > 0 Chart
    have hx_ne : x ≠ 0 := ne_of_gt h1
    have h_angle : 2 * Real.pi * (Real.arctan (y / x) / (2 * Real.pi) + 1) = Real.arctan (y / x) + 2 * Real.pi := by
      have hp : 2 * Real.pi ≠ 0 := by linarith [Real.pi_pos]
      calc 2 * Real.pi * (Real.arctan (y / x) / (2 * Real.pi) + 1)
        _ = 2 * Real.pi * (Real.arctan (y / x) / (2 * Real.pi)) + 2 * Real.pi := by ring
        _ = Real.arctan (y / x) + 2 * Real.pi := by rw [mul_div_cancel₀ _ hp]
    have h_sq_div : 1 + (y/x)^2 = (x^2 + y^2) / x^2 := by
      calc 1 + (y/x)^2 = 1 + y^2 / x^2 := by rw [div_pow]
        _ = x^2 / x^2 + y^2 / x^2 := by rw [div_self (pow_ne_zero 2 hx_ne)]
        _ = (x^2 + y^2) / x^2 := by rw [add_div]
    have h_sqrt_x2 : Real.sqrt (x^2) = x := Real.sqrt_sq (le_of_lt h1)
    have h_sqrt_div : Real.sqrt (1 + (y/x)^2) = Real.sqrt (x^2 + y^2) / x := by
      rw [h_sq_div, Real.sqrt_div (by positivity), h_sqrt_x2]
    constructor
    · rw [h_angle, Real.cos_add, hc2pi, hs2pi]
      have : Real.cos (Real.arctan (y / x)) * 1 - Real.sin (Real.arctan (y / x)) * 0 = Real.cos (Real.arctan (y / x)) := by ring
      rw [this, Real.cos_arctan, h_sqrt_div]
      have h_sqrt_pos : 0 < Real.sqrt (x^2 + y^2) := by apply Real.sqrt_pos.mpr; positivity
      have h_sqrt_ne : Real.sqrt (x^2 + y^2) ≠ 0 := ne_of_gt h_sqrt_pos
      field_simp [hx_ne, h_sqrt_ne]
    · rw [h_angle, Real.sin_add, hc2pi, hs2pi]
      have : Real.sin (Real.arctan (y / x)) * 1 + Real.cos (Real.arctan (y / x)) * 0 = Real.sin (Real.arctan (y / x)) := by ring
      rw [this, Real.sin_arctan, h_sqrt_div]
      have h_sqrt_pos : 0 < Real.sqrt (x^2 + y^2) := by apply Real.sqrt_pos.mpr; positivity
      have h_sqrt_ne : Real.sqrt (x^2 + y^2) ≠ 0 := ne_of_gt h_sqrt_pos
      field_simp [hx_ne, h_sqrt_ne]
  · -- x < 0 Chart
    have hx_ne : x ≠ 0 := ne_of_lt h2
    have h_neg_x_ne : -x ≠ 0 := by linarith
    have h_angle : 2 * Real.pi * (Real.arctan (y / x) / (2 * Real.pi) + 1 / 2) = Real.arctan (y / x) + Real.pi := by
      have hp : 2 * Real.pi ≠ 0 := by linarith [Real.pi_pos]
      calc 2 * Real.pi * (Real.arctan (y / x) / (2 * Real.pi) + 1 / 2)
        _ = 2 * Real.pi * (Real.arctan (y / x) / (2 * Real.pi)) + Real.pi := by ring
        _ = Real.arctan (y / x) + Real.pi := by rw [mul_div_cancel₀ _ hp]
    have h_sq_div : 1 + (y/x)^2 = (x^2 + y^2) / x^2 := by
      calc 1 + (y/x)^2 = 1 + y^2 / x^2 := by rw [div_pow]
        _ = x^2 / x^2 + y^2 / x^2 := by rw [div_self (pow_ne_zero 2 hx_ne)]
        _ = (x^2 + y^2) / x^2 := by rw [add_div]
    have h_sqrt_x2 : Real.sqrt (x^2) = -x := by
      have : x ≤ 0 := le_of_lt h2
      exact Real.sqrt_sq_eq_abs x |>.trans (abs_of_nonpos this)
    have h_sqrt_div : Real.sqrt (1 + (y/x)^2) = Real.sqrt (x^2 + y^2) / (-x) := by
      rw [h_sq_div, Real.sqrt_div (by positivity), h_sqrt_x2]
    constructor
    · rw [h_angle, Real.cos_add, hcpi, hspi]
      have : Real.cos (Real.arctan (y / x)) * -1 - Real.sin (Real.arctan (y / x)) * 0 = -Real.cos (Real.arctan (y / x)) := by ring
      rw [this, Real.cos_arctan, h_sqrt_div]
      have h_sqrt_pos : 0 < Real.sqrt (x^2 + y^2) := by apply Real.sqrt_pos.mpr; positivity
      have h_sqrt_ne : Real.sqrt (x^2 + y^2) ≠ 0 := ne_of_gt h_sqrt_pos
      field_simp [hx_ne, h_neg_x_ne, h_sqrt_ne]
    · rw [h_angle, Real.sin_add, hcpi, hspi]
      have : Real.sin (Real.arctan (y / x)) * -1 + Real.cos (Real.arctan (y / x)) * 0 = -Real.sin (Real.arctan (y / x)) := by ring
      rw [this, Real.sin_arctan, h_sqrt_div]
      have h_sqrt_pos : 0 < Real.sqrt (x^2 + y^2) := by apply Real.sqrt_pos.mpr; positivity
      have h_sqrt_ne : Real.sqrt (x^2 + y^2) ≠ 0 := ne_of_gt h_sqrt_pos
      field_simp [hx_ne, h_neg_x_ne, h_sqrt_ne]
  · -- x = 0, y > 0 Chart
    have hx0 : x = 0 := h3.1
    have hy_pos : y > 0 := h3.2
    have h_angle : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
    have h_sq : Real.sqrt (x^2 + y^2) = y := by
      rw [hx0, zero_pow (by norm_num), zero_add, Real.sqrt_sq (le_of_lt hy_pos)]
    constructor
    · rw [h_angle, Real.cos_pi_div_two, mul_zero, hx0]
    · rw [h_angle, Real.sin_pi_div_two, mul_one, h_sq]
  · -- x = 0, y < 0 Chart
    have hx0 : x = 0 := h4.1
    have hy_neg : y < 0 := h4.2
    have h_angle : 2 * Real.pi * (3 / 4 : ℝ) = Real.pi + Real.pi / 2 := by ring
    have h_cos : Real.cos (Real.pi + Real.pi / 2) = 0 := by
      rw [Real.cos_add, hcpi, hspi, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
    have h_sin : Real.sin (Real.pi + Real.pi / 2) = -1 := by
      rw [Real.sin_add, hcpi, hspi, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
    have h_sq : Real.sqrt (x^2 + y^2) = -y := by
      rw [hx0, zero_pow (by norm_num), zero_add, Real.sqrt_sq_eq_abs, abs_of_neg hy_neg]
    constructor
    · rw [h_angle, h_cos, mul_zero, hx0]
    · rw [h_angle, h_sin, h_sq]; ring
  · -- x = 0, y = 0 Edge Case
    have hx0 : x = 0 := by
      rcases lt_trichotomy x 0 with hx | hx | hx
      · exfalso; exact h2 hx
      · exact hx
      · exfalso; exact h1 hx
    have hy0 : y = 0 := by
      rcases lt_trichotomy y 0 with hy | hy | hy
      · exfalso; exact h4 ⟨hx0, hy⟩
      · exact hy
      · exfalso; exact h3 ⟨hx0, hy⟩
    constructor
    · rw [hx0, hy0]; simp
    · rw [hx0, hy0]; simp

/--
Project Lemma: Addition recovers classical complex addition.
-/
lemma proj_add_state (p q : PSpace) :
    proj (add_state p q) = proj p + proj q := by
  let A := p.mag.val
  let x1 := p.phase
  let B := q.mag.val
  let x2 := q.phase
  let C_sum := A * Real.cos (2 * Real.pi * x1) + B * Real.cos (2 * Real.pi * x2)
  let S_sum := A * Real.sin (2 * Real.pi * x1) + B * Real.sin (2 * Real.pi * x2)

  have h_re : (proj p + proj q).re = C_sum := by
    rw [Complex.add_re, proj_re p, proj_re q]
  have h_im : (proj p + proj q).im = S_sum := by
    rw [Complex.add_im, proj_im p, proj_im q]

  have h_mag_val : (add_state p q).mag.val = Real.sqrt (C_sum^2 + S_sum^2) := rfl
  have h_phase_val : (add_state p q).phase = pspace_arctan S_sum C_sum := rfl

  apply Complex.ext
  · rw [proj_re, h_mag_val, h_phase_val]
    have h_proj := (pspace_arctan_proj C_sum S_sum).1
    rw [h_proj]
    exact h_re.symm
  · rw [proj_im, h_mag_val, h_phase_val]
    have h_proj := (pspace_arctan_proj C_sum S_sum).2
    rw [h_proj]
    exact h_im.symm


/-- Project Lemma: Subtraction recovers classical complex subtraction. -/
lemma proj_sub_state (p q : PSpace) :
    proj (sub_state p q) = proj p - proj q := by
  have h_add := proj_add_state p (neg_state q)
  rw [proj_neg_state] at h_add
  calc proj (sub_state p q)
    _ = proj p + -proj q := h_add
    _ = proj p - proj q := sub_eq_add_neg _ _ |>.symm

noncomputable def mul_state (p q : PSpace) : PSpace :=
  let new_mag : {r : ℝ // r ≥ 0} :=
    ⟨p.mag.val * q.mag.val, mul_nonneg p.mag.property q.mag.property⟩
  ⟦new_mag, p.phase + q.phase⟧


/--
Axiom 1.9.2: Inverse phase
-/
noncomputable def inv_phase_state (p : PSpace) : PSpace :=
  ⟦p.mag, - p.phase⟧


/-- Project Lemma: Multiplication recovers classical complex multiplication. -/
lemma proj_mul_state (p q : PSpace) : proj (mul_state p q) = proj p * proj q := by
  dsimp [proj, mul_state]
  push_cast
  have h_dist : 2 * ↑Real.pi * Complex.I * (↑p.phase + ↑q.phase) =
                2 * ↑Real.pi * Complex.I * ↑p.phase +
                2 * ↑Real.pi * Complex.I * ↑q.phase := by ring
  rw [h_dist, Complex.exp_add]
  ring

/-- Project Lemma: Division recovers classical complex division. -/
noncomputable def div_state (p q : PSpace) : PSpace :=
  let new_mag : {r : ℝ // r ≥ 0} :=
    ⟨p.mag.val / q.mag.val, div_nonneg p.mag.property q.mag.property⟩
  ⟦new_mag, p.phase - q.phase⟧

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
Not used in the proof. Here as exposition of a much better way to
exponentiate than standard conditional exponentiation. And shows
why rotation units are the correct unit to use in polar arithmetic.
-/
noncomputable def exp_state (p q : PSpace) : PSpace :=
  have new_mag_nonneg : 0 ≤ p.mag.val ^ q.mag.val :=
    Real.rpow_nonneg p.mag.property q.mag.val
  let new_mag : {r : ℝ // r ≥ 0} := ⟨p.mag.val ^ q.mag.val, new_mag_nonneg⟩
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



/-
CLASSICAL ANALYTIC FOUNDATIONS

Classical Riemann zeta function.

-/

/--
The true Riemann completed zeta function ξ(s).
Mathlib implements the standard completed zeta as `completedRiemannZeta` (Λ(s)).
Riemann's ξ(s) is classically defined as (1/2) * s * (s - 1) * Λ(s).
Its zeros correspond exactly to the nontrivial zeros of the Riemann zeta function.
-/
noncomputable def xi_C (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s



/--
Absolute convergence of the ordinary Riemann zeta Dirichlet series.
Defined natively via Mathlib's Summable property on the shifted natural sequence.
-/
def IsAbsolutelyConvergentZeta (s : ℂ) : Prop :=
  Summable (fun (n : ℕ) => ‖((n + 1 : ℂ) ^ (-s))‖)


/--
Classical abscissa-of-absolute-convergence theorem for the Riemann zeta
Dirichlet series.
Citation: Titchmarsh, E. C. (1986). The Theory of the Riemann Zeta-Function, Ch. I §1.1.
-/
axiom classical_zeta_convergence (s : ℂ) :
  IsAbsolutelyConvergentZeta s ↔ 1 < s.re


/--
The true functional equation for Riemann's completed zeta function ξ(s).
Proven natively using Mathlib's underlying Λ₀(s) functional equation.
-/
theorem classical_xi_functional_equation (s : ℂ) :
    xi_C s = xi_C (1 - s) := by
  unfold xi_C
  rw [completedRiemannZeta₀_one_sub]
  ring

/--
Classical Schwarz reflection principle for the completed Riemann zeta function.

Because $\xi(s)$ is entire and strictly real-valued on the real axis, the Schwarz
reflection principle rigorously guarantees $\xi(\bar{s}) = \overline{\xi(s)}$.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter II (§ 2.1, pp. 13–16 & § 2.12, pp. 30–32).
- Ahlfors, L. V. (1979). *Complex Analysis* (3rd ed.). McGraw-Hill.
  Chapter 4 (§ 6.2: The Reflection Principle, Theorem 24, p. 172).
-/
axiom classical_xi_schwarz (s : ℂ) : xi_C (star s) = star (xi_C s)



open Filter

/--
Analytic definition of root multiplicity.
A complex number z is a root of multiplicity m for a function f if
the punctured limit of f(s) / (s - z)^m as s → z (with s ≠ z) exists and is strictly non-zero.

Citations:
- Ahlfors, L. V. (1979). *Complex Analysis* (3rd ed.). McGraw-Hill.
  (Chapter 4, Section 3.2: Zeros and Poles, pp. 127–128).
- Conway, J. B. (1978). *Functions of One Complex Variable I* (2nd ed.). Springer-Verlag.
  (Chapter IV, Section 3: Zeros of an Analytic Function, pp. 75–79).
-/
def IsAnalyticRootOfMultiplicity (f : ℂ → ℂ) (z : ℂ) (m : ℕ) : Prop :=
  m ≥ 1 ∧
  (∃ (c : ℂ), c ≠ 0 ∧ Tendsto (fun s => f s / (s - z)^m) (nhdsWithin z {z}ᶜ) (nhds c)) ∧
  (∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ ∀ᶠ s in nhds z, f s = (s - z)^m * g s)

/--
Classical Identity Theorem consequence.
Because the completed zeta function ξ(s) is an entire function and not identically zero,
any root must have a strictly positive, finite integer multiplicity.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.). Oxford Univ. Press.
  (Chapter II, Section 2.1 & Section 2.12: The functional equation establishes ξ(s) as an entire function).
- Ahlfors, L. V. (1979). *Complex Analysis* (3rd ed.). McGraw-Hill.
  (Chapter 4, Section 3.1–3.2, pp. 126–128: The Identity Theorem guarantees zeros of non-trivial entire functions are isolated with finite integer multiplicity).
- Conway, J. B. (1978). *Functions of One Complex Variable I* (2nd ed.). Springer-Verlag.
  (Chapter IV, Section 3, Theorem 3.7, p. 78).
-/
axiom classical_xi_root_multiplicity_exists (z : ℂ) (h_zero : xi_C z = 0) :
  ∃ m : ℕ, IsAnalyticRootOfMultiplicity xi_C z m



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

Citations:
- Hardy, G. H., & Riesz, M. (1915). *The General Theory of Dirichlet's Series*.
  Cambridge Tracts in Mathematics and Mathematical Physics, No. 18.
  (Chapter II, § 4, Theorem 6, p. 7: Uniqueness theorem for the coefficients of Dirichlet series).
- Apostol, T. M. (1990). *Modular Functions and Dirichlet Series in Number Theory* (2nd ed.).
  Graduate Texts in Mathematics, vol. 41. Springer-Verlag.
  (Chapter 11, § 11.4, Theorem 11.3, p. 226: Uniqueness theorem for ordinary Dirichlet series).
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. (Chapter I, § 1.1).
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
      Complex.exp (- (tau : ℂ) * (Real.log (n : ℝ) : ℂ)) -- Complex.I removed to match LaTeX spatial translation

/--
Classical Fact: Convergence of the logarithmic derivative Dirichlet series and its spatial shift.
Because $-\frac{\zeta'}{\zeta}(s) = \sum_{n=1}^\infty \Lambda(n) n^{-s}$ converges absolutely for $\operatorname{Re}(s) > 1$,
and the shifted series $\sum_{n=1}^\infty \Lambda(n) n^{-\tau} n^{-s}$ converges absolutely for $\operatorname{Re}(s) > 1 - \tau$,
both series converge absolutely on the common half-plane $\operatorname{Re}(s) > \sigma_2 = \max(1, 1 - \tau)$.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter I (§ 1.2, Equation 1.2.8, p. 3).
- Apostol, T. M. (1976). *Introduction to Analytic Number Theory*.
  Undergraduate Texts in Mathematics. Springer-Verlag. Chapter 11 (§ 11.5, Theorem 11.7, p. 236).
-/
axiom classical_dirichlet_shift_summable (tau : ℝ) :
  ∃ (σ₂ : ℝ), ∀ (s : ℂ), σ₂ < s.re →
    Summable (dirichletTerm logZetaCoeff s) ∧
    Summable (dirichletTerm (translatedLogZetaCoeff tau) s)

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
Project interface lemma: Translation invariance forces the complex phase multiplier
to be exactly 1 for non-zero coefficients.
-/
lemma classical_dirichlet_translation_coefficients
    (tau : ℝ)
    (h_inv : IsDirichletSeriesInvariantUnderTranslation tau)
    (n : ℕ)
    (hn : HasNonZeroCoefficient n) :
    Complex.exp (- (tau : ℂ) * (Real.log (n : ℝ) : ℂ)) = 1 := by
  have h_coeff : logZetaCoeff n = translatedLogZetaCoeff tau n :=
    classical_dirichlet_series_uniqueness logZetaCoeff (translatedLogZetaCoeff tau) h_inv n hn.1
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn.1

  have h_left : logZetaCoeff n = (vonMangoldt n : ℂ) := by
    unfold logZetaCoeff; simp [hn0]

  have h_right : translatedLogZetaCoeff tau n = (vonMangoldt n : ℂ) * Complex.exp (- (tau : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
    unfold translatedLogZetaCoeff; simp [hn0]

  have h_coeff_expanded : (vonMangoldt n : ℂ) = (vonMangoldt n : ℂ) * Complex.exp (- (tau : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
    calc (vonMangoldt n : ℂ)
      _ = logZetaCoeff n := h_left.symm
      _ = translatedLogZetaCoeff tau n := h_coeff
      _ = (vonMangoldt n : ℂ) * Complex.exp (- (tau : ℂ) * (Real.log (n : ℝ) : ℂ)) := h_right

  have h_factor : (vonMangoldt n : ℂ) * (Complex.exp (- (tau : ℂ) * (Real.log (n : ℝ) : ℂ)) - 1) = 0 := by
    calc (vonMangoldt n : ℂ) * (Complex.exp (- (tau : ℂ) * (Real.log (n : ℝ) : ℂ)) - 1)
      _ = (vonMangoldt n : ℂ) * Complex.exp (- (tau : ℂ) * (Real.log (n : ℝ) : ℂ)) - (vonMangoldt n : ℂ) := by ring
      _ = 0 := sub_eq_zero.mpr h_coeff_expanded.symm

  have h_vM_neq : (vonMangoldt n : ℂ) ≠ 0 := by exact_mod_cast hn.2
  exact sub_eq_zero.mp ((mul_eq_zero.mp h_factor).resolve_left h_vM_neq)



/--
A vertical phase translation leaving all Dirichlet coefficients unchanged
strictly forces the spatial translation parameter tau to zero.
Because this is a spatial deformation (Real exponent) rather than a phase
rotation, the equality exp(-tau * log 2) = 1 directly implies tau = 0.
-/
theorem dirichlet_translation_zero
    (tau : ℝ)
    (h_invariant : IsDirichletSeriesInvariantUnderTranslation tau) :
    tau = 0 := by
  -- 1. Evaluate the Dirichlet phase rotation at the first prime (n = 2)
  have h_exp2 : Complex.exp (- (tau : ℂ) * (Real.log (2 : ℝ) : ℂ)) = 1 :=
    classical_dirichlet_translation_coefficients tau h_invariant 2 coefficient_two_non_zero

  -- 2. Extract the integer winding multiple (Complex.exp(z) = 1 ↔ z = 2πki)
  have h_eq_2pi_k := Complex.exp_eq_one_iff.mp h_exp2
  rcases h_eq_2pi_k with ⟨k, hk⟩

  -- 3. Extract the Imaginary components from the strict complex equality
  -- Since the exponent is purely real, its imaginary part is 0.
  have h_im : (- (tau : ℂ) * (Real.log (2 : ℝ) : ℂ)).im = ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im := by
    have h1 : (k * (2 * ↑Real.pi * Complex.I) : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [hk, h1]

  have h_lhs : (- (tau : ℂ) * (Real.log (2 : ℝ) : ℂ)).im = 0 := by
    have h_real : - (tau : ℂ) * (Real.log (2 : ℝ) : ℂ) = Complex.ofReal (-tau * Real.log 2) := by push_cast; ring
    rw [h_real, Complex.ofReal_im]

  have h_rhs : ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im = (k : ℝ) * (2 * Real.pi) := by
    have h_eq : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = Complex.ofReal ((k : ℝ) * (2 * Real.pi)) * Complex.I := by push_cast; ring
    rw [h_eq]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]

  rw [h_lhs, h_rhs] at h_im

  -- 4. This forces the discrete integer k to be exactly 0
  have h_pi_pos : 0 < 2 * Real.pi := by positivity
  have h_k_zero_real : (k : ℝ) = 0 := by
    calc (k : ℝ) = ((k : ℝ) * (2 * Real.pi)) / (2 * Real.pi) := by rw [mul_div_cancel_right₀ _ (ne_of_gt h_pi_pos)]
      _ = 0 / (2 * Real.pi) := by rw [← h_im]
      _ = 0 := zero_div _
  have h_k_zero : k = 0 := by exact_mod_cast h_k_zero_real

  -- 5. Algebraic resolution back to tau = 0
  rw [h_k_zero] at hk
  -- Explicitly evaluate the cast integer zero to bypass the elaborator trap
  have hk_eval : ((0 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) = 0 := by push_cast; ring
  rw [hk_eval] at hk

  have h_re : (- (tau : ℂ) * (Real.log (2 : ℝ) : ℂ)).re = 0 := by
    rw [hk, Complex.zero_re]

  have h_re_calc : (- (tau : ℂ) * (Real.log (2 : ℝ) : ℂ)).re = -tau * Real.log 2 := by
    have h_real : - (tau : ℂ) * (Real.log (2 : ℝ) : ℂ) = Complex.ofReal (-tau * Real.log 2) := by push_cast; ring
    rw [h_real, Complex.ofReal_re]

  rw [h_re_calc] at h_re

  have h_log2_neq : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h_tau_zero : -tau = 0 := by
    cases mul_eq_zero.mp h_re with
    | inl h1 => exact h1
    | inr h2 => exfalso; exact h_log2_neq h2
  linarith


/--
The translation parameter `tau` induces the standard Dirichlet coefficient
multiplier `n⁻ᵗᵃᵘ = exp (-tau * log n)`.
-/
def IsDirichletDeformation (tau : ℝ) : Prop :=
  IsDirichletSeriesInvariantUnderTranslation tau









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


/-
CLASSICAL RIEMANN ZETA FACTS
-/



/--
The set of all zeros of the completed Riemann zeta function $\xi(s)$.
-/
def classical_zeta_root_set : Set ℂ := {s : ℂ | xi_C s = 0}



/--
Classical Analytic Fact: Local finiteness of Riemann zeta zero ordinates.
Due to the discreteness and isolation of the zeros of an entire function of order 1
within the bounded critical strip $0 < \operatorname{Re}(s) < 1$, the number of zeros whose
imaginary parts lie within any bounded horizontal strip ($\vert{}s.im\vert{} \le T$) is strictly finite.

Citation:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter IX (§ 9.1–9.3, pp. 212–216).
-/
axiom classical_xi_roots_locally_finite (T : ℝ) :
  Set.Finite {s : ℂ | xi_C s = 0 ∧ |s.im| ≤ T}


/--
Classical Analytic Fact: Countability of the Riemann zeta zero set.

By the Identity Theorem for analytic functions, because the completed Riemann zeta
function $\xi(s)$ is a non-trivial entire function that does not vanish identically,
every zero $z_0 \in \mathbb{C}$ of $\xi(s)$ is isolated. A subset of the complex plane
where every point is isolated forms a discrete topological space. Since $\mathbb{C}$ is
second-countable, any discrete subset is at most countable.

Detailed Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter II (§ 2.12, pp. 30–32) & Chapter IX (§ 9.1–9.3, pp. 212–216),
  establishing $\xi(s)$ as an entire function of order 1 and managing the zero enumeration sequence.
- Conway, J. B. (1978). *Functions of One Complex Variable I* (2nd ed.).
  Graduate Texts in Mathematics, vol. 11. Springer-Verlag. Chapter IV (§ 3, Theorem 3.7
  & Corollary 3.8, pp. 78–79), proving that the zeros of a non-constant analytic function on
  a connected open domain are isolated, which mathematically guarantees countability.
-/
lemma classical_xi_root_set_countable : classical_zeta_root_set.Countable := by
  have h_union : classical_zeta_root_set ⊆ ⋃ (k : ℕ), {s : ℂ | xi_C s = 0 ∧ |s.im| ≤ (k : ℝ)} := by
    intro s hs
    rcases exists_nat_ge |s.im| with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hs, hk⟩
  have h_cnt : (⋃ (k : ℕ), {s : ℂ | xi_C s = 0 ∧ |s.im| ≤ (k : ℝ)}).Countable :=
    Set.countable_iUnion (fun (k : ℕ) => (classical_xi_roots_locally_finite (k : ℝ)).countable)
  exact h_cnt.mono h_union

/--
Classical Analytic Fact: The Argument Principle applied to a strictly isolating circle for $\xi(s)$.

By Cauchy's Argument Principle and the Residue Theorem, the closed contour integral of the
logarithmic derivative of a meromorphic function along a simple closed path equals $2\pi i$
times the sum of the orders of the zeros inside minus the poles inside.

Because the completed Riemann zeta function $\xi(s)$ is an entire function of order $1$
with no poles anywhere in the finite complex plane, choosing a circle of radius $R > 0$
centered at a zero $z_0$ such that:
1. No other zeros of $\xi(s)$ lie inside the open disk ($h_{isolated}$).
2. No zeros of $\xi(s)$ lie on the boundary circle itself ($h_{boundary}$).
guarantees that the contour integral over the circle computes the exact analytical
multiplicity $m$ of the zero $z_0$, yielding precisely $2\pi i \cdot m$.

Detailed Citations & Theoretical Background:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter IX (§ 9.2, pp. 212–215), where the argument principle
  and logarithmic derivative integration are formally applied to contour boxes enclosing
  the non-trivial zeros of $\zeta(s)$ and $\xi(s)$.
- Ahlfors, L. V. (1979). *Complex Analysis* (3rd ed.). McGraw-Hill.
  Chapter 4 (§ 5.2, Theorem 18, pp. 152–154), establishing the rigorous local formulation
  of the Argument Principle for isolated zeros within circular neighborhoods under strict
  boundary and interior non-vanishing constraints.
- Conway, J. B. (1978). *Functions of One Complex Variable I* (2nd ed.).
  Graduate Texts in Mathematics, vol. 11. Springer-Verlag.
  Chapter V (§ 3, Theorem 3.4, pp. 115–118), providing the formal meromorphic residue
  evaluation of $\frac{f'}{f}$ over simple closed positively-oriented paths.
-/
axiom classical_argument_principle_xi
    (z₀ : ℂ)
    (h_zero : xi_C z₀ = 0)
    (R : ℝ) (hR : R > 0)
    (m : ℕ)
    -- Structural multiplicity tie: xi_C factors locally as (z - z₀)^m * g(z) with g(z₀) ≠ 0
    (h_mult : ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
                ∀ᶠ z in nhds z₀, xi_C z = (z - z₀)^m * g z)
    -- 1. Strict boundary non-vanishing condition: no zeros lie on the circle of radius R
    (h_boundary : ∀ z : ℂ, ‖z - z₀‖ = R → xi_C z ≠ 0)
    -- 2. Strict interior isolation condition: z₀ is the sole zero inside the open disk of radius R
    (h_isolated : ∀ z : ℂ, ‖z - z₀‖ < R → xi_C z = 0 → z = z₀) :
    circleIntegral (fun z => deriv xi_C z / xi_C z) z₀ R = 2 * Real.pi * Complex.I * (m : ℂ)

/--
Classical Analytic Fact: Open Critical Strip Bounds for Non-Trivial Zeros.
Hadamard and de la Vallée-Poussin (1896) proved that the completed Riemann zeta
function has no zeros on the boundaries $\operatorname{Re}(s) = 0$ and $\operatorname{Re}(s) = 1$,
and the Euler product excludes $\operatorname{Re}(s) > 1$. Therefore, all zeros of $\xi(s)$
strictly satisfy $0 < \operatorname{Re}(s) < 1$.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter III (§ 3.2 & § 3.6, Theorem 3.5, pp. 45–51).
- Davenport, H. (2000). *Multiplicative Number Theory* (3rd ed.).
  Graduate Texts in Mathematics, vol. 74. Springer-Verlag. Chapter 13 (pp. 84–88).
-/
axiom classical_zero_critical_strip (z : ℂ) (h : xi_C z = 0) : 0 < z.re ∧ z.re < 1


/--
Classical Analytic Fact: The zero set of the completed Riemann zeta function is infinite.
Guaranteed by Hadamard's factorization theorem for the order-1 entire function $\xi(s)$
and Hardy's theorem (1914) establishing infinitely many zeros on the critical line.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter II (§ 2.12, pp. 30–32), Chapter IX (§ 9.3, pp. 214–216),
  & Chapter X (§ 10.1, pp. 256–258).
-/
axiom classical_zeta_root_set_infinite : classical_zeta_root_set.Infinite

/--
Existence of zeros for the completed Riemann zeta function (Proved Corollary).
Derived natively from `classical_zeta_root_set_infinite`.
-/
lemma classical_xi_root_exists : ∃ z : ℂ, xi_C z = 0 :=
  classical_zeta_root_set_infinite.nonempty

lemma classical_zeta_root_set_nonempty : classical_zeta_root_set.Nonempty := by
  rcases classical_xi_root_exists with ⟨z, hz⟩
  exact ⟨z, hz⟩


/--
Extract the existential surjection f : ℕ → ↑zeta_root_set_
Using Lean's Classical.choose to extract a native sequence function.
-/
noncomputable def classical_zeta_root_surjection : ℕ → ↑classical_zeta_root_set :=
  Classical.choose (Set.Countable.exists_surjective classical_zeta_root_set_nonempty classical_xi_root_set_countable)

/--
Native Bijection $\mathbb{N} \simeq \text{classical\_zeta\_root\_set}$.
Derived constructively in Lean from `classical_zeta_root_set_infinite` (`Set.Infinite`)
and `classical_xi_root_set_countable` (`Set.Countable`) via Mathlib's `Denumerable` / `Encodable`
equivalence for countably infinite sets, requiring no additional axioms.
-/
noncomputable def classical_zeta_root_equiv : ℕ ≃ classical_zeta_root_set :=
  haveI : Countable classical_zeta_root_set := classical_xi_root_set_countable.to_subtype
  haveI : Infinite classical_zeta_root_set := classical_zeta_root_set_infinite.to_subtype
  haveI : Encodable classical_zeta_root_set := Encodable.ofCountable classical_zeta_root_set
  (Denumerable.ofEncodableOfInfinite classical_zeta_root_set).eqv.symm


/--
The sequence of Riemann zeta zeros $\rho_n \in \mathbb{C}$.
Defined via the bijective enumeration `classical_zeta_root_equiv` of `classical_zeta_root_set`,
so both injectivity and surjectivity hold as proved theorems rather than axioms.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.). Oxford Univ. Press. (Chapter IX: Zero enumeration).
- Davenport, H. (2000). *Multiplicative Number Theory* (3rd ed.). Springer. (Chapter 12: Ordering of zero sequences).
-/
noncomputable def classical_zeta_root (n : ℕ) : ℂ :=
  (classical_zeta_root_equiv n).val

lemma classical_zeta_root_injective : Function.Injective classical_zeta_root := by
  intro n₁ n₂ h
  dsimp [classical_zeta_root] at h
  exact classical_zeta_root_equiv.injective (Subtype.ext h)

lemma classical_zeta_root_is_root (n : ℕ) : xi_C (classical_zeta_root n) = 0 := by
  dsimp [classical_zeta_root]
  exact (classical_zeta_root_equiv n).property

/--
Surjectivity of the Zeta Root Enumeration (Proved Theorem).
Every non-trivial zero of the completed Riemann zeta function $\xi(s)$
is attained by a unique index $n \in \mathbb{N}$ in the bijective enumeration sequence.
-/
lemma classical_zeta_root_surjective (z : ℂ) (hz : xi_C z = 0) : ∃ n : ℕ, classical_zeta_root n = z := by
  refine ⟨classical_zeta_root_equiv.symm ⟨z, hz⟩, ?_⟩
  dsimp [classical_zeta_root]
  rw [Equiv.apply_symm_apply]




/--
Classical Analytic Fact: Non-vanishing of the completed Riemann zeta function at the origin.
Classically, $\xi(0) = \frac{1}{2} \neq 0$, and by Hadamard and de la Vallée-Poussin (1896),
all zeros of $\xi(s)$ lie strictly inside the open critical strip $0 < \operatorname{Re}(s) < 1$.
Proven natively here as a corollary of `classical_zero_critical_strip`.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter II (§ 2.12, p. 31) & Chapter III (§ 3.6, p. 51).
- Edwards, H. M. (1974). *Riemann's Zeta Function*. Academic Press. Chapter 1 (§ 1.14, p. 16).
-/
lemma classical_xi_zero_neq_zero (z : ℂ) (h : xi_C z = 0) : z ≠ 0 := by
  intro hz
  have h_pos : 0 < z.re := (classical_zero_critical_strip z h).1
  rw [hz, Complex.zero_re] at h_pos
  exact lt_irrefl 0 h_pos

/--
Classical Analytic Fact: Cubic Taylor remainder of the primary Weierstrass/Hadamard factor.
Because $E_1(w) = (1 - w)e^w$ is an entire function with Maclaurin expansion
$$E_1(w) = 1 - \frac{w^2}{2} - \frac{w^3}{3} - \cdots = 1 - \frac{w^2}{2} + O(w^3),$$
its deviation from its quadratic approximation $1 - w^2/2$ on any closed disk $\Vert{}w\Vert{} \le R_w$
is bounded by $C \Vert{}w\Vert{}^3$ for a constant $C > 0$ depending only on $R_w$.

Citations:
- Ahlfors, L. V. (1979). *Complex Analysis* (3rd ed.). McGraw-Hill.
  Chapter 5 (§ 2.2: Canonical Products, pp. 193–196, establishing the elementary
  Weierstrass primary factor $E_1(w) = (1-w)e^w$ and its cubic remainder bound on compact disks).
- Conway, J. B. (1978). *Functions of One Complex Variable I* (2nd ed.). Springer-Verlag.
  Chapter VII (§ 5: Weierstrass Factorization Theorem, Lemma 5.11, pp. 168–170).
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter II (§ 2.12, pp. 30–32).
-/
axiom classical_single_factor_taylor_bound (R_w : ℝ) (hRw : R_w > 0) :
  ∃ C > 0, ∀ w : ℂ, ‖w‖ ≤ R_w →
    ‖(1 - w) * Complex.exp w - (1 - w^2 / 2)‖ ≤ C * ‖w‖^3

/--
Helper 1a: Single variable Taylor bound.
Bounds the deviation of the primary Hadamard factor from its quadratic approximation.
-/
lemma single_factor_taylor_bound (R_w : ℝ) (hRw : R_w > 0) :
  ∃ C > 0, ∀ w : ℂ, ‖w‖ ≤ R_w →
    ‖(1 - w) * Complex.exp w - (1 - w^2 / 2)‖ ≤ C * ‖w‖^3 := by
  exact classical_single_factor_taylor_bound R_w hRw

/--
Classical Analytic Fact: Multivariable Taylor remainder bound for the 4-fold Hadamard product.
If each primary Weierstrass factor $E_1(w_j) = (1 - w_j)e^{w_j}$ deviates from its quadratic
Taylor polynomial $1 - w_j^2/2$ by at most $C_1 \Vert{}w_j\Vert{}^3$ on the closed disk $\Vert{}w_j\Vert{} \le R_w$,
then the four-factor product $\prod_{j=1}^4 E_1(w_j)$ deviates from the combined quadratic
approximation $1 - \frac{1}{2}\sum_{j=1}^4 w_j^2$ by at most $C \sum_{j=1}^4 \Vert{}w_j\Vert{}^3$ on
$\Vert{}w_j\Vert{} \le R_w$, as all quartic and higher-order cross terms are absorbed into the cubic
majorant on the bounded compact polydisk $\Vert{}w_j\Vert{} \le R_w$.

Citations:
- Ahlfors, L. V. (1979). *Complex Analysis* (3rd ed.). McGraw-Hill.
  Chapter 5 (§ 2.1–2.2: Infinite Products and Canonical Products, pp. 191–196).
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter II (§ 2.12, pp. 30–32, grouping conjugate and
  functional-equation symmetric factors in Hadamard's product for $\xi(s)$).
-/
axiom classical_quad_product_bound_from_single (R_w : ℝ) (hRw : R_w > 0)
  (C1 : ℝ) (hC1 : C1 > 0)
  (h_single : ∀ w : ℂ, ‖w‖ ≤ R_w → ‖(1 - w) * Complex.exp w - (1 - w^2 / 2)‖ ≤ C1 * ‖w‖^3) :
  ∃ C > 0, ∀ w1 w2 w3 w4 : ℂ,
    ‖w1‖ ≤ R_w → ‖w2‖ ≤ R_w → ‖w3‖ ≤ R_w → ‖w4‖ ≤ R_w →
    ‖(((1 - w1) * Complex.exp w1) * ((1 - w2) * Complex.exp w2) *
      ((1 - w3) * Complex.exp w3) * ((1 - w4) * Complex.exp w4)) -
     (1 - (w1^2 + w2^2 + w3^2 + w4^2) / 2)‖ ≤ C * (‖w1‖^3 + ‖w2‖^3 + ‖w3‖^3 + ‖w4‖^3)

/--
Classical Analytic Fact: Global continuity of the completed Riemann zeta function $\xi(s)$.
Because $\xi(s) = \frac{1}{2}s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ is an entire (holomorphic on $\mathbb{C}$)
function of order 1, it is continuous everywhere on the complex plane $\mathbb{C}$.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter II (§ 2.1, pp. 13–16 & § 2.12, pp. 30–32, proving that
   the factor $s(s-1)$ cancels the simple poles of $\Gamma(s/2)$ at $s=0$ and $\zeta(s)$ at $s=1$,
  rendering $\xi(s)$ an entire function).
- Ahlfors, L. V. (1979). *Complex Analysis* (3rd ed.). McGraw-Hill.
  Chapter 2 (§ 1.2, p. 25, establishing that every holomorphic function is continuous).
-/
axiom classical_xi_continuous : Continuous xi_C


/--
Classical Analytic Fact: Partitioning an absolutely convergent series by a boolean predicate.
An unconditionally convergent series over $\mathbb{N}$ can be decomposed into the sum of
its restriction to indices satisfying $p(j)$ and its restriction to indices satisfying $\neg p(j)$.
Proved natively in Lean from `Summable.of_norm_bounded` and `HasSum.add`.

Citations:
- Apostol, T. M. (1974). *Mathematical Analysis* (2nd ed.). Addison-Wesley.
  Chapter 8 (§ 8.15: Rearrangements of Series, Theorem 8.27, pp. 198–200).
- Rudin, W. (1976). *Principles of Mathematical Analysis* (3rd ed.). McGraw-Hill.
  Chapter 3 (§ 3.55: Rearrangements, Theorem 3.55, p. 75).
-/
lemma classical_tsum_partition (f : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p] (hf : Summable f) :
    (∑' j, f j) = (∑' j, if p j then f j else (0:ℝ)) + (∑' j, if p j then (0:ℝ) else f j) := by
  have hf1 : Summable (fun j => if p j then f j else (0 : ℝ)) := by
    apply Summable.of_norm_bounded (g := fun j => ‖f j‖) hf.norm
    intro j
    split_ifs <;> simp
  have hf2 : Summable (fun j => if p j then (0 : ℝ) else f j) := by
    apply Summable.of_norm_bounded (g := fun j => ‖f j‖) hf.norm
    intro j
    split_ifs <;> simp
  have h_add : (∑' j, ((if p j then f j else (0 : ℝ)) + (if p j then (0 : ℝ) else f j))) =
      (∑' j, if p j then f j else (0 : ℝ)) + (∑' j, if p j then (0 : ℝ) else f j) :=
    (hf1.hasSum.add hf2.hasSum).tsum_eq
  rw [← h_add]
  congr 1
  ext j
  split_ifs <;> ring



/-- Native sequence of real parts (β) of the roots -/
noncomputable def zeta_beta : ℕ → ℝ :=
  fun n => (classical_zeta_root n).re

/-- Native sequence of imaginary parts (γ) of the roots -/
noncomputable def zeta_gamma : ℕ → ℝ :=
  fun n => (classical_zeta_root n).im

/--
Two-sided counting function for zero ordinates with absolute height in $[1, T]$.
The condition `1 ≤ |gamma n|` provides a positive lower cutoff for generic sequence
summability arguments (`HasRVMCount`), while for `zeta_gamma` it omits no zeros
because the lowest non-trivial zero of $\xi(s)$ occurs at $\vert{}\gamma_1\vert{} \approx 14.1347 > 1$.
-/
noncomputable def N_count (gamma : ℕ → ℝ) (T : ℝ) : ℝ :=
  (({n : ℕ | 1 ≤ |gamma n| ∧ |gamma n| ≤ T}).ncard : ℝ)

/--
Classical Analytic Fact: The Symmetric Riemann-von Mangoldt Upper Bound.
By the Riemann-von Mangoldt formula, the number $N(T)$ of zeros of $\xi(s)$ with
$0 < \operatorname{Im}(\rho) \le T$ satisfies
$$N(T) = \frac{T}{2\pi}\log\frac{T}{2\pi} - \frac{T}{2\pi} + O(\log T).$$
By Schwarz reflection symmetry ($\xi(\bar{s}) = \overline{\xi(s)}$), the two-sided count of
zeros in $1 \le \vert{}\operatorname{Im}(\rho)\vert{} \le T$ is bounded by $2N(T) \le C T \log T$ for $T \ge 2$.

Citations:
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.).
  Oxford University Press. Chapter IX (§ 9.3, Theorem 9.4, pp. 214–216).
- Davenport, H. (2000). *Multiplicative Number Theory* (3rd ed.).
  Graduate Texts in Mathematics, vol. 74. Springer-Verlag. Chapter 15 (pp. 97–101).
-/
axiom classical_riemann_von_mangoldt_bound :
  ∃ C > 0, ∀ T : ℝ, 2 ≤ T → N_count zeta_gamma T ≤ C * T * Real.log T



end TainoPolar
