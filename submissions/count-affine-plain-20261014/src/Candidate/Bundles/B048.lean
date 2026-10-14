/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B047
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import OAI.NumberTheory.DirichletL.Detector.Euler
import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrictSelected
import OAI.NumberTheory.DirichletL.Detector.HighRowsClosed
import OAI.NumberTheory.DirichletL.Detector.Local

/- BEGIN ORIGINAL Cycle25.Numerator.AmplitudeHolder; sha256 11a7b2343e9ee26019a9346cc02fd816c79e1ccf3556a046a03b4c5c7c8823f8 -/
section
                               
                                
                                                 

/-! Exact amplitude-bin exponent extracted from the weighted fourth moment. -/
noncomputable section
open scoped BigOperators
namespace Cycle25.Numerator

theorem rpow_fourth (U e : ℝ) (hU : 0 ≤ U) : (U^e)^4 = U^(4*e) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hU]
  congr 1
  ring

theorem weighted_amplitude_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (U R total selected epsilon Ccount Cmoment : ℝ)
    (hU : 0 < U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^selected ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^total)
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(total-selected/2+(3*R+1+epsilon)/4) := by
  have hL : 0 < U^selected := Real.rpow_pos_of_pos hU _
  have hh := weighted_row_holder_with_full s S Q P (U^selected) (U^total)
    hL.le (Real.rpow_nonneg hU.le _) hselected hfull
  have hpow (e : ℝ) (n : ℕ) : (U^e)^n = U^(e*n) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
  have hcomb : (U^total)^4 * (Ccount * U^R)^3 * (Cmoment * U^(1+epsilon)) =
      Ccount^3 * Cmoment * U^(4*total+3*R+1+epsilon) := by
    rw [mul_pow,hpow,hpow]
    rw [show total*(4:ℕ) = 4*total by ring,show R*(3:ℕ) = 3*R by ring]
    calc
      _ = Ccount^3 * Cmoment * ((U^(4*total) * U^(3*R))*U^(1+epsilon)) := by ring
      _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU]; congr 2; ring
  have htarget : (U^selected)^2 *
      (Ccount*Cmoment*U^(total-selected/2+(3*R+1+epsilon)/4))^4 =
      Ccount^4 * Cmoment^4 * U^(4*total+3*R+1+epsilon) := by
    rw [mul_pow,mul_pow,hpow,hpow]
    calc
      _ = Ccount^4 * Cmoment^4 *
          (U^(selected*2) * U^((total-selected/2+(3*R+1+epsilon)/4)*4)) := by ring
      _ = _ := by rw [←Real.rpow_add hU]; congr 2; ring
  have hconst : Ccount^3 * Cmoment ≤ Ccount^4 * Cmoment^4 := by
    have hc0 : 0 ≤ Ccount := le_trans zero_le_one hc
    have hm0 : 0 ≤ Cmoment := le_trans zero_le_one hm
    have hc' : Ccount^3 ≤ Ccount^4 := pow_le_pow_right₀ hc (by norm_num)
    have hm' : Cmoment ≤ Cmoment^4 := by
      simpa only [pow_one] using pow_le_pow_right₀ hm (show 1 ≤ 4 by norm_num)
    exact mul_le_mul hc' hm' hm0 (by positivity)
  have hh' : (U^selected)^2 * (∑ i ∈ s, ‖S i * P i‖)^4 ≤
      (U^selected)^2 * (Ccount*Cmoment*U^(total-selected/2+(3*R+1+epsilon)/4))^4 := by
    calc
      _ ≤ (U^total)^4 * (s.card : ℝ)^3 * (Cmoment * U^(1+epsilon)) :=
        hh.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
      _ ≤ (U^total)^4 * (Ccount*U^R)^3 * (Cmoment * U^(1+epsilon)) := by
        gcongr
      _ = Ccount^3*Cmoment*U^(4*total+3*R+1+epsilon) := hcomb
      _ ≤ Ccount^4*Cmoment^4*U^(4*total+3*R+1+epsilon) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hU.le _)
      _ = _ := htarget.symm
  have hf := (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp hh'
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
    (by norm_num : (4 : ℕ) ≠ 0)).mp hf

/-- A bounded dilation box pays for the lost selected-prime capacity.  The
box width xi appears only as the explicit small exponent loss delta*xi/4. -/
theorem weighted_dilation_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (κ U R q L z v xi delta loss epsilon Ccount Cmoment : ℝ)
    (hκ : 7 / 10 ≤ κ)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) (hxi : 0 ≤ xi)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^(q*selectedCapacity κ z (v+xi)-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    U^(-delta*v/4) * (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4-
        11*delta*(v+xi)/84) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hh := weighted_amplitude_bin s S Q P U R (q*L)
    (q*selectedCapacity κ z (v+xi)-loss) epsilon Ccount Cmoment hU0 hc hm
    hcard hselected hfull henergy
  have hd := capacity_damping_uniform hκ hq hqdelta (add_nonneg hv hxi) (z := z)
  calc
    _ ≤ U^(-delta*v/4) *
        (Ccount*Cmoment*U^(q*L-(q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = (Ccount*Cmoment) * (U^(-delta*v/4) *
        U^(q*L-(q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4)) := by ring
    _ = Ccount*Cmoment*U^(-delta*v/4+q*L-
        (q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←Real.rpow_add hU0]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.AmplitudeHolder -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorLocalCoefficients; sha256 e3bfb0b967d5c587dcdf520952fe04446b512da94aaeaa3b91e5c23ded8b16cc -/
section
                                                 
                                                 
                                                          
                     

/-! Exact finite coefficient expansions of the original local numerator factors.

The local variable is `T = Q^(-w)`.  All coefficients below are independent of `T`.
We use finite lists of terms, so no cancellation is lost by replacing a polynomial by
its values on a vertical line.  These lemmas refer directly to the original continued
correction and compensated replacement.
-/

noncomputable section
open scoped BigOperators
namespace Cycle25.Weighted.Numerator
open OAI.SevenEighths ProbeLocal ProbeEuler

def affine (a b T : ℂ) : ℂ := a + b * T
def quadratic (a b c T : ℂ) : ℂ := a + b * T + c * T ^ 2
def cubic (a b c d T : ℂ) : ℂ := a + b * T + c * T ^ 2 + d * T ^ 3

/-- The two coefficients of the marked defect after the original unramified
cancellation. -/
def markedDefectConstant (R V qInv D : ℂ) : ℂ :=
  (R * (1 - qInv) / (1 - V) - D * R) / (1 - R)
def markedDefectLinear (R V chi K : ℂ) : ℂ :=
  (chi * R - K * V / (1 - V)) / (1 - R)

theorem marked_defect_affine (R V qInv D chi K T : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv (K * T) (-D + chi * T * R) 1 + D =
      affine (markedDefectConstant R V qInv D) (markedDefectLinear R V chi K) T := by
  unfold markedFactor affine markedDefectConstant markedDefectLinear
  simp only [pow_one]
  field_simp
  ring

def correctionDefectConstant (V D E₀ : ℂ) : ℂ :=
  (D * V + (1 - V) * E₀) / (1 - D)
def correctionDefectLinear (V D chi E₀ E₁ : ℂ) : ℂ :=
  (D * chi * (1 - V) - V * chi + (1 - V) * (E₁ - chi * E₀)) / (1 - D)
def correctionDefectQuadratic (V D chi E₁ : ℂ) : ℂ :=
  (-(1 - V) * chi * E₁) / (1 - D)

theorem correction_defect_quadratic (V D chi E₀ E₁ T : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V (chi * T) D (affine E₀ E₁ T - D) - 1 =
      quadratic (correctionDefectConstant V D E₀)
        (correctionDefectLinear V D chi E₀ E₁)
        (correctionDefectQuadratic V D chi E₁) T := by
  unfold continuedCorrection affine quadratic correctionDefectConstant
    correctionDefectLinear correctionDefectQuadratic
  field_simp
  ring

/-- Coefficients of the error bracket after the exact normalized cancellation. -/
def errorBracketConstant (V D B nu E₀ : ℂ) : ℂ :=
  nu * (V / (1 - V) - D) + (B + nu) * E₀
def errorBracketLinear (V D B nu E₀ E₁ : ℂ) : ℂ :=
  -(V / (1 - V) - D) + (B + nu) * E₁ - E₀
def errorBracketQuadratic (E₁ : ℂ) : ℂ := -E₁

theorem compensated_error_cubic (V D chi B nu E₀ E₁ T : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = nu) (hchi : nu * chi = 1) :
    compensatedReplacement V (chi * T) D (affine E₀ E₁ T - D) B T +
      continuedCorrection V (chi * T) D (affine E₀ E₁ T - D) * nu =
    let c := (1 - V) / (1 - D)
    let a := errorBracketConstant V D B nu E₀
    let b := errorBracketLinear V D B nu E₀ E₁
    let d := errorBracketQuadratic E₁
    cubic (c * a) (c * (b - chi * a)) (c * (d - chi * b))
      (-c * chi * d) T := by
  have hvW : nu * (chi * T) = T := by rw [← mul_assoc, hchi, one_mul]
  rw [continued_normalized_cancellation _ _ _ _ _ _ _ hV hD hBD hvW]
  dsimp only
  unfold affine cubic errorBracketConstant errorBracketLinear errorBracketQuadratic
  ring

/-- The ramified replacement is quadratic, including its strict term. -/
theorem ramified_error_quadratic (V B A C T : ℂ) :
    compensatedReplacement V 0 0 (affine A C T) B T =
      quadratic (B * (1 - V) * A)
        (B * (1 - V) * C - 1 - (1 - V) * A)
        (-(1 - V) * C) T := by
  simp only [compensatedReplacement, affine, quadratic, mul_zero, sub_zero,
    mul_one, div_one]
  ring

theorem norm_affine_le (a b T : ℂ) :
    ‖affine a b T‖ ≤ ‖a‖ + ‖b‖ * ‖T‖ := by
  simpa only [affine, norm_mul] using norm_add_le a (b * T)

theorem norm_quadratic_le (a b c T : ℂ) :
    ‖quadratic a b c T‖ ≤ ‖a‖ + ‖b‖ * ‖T‖ + ‖c‖ * ‖T‖ ^ 2 := by
  calc
    _ ≤ ‖a + b * T‖ + ‖c * T ^ 2‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_pow]
      exact add_le_add (norm_affine_le a b T) le_rfl

theorem norm_cubic_le (a b c d T : ℂ) :
    ‖cubic a b c d T‖ ≤
      ‖a‖ + ‖b‖ * ‖T‖ + ‖c‖ * ‖T‖ ^ 2 + ‖d‖ * ‖T‖ ^ 3 := by
  calc
    _ ≤ ‖a + b * T + c * T ^ 2‖ + ‖d * T ^ 3‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_pow]
      exact add_le_add (norm_quadratic_le a b c T) le_rfl

section ActualMarkedRow
open OAI.ActualEisensteinCubic OAI.CompletedGauss
open OAI.ConcretePrimeRowBridge OAI.SevenEighths.ProbePrimePower
local notation "O" => OAI.ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

/-- Every original marked term has exactly the declared degree in `Q^(-w)`. -/
theorem rowMarkedTerm_monomial (eta a X W V rho : ℂ) (j e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho j e l k m =
      rowMarkedTerm p hp hg eta a X 1 V rho j e l k m * W ^ k := by
  unfold rowMarkedTerm
  split_ifs
  · simp
  · unfold rowWeightedScalar weightedScalar
    simp only [one_pow, mul_one]
    ring

/-- The closed marked factor is genuinely affine in the Mellin local variable,
including ramified rows.  This derives the degree bound from the original Gauss
sum definition, rather than imposing it as a hypothesis. -/
theorem rowClosedMarked_affine (eta a X W V rho : ℂ) (j : ℕ) :
    rowClosedMarked p hp hg eta a X W V rho j =
      rowClosedMarked p hp hg eta a X 0 V rho j +
        (rowClosedMarked p hp hg eta a X 1 V rho j -
          rowClosedMarked p hp hg eta a X 0 V rho j) * W := by
  unfold rowClosedMarked rowBaseFinite
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  norm_num only [rowMarkedTerm, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff,
    if_false, rowWeightedScalar, weightedScalar, pow_zero, pow_one,
    zero_pow, one_pow, mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero]
  ring

end ActualMarkedRow
end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorLocalCoefficients -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorPolynomialMass; sha256 5283db55bb578f8ff55621f5ad642c5be4de438ea1ff46bd2af1e1e2161f6ed2 -/
section
                                                            
                                                    
                                                 

/-! A finite Fourier extraction of coefficient mass from a uniform local bound.
Unlike a pointwise estimate at a single `w`, the four evaluations below determine
all coefficients of the local quadratic polynomial. -/
noncomputable section
namespace Cycle25.Weighted.Numerator

private theorem average_four_norm_le (a b c d : ℂ) (B : ℝ)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) :
    ‖(a + b + c + d) / 4‖ ≤ B := by
  rw [norm_div]
  rw [show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have h := (norm_add_le (a + b + c) d).trans
    (add_le_add ((norm_add_le (a + b) c).trans
      (add_le_add (norm_add_le a b) le_rfl)) le_rfl)
  linarith

theorem quadratic_coefficients_of_four_bounds (a b c : ℂ) (B : ℝ)
    (h₁ : ‖quadratic a b c 1‖ ≤ B) (h₂ : ‖quadratic a b c (-1)‖ ≤ B)
    (h₃ : ‖quadratic a b c Complex.I‖ ≤ B)
    (h₄ : ‖quadratic a b c (-Complex.I)‖ ≤ B) :
    ‖a‖ ≤ B ∧ ‖b‖ ≤ B ∧ ‖c‖ ≤ B := by
  have ha : a = (quadratic a b c 1 + quadratic a b c (-1) +
      quadratic a b c Complex.I + quadratic a b c (-Complex.I)) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring
  have hb : b = (quadratic a b c 1 + -(quadratic a b c (-1)) +
      (-Complex.I * quadratic a b c Complex.I) +
      (Complex.I * quadratic a b c (-Complex.I))) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hc : c = (quadratic a b c 1 + quadratic a b c (-1) +
      -(quadratic a b c Complex.I) + -(quadratic a b c (-Complex.I))) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]
    exact average_four_norm_le _ _ _ _ B h₁ h₂ h₃ h₄
  · rw [hb]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₄
  · rw [hc]
    exact average_four_norm_le _ _ _ _ B h₁ h₂
      (by simpa only [norm_neg] using h₃) (by simpa only [norm_neg] using h₄)

def quadraticMass (a b c : ℂ) (r : ℝ) : ℝ := ‖a‖ + ‖b‖ * r + ‖c‖ * r ^ 2

theorem quadraticMass_le_of_circle_bound (a b c : ℂ) (r B : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ T : ℂ, ‖T‖ = r → ‖quadratic a b c T‖ ≤ B) :
    quadraticMass a b c r ≤ 3 * B := by
  have he (T : ℂ) : quadratic a (b * r) (c * (r : ℂ) ^ 2) T =
      quadratic a b c ((r : ℂ) * T) := by unfold quadratic; ring
  have hn (T : ℂ) (hT : ‖T‖ = 1) : ‖(r : ℂ) * T‖ = r := by
    rw [norm_mul, hT, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hh := quadratic_coefficients_of_four_bounds a (b * r) (c * (r : ℂ) ^ 2) B
    (by rw [he]; exact hbound _ (hn 1 (by simp)))
    (by rw [he]; exact hbound _ (hn (-1) (by simp)))
    (by rw [he]; exact hbound _ (hn Complex.I (by simp)))
    (by rw [he]; exact hbound _ (hn (-Complex.I) (by simp)))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hh
  unfold quadraticMass
  linarith [hh.1, hh.2.1, hh.2.2]

theorem quadraticMass_mono (a b c : ℂ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    quadraticMass a b c r ≤ quadraticMass a b c s := by
  unfold quadraticMass
  gcongr

/-- The complete vertical line visits the complete circle in the local variable.
This is why a bound uniform in the imaginary part really does control every local
coefficient, once the finite degree is known. -/
theorem vertical_cpow_surjective (Q sigma : ℝ) (hQ : 1 < Q) (T : ℂ)
    (hT : ‖T‖ = Q ^ (-sigma)) :
    ∃ w : ℂ, w.re = sigma ∧ (Q : ℂ) ^ (-w) = T := by
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
  have hlog : Real.log Q ≠ 0 := ne_of_gt (Real.log_pos hQ)
  have hT0 : T ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hT
    exact (Real.rpow_pos_of_pos hQ0 (-sigma)).ne' hT.symm
  refine ⟨-Complex.log T / (Real.log Q : ℂ), ?_, ?_⟩
  · rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re, hT,
      Real.rpow_def_of_pos hQ0, Real.log_exp]
    field_simp
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hQ0.ne'),
      ← Complex.ofReal_log hQ0.le]
    have hlogC : (Real.log Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
    have he : (Real.log Q : ℂ) * -(-Complex.log T / (Real.log Q : ℂ)) =
        Complex.log T := by field_simp
    rw [he, Complex.exp_log hT0]

/-- A uniform bound on one vertical line controls the absolute quadratic
coefficient mass, and all lines to its right. -/
theorem quadraticMass_le_of_vertical_bound (Q sigma tau B : ℝ) (a b c : ℂ)
    (hQ : 1 < Q) (hst : sigma ≤ tau)
    (hbound : ∀ w : ℂ, w.re = sigma →
      ‖quadratic a b c ((Q : ℂ) ^ (-w))‖ ≤ B) :
    quadraticMass a b c (Q ^ (-tau)) ≤ 3 * B := by
  apply (quadraticMass_mono a b c (Q ^ (-tau)) (Q ^ (-sigma))
    (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith))).trans
  apply quadraticMass_le_of_circle_bound a b c _ B (Real.rpow_nonneg (by linarith) _)
  intro T hT
  obtain ⟨w, hw, he⟩ := vertical_cpow_surjective Q sigma hQ T hT
  rw [← he]
  exact hbound w hw

theorem cubic_coefficients_of_four_bounds (a b c d : ℂ) (B : ℝ)
    (h₁ : ‖cubic a b c d 1‖ ≤ B) (h₂ : ‖cubic a b c d (-1)‖ ≤ B)
    (h₃ : ‖cubic a b c d Complex.I‖ ≤ B)
    (h₄ : ‖cubic a b c d (-Complex.I)‖ ≤ B) :
    ‖a‖ ≤ B ∧ ‖b‖ ≤ B ∧ ‖c‖ ≤ B ∧ ‖d‖ ≤ B := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]; ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.I_sq]; norm_num
  have ha : a = (cubic a b c d 1 + cubic a b c d (-1) +
      cubic a b c d Complex.I + cubic a b c d (-Complex.I)) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [hI3]
  have hb : b = (cubic a b c d 1 + -(cubic a b c d (-1)) +
      (-Complex.I * cubic a b c d Complex.I) +
      (Complex.I * cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [Complex.I_sq, hI3, hI4]
    ring
  have hc : c = (cubic a b c d 1 + cubic a b c d (-1) +
      -(cubic a b c d Complex.I) + -(cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [hI3]
  have hd : d = (cubic a b c d 1 + -(cubic a b c d (-1)) +
      (Complex.I * cubic a b c d Complex.I) +
      (-Complex.I * cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [Complex.I_sq, hI3, hI4]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]
    exact average_four_norm_le _ _ _ _ B h₁ h₂ h₃ h₄
  · rw [hb]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₄
  · rw [hc]
    exact average_four_norm_le _ _ _ _ B h₁ h₂
      (by simpa only [norm_neg] using h₃) (by simpa only [norm_neg] using h₄)
  · rw [hd]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₄

def cubicMass (a b c d : ℂ) (r : ℝ) : ℝ :=
  ‖a‖ + ‖b‖ * r + ‖c‖ * r ^ 2 + ‖d‖ * r ^ 3

theorem cubicMass_le_of_circle_bound (a b c d : ℂ) (r B : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ T : ℂ, ‖T‖ = r → ‖cubic a b c d T‖ ≤ B) :
    cubicMass a b c d r ≤ 4 * B := by
  have he (T : ℂ) : cubic a (b * r) (c * (r : ℂ) ^ 2) (d * (r : ℂ) ^ 3) T =
      cubic a b c d ((r : ℂ) * T) := by unfold cubic; ring
  have hn (T : ℂ) (hT : ‖T‖ = 1) : ‖(r : ℂ) * T‖ = r := by
    rw [norm_mul, hT, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hh := cubic_coefficients_of_four_bounds a (b * r) (c * (r : ℂ) ^ 2)
    (d * (r : ℂ) ^ 3) B
    (by rw [he]; exact hbound _ (hn 1 (by simp)))
    (by rw [he]; exact hbound _ (hn (-1) (by simp)))
    (by rw [he]; exact hbound _ (hn Complex.I (by simp)))
    (by rw [he]; exact hbound _ (hn (-Complex.I) (by simp)))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hh
  unfold cubicMass
  linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]

theorem cubicMass_mono (a b c d : ℂ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    cubicMass a b c d r ≤ cubicMass a b c d s := by
  unfold cubicMass
  gcongr

theorem cubicMass_le_of_vertical_bound (Q sigma tau B : ℝ) (a b c d : ℂ)
    (hQ : 1 < Q) (hst : sigma ≤ tau)
    (hbound : ∀ w : ℂ, w.re = sigma →
      ‖cubic a b c d ((Q : ℂ) ^ (-w))‖ ≤ B) :
    cubicMass a b c d (Q ^ (-tau)) ≤ 4 * B := by
  apply (cubicMass_mono a b c d (Q ^ (-tau)) (Q ^ (-sigma))
    (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith))).trans
  apply cubicMass_le_of_circle_bound a b c d _ B (Real.rpow_nonneg (by linarith) _)
  intro T hT
  obtain ⟨w, hw, he⟩ := vertical_cpow_surjective Q sigma hQ T hT
  rw [← he]
  exact hbound w hw

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorPolynomialMass -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorRamifiedMass; sha256 d1d111256fa463d844ddc5abbb886703296f9e8b614410064e7442705bc7f530 -/
section
                                                         
                                                                         

/-! Actual coefficient bounds for ramified local errors.  The certified original
regular-error estimate is uniform on a vertical line.  Exact finite-degree
extraction turns that estimate into the coefficient bound needed before the
physical numerator is reconstructed. -/
noncomputable section
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

structure QuadraticCoefficients where
  a : ℂ
  b : ℂ
  c : ℂ

def QuadraticCoefficients.eval (c : QuadraticCoefficients) (T : ℂ) : ℂ :=
  quadratic c.a c.b c.c T
def QuadraticCoefficients.mass (c : QuadraticCoefficients) (r : ℝ) : ℝ :=
  quadraticMass c.a c.b c.c r

def ramifiedRegularCoefficients (eta a rho x z : ℂ) (j : ℕ) : QuadraticCoefficients :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  let X := Q ^ (-x)
  let B := star eta * Q ^ x
  let P₀ := rowClosedMarked p hp hg eta a X 0 V rho j
  let P₁ := rowClosedMarked p hp hg eta a X 1 V rho j - P₀
  let S := B * (1 - V) *
    (rowMarkedTerm p hp hg eta a X 1 V rho j 1 0 1 0 /
      (1 - evenRatio (Ideal.absNorm (Ideal.span {p})) a X V))
  ⟨B * (1 - V) * P₀,
    B * (1 - V) * P₁ - 1 - (1 - V) * P₀ - S,
    -(1 - V) * P₁⟩

theorem ramified_regular_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j -
      ramifiedStrictSelected p hp hg eta a rho x w z j =
    (ramifiedRegularCoefficients p hp hg eta a rho x z j).eval
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hP := rowClosedMarked_affine p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j
  have hT := rowMarkedTerm_monomial p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0
  unfold ramifiedSelected ramifiedStrictSelected ramifiedClosed
  rw [hP, hT]
  simp only [pow_one]
  unfold QuadraticCoefficients.eval ramifiedRegularCoefficients quadratic
  ring

/-- No analytic estimate is assumed here: this coefficient mass follows from the
original regular-error theorem, applied on the complete old vertical line. -/
theorem ramified_regular_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (alpha eps sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hsigma : 1 - alpha - 6 * eps ≤ sigma) (j : ℕ) (hj : j < 6) :
    (ramifiedRegularCoefficients p hp hg eta a rho x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma)) ≤
      1155 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ) := by
  let c := ramifiedRegularCoefficients p hp hg eta a rho x z j
  have hb := quadraticMass_le_of_vertical_bound
    (Ideal.absNorm (Ideal.span {p}) : ℝ) (1 - alpha - 6 * eps) sigma
    (385 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ))
    c.a c.b c.c (by linarith) hsigma (by
      intro w hw
      have hh := ramifiedSelected_central_regular p hp hg hc eta a rho x w z
        alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j hj
      rw [ramified_regular_expansion p hp hg] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  nlinarith

def ramifiedStrictCoefficient (eta a rho x z : ℂ) (j : ℕ) : ℂ :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  star eta * Q ^ x * (1 - V) *
    (rowMarkedTerm p hp hg eta a (Q ^ (-x)) 1 V rho j 1 0 1 0 /
      (1 - evenRatio (Ideal.absNorm (Ideal.span {p})) a (Q ^ (-x)) V))

theorem ramified_strict_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedStrictSelected p hp hg eta a rho x w z j =
      ramifiedStrictCoefficient p hp hg eta a rho x z j *
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w) := by
  have ht := rowMarkedTerm_monomial p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0
  unfold ramifiedStrictSelected ramifiedStrictCoefficient
  rw [ht]
  simp only [pow_one]
  ring

/-- The only large coefficient is the original strict ramified coefficient. -/
theorem ramified_strict_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (j : ℕ) (hj : j < 6) :
    ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ *
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) ≤
      6 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 - sigma) := by
  have hh := ramifiedStrictSelected_central_norm p hp hg hc eta a rho x
    (sigma : ℂ) z hQ heta ha hρ hx hz j hj
  rw [ramified_strict_expansion p hp hg, norm_mul,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith :
      (0 : ℝ) < Ideal.absNorm (Ideal.span {p})), Complex.neg_re, Complex.ofReal_re] at hh
  exact hh

theorem ramified_boundary_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (j : ℕ) (hj : j ≤ 1) :
    ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ *
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) ≤
      6 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) := by
  have hh := ramifiedStrictSelected_boundary_norm p hp hg hc eta a rho x
    (sigma : ℂ) z hQ heta ha hρ hx hz j hj
  rw [ramified_strict_expansion p hp hg, norm_mul,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith :
      (0 : ℝ) < Ideal.absNorm (Ideal.span {p})), Complex.neg_re, Complex.ofReal_re] at hh
  exact hh

def ramifiedCorrectionCoefficients (eta a rho x z : ℂ) (j : ℕ) : QuadraticCoefficients :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  let P₀ := rowClosedMarked p hp hg eta a (Q ^ (-x)) 0 V rho j
  let P₁ := rowClosedMarked p hp hg eta a (Q ^ (-x)) 1 V rho j - P₀
  ⟨1 + (1 - V) * P₀, (1 - V) * P₁, 0⟩

theorem ramified_correction_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedClosed p hp hg eta a rho x w z j =
      (ramifiedCorrectionCoefficients p hp hg eta a rho x z j).eval
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hh := rowClosedMarked_affine p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j
  unfold ramifiedClosed
  rw [hh]
  unfold ramifiedCorrectionCoefficients QuadraticCoefficients.eval quadratic
  ring

theorem ramified_correction_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma)
    (j : ℕ) (hj : j < 6) :
    (ramifiedCorrectionCoefficients p hp hg eta a rho x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma)) ≤ 579 := by
  let c := ramifiedCorrectionCoefficients p hp hg eta a rho x z j
  have hb := quadraticMass_le_of_vertical_bound
    (Ideal.absNorm (Ideal.span {p}) : ℝ) sigma sigma 193 c.a c.b c.c
    (by linarith) le_rfl (by
      intro w hw
      have hh := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z
        hQ heta ha hρ hx (by rw [hw]; exact hsigma) hz (by rw [hw]; exact hxw) j hj
      rw [ramified_correction_expansion p hp hg] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  norm_num only [show (3 : ℝ) * 193 = 579 by norm_num] at hb
  exact hb

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorRamifiedMass -/
