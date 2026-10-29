/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.RadialSeparation
import Candidate.Local.Qrh.JointDetector.SelectedBilinear

/-!
# Actual radial kernels against the selected bilinear operator

Finite row/source dyads are separated inside the actual paper radial Fourier
kernel. The divisor expansion precedes the selected operator estimate.
The operator norm remains exact: no analytic selected-norm bound is assumed.
-/

namespace Qrh.JointDetector

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def radialLogPhase (t x y z : ℝ) : ℂ :=
  FourierBridge.logPhase t (-Real.log x) *
    FourierBridge.logPhase t (-Real.log y) *
    FourierBridge.logPhase t (Real.log z)

theorem radialLogPhase_norm (t x y z : ℝ) : ‖radialLogPhase t x y z‖ = 1 := by
  simp only [radialLogPhase, norm_mul, FourierBridge.logPhase_norm, mul_one]

theorem radialLogPhase_continuous (x y z : ℝ) :
    Continuous (fun t => radialLogPhase t x y z) :=
  ((FourierBridge.logPhase_continuous_left _).mul
    (FourierBridge.logPhase_continuous_left _)).mul
      (FourierBridge.logPhase_continuous_left _)

private theorem radial_phase_integrable (b : 𝓢(ℝ, ℂ))
    (hi : Integrable (fun t : ℝ => ‖b t‖) volume) (c : ℂ) (x y z : ℝ) :
    Integrable (fun t => c * (radialLogPhase t x y z * b t)) volume := by
  apply (hi.const_mul ‖c‖).mono'
    (continuous_const.mul ((radialLogPhase_continuous x y z).mul b.continuous)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    change ‖c * (radialLogPhase t x y z * b t)‖ ≤ ‖c‖ * ‖b t‖
    simp only [norm_mul, radialLogPhase_norm, one_mul, le_refl]

/-- Finite Fubini, with the actual radial transform still on the left. -/
theorem finite_radial_integral {J : Type*} [Fintype J]
    (W b : 𝓢(ℝ, ℂ)) (R : ℝ) (c : J → ℂ) (x y z : J → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (1 : ℝ) 2)
    (hy : ∀ j, y j ∈ Set.Icc (1 : ℝ) 2)
    (hz : ∀ j, z j ∈ Set.Icc (1 : ℝ) 2)
    (hi : Integrable (fun t : ℝ => ‖b t‖) volume)
    (hsep : ∀ x y z : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
      y ∈ Set.Icc (1 : ℝ) 2 → z ∈ Set.Icc (1 : ℝ) 2 →
      paperRadialFourier W (R * z / (x * y)) =
        ∫ t : ℝ, radialLogPhase t x y z * b t) :
    (∑ j, c j * paperRadialFourier W (R * z j / (x j * y j))) =
      ∫ t : ℝ, b t * ∑ j, c j * radialLogPhase t (x j) (y j) (z j) := by
  calc
    _ = ∑ j, ∫ t : ℝ, c j * (radialLogPhase t (x j) (y j) (z j) * b t) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hsep _ _ _ (hx j) (hy j) (hz j), integral_const_mul]
    _ = ∫ t : ℝ, ∑ j, c j * (radialLogPhase t (x j) (y j) (z j) * b t) :=
      (integral_finsetSum Finset.univ
        (fun j _ => radial_phase_integrable b hi (c j) (x j) (y j) (z j))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

def radialQuadCoefficient {E : Type*} (rows : Finset O) (sources : Finset (Ideal O))
    (mask : E → rows → Prop) [∀ e r, Decidable (mask e r)]
    (a c : rows → ℂ) (w : sources → ℂ) (μ : E → ℂ)
    (u : E × sources × rows × rows) : ℂ :=
  μ u.1 * w u.2.1 * maskedRowVector mask a u.1 u.2.2.1 *
    maskedRowVector mask c u.1 u.2.2.2 *
    star (selectedMatrix rows sources u.2.1 u.2.2.1) *
    selectedMatrix rows sources u.2.1 u.2.2.2

/-- The two coefficient masks are exactly the original simultaneous row selector. -/
theorem radialQuadCoefficient_eq_if {E : Type*}
    (rows : Finset O) (sources : Finset (Ideal O))
    (mask : E → rows → Prop) [∀ e r, Decidable (mask e r)]
    (a c : rows → ℂ) (w : sources → ℂ) (μ : E → ℂ)
    (u : E × sources × rows × rows) :
    radialQuadCoefficient rows sources mask a c w μ u =
      if mask u.1 u.2.2.1 ∧ mask u.1 u.2.2.2 then
        μ u.1 * w u.2.1 * a u.2.2.1 * c u.2.2.2 *
          star (selectedMatrix rows sources u.2.1 u.2.2.1) *
          selectedMatrix rows sources u.2.1 u.2.2.2
      else 0 := by
  unfold radialQuadCoefficient maskedRowVector
  by_cases hr : mask u.1 u.2.2.1 <;> by_cases hs : mask u.1 u.2.2.2 <;>
    simp [hr, hs]

/-- The expanded `(e,I,r,s)` quadform with the ACTUAL radial kernel. -/
def radialMaskedQuad {E : Type*} [Fintype E]
    (rows : Finset O) (sources : Finset (Ideal O))
    (mask : E → rows → Prop) [∀ e r, Decidable (mask e r)]
    (a c : rows → ℂ) (w : sources → ℂ) (μ : E → ℂ)
    (x : rows → ℝ) (z : sources → ℝ) (W : 𝓢(ℝ, ℂ)) (R : ℝ) : ℂ :=
  ∑ u : E × sources × rows × rows,
    radialQuadCoefficient rows sources mask a c w μ u *
      paperRadialFourier W (R * z u.2.1 / (x u.2.2.1 * x u.2.2.2))

def radialSeparatedBilinear {E : Type*} [Fintype E]
    (rows : Finset O) (sources : Finset (Ideal O))
    (mask : E → rows → Prop) [∀ e r, Decidable (mask e r)]
    (a c : rows → ℂ) (w : sources → ℂ) (μ : E → ℂ)
    (x : rows → ℝ) (z : sources → ℝ) (t : ℝ) : ℂ :=
  ∑ e, μ e * selectedBilinear rows sources
    (maskedRowVector mask (fun r => a r * FourierBridge.logPhase t (-Real.log (x r))) e)
    (maskedRowVector mask (fun r => c r * FourierBridge.logPhase t (-Real.log (x r))) e)
    (fun I => w I * FourierBridge.logPhase t (Real.log (z I)))

private theorem maskedRowVector_mul {E T : Type*}
    (mask : E → T → Prop) [∀ e r, Decidable (mask e r)]
    (a p : T → ℂ) (e : E) (r : T) :
    maskedRowVector mask (fun r => a r * p r) e r = maskedRowVector mask a e r * p r := by
  unfold maskedRowVector
  split_ifs <;> simp

private theorem two_sum_product {T U : Type*} [Fintype T] [Fintype U]
    (d : ℂ) (l : T → ℂ) (r : U → ℂ) :
    d * ((∑ i, l i) * (∑ j, r j)) = ∑ i, ∑ j, d * l i * r j := by
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem radialQuad_phase_sum {E : Type*} [Fintype E]
    (rows : Finset O) (sources : Finset (Ideal O))
    (mask : E → rows → Prop) [∀ e r, Decidable (mask e r)]
    (a c : rows → ℂ) (w : sources → ℂ) (μ : E → ℂ)
    (x : rows → ℝ) (z : sources → ℝ) (t : ℝ) :
    (∑ u : E × sources × rows × rows,
      radialQuadCoefficient rows sources mask a c w μ u *
        radialLogPhase t (x u.2.2.1) (x u.2.2.2) (z u.2.1)) =
      radialSeparatedBilinear rows sources mask a c w μ x z t := by
  unfold radialQuadCoefficient radialSeparatedBilinear selectedBilinear
  simp_rw [maskedRowVector_mul]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  let l : rows → ℂ := fun r => maskedRowVector mask a e r *
    FourierBridge.logPhase t (-Real.log (x r)) * star (selectedMatrix rows sources I r)
  let rr : rows → ℂ := fun s => maskedRowVector mask c e s *
    FourierBridge.logPhase t (-Real.log (x s)) * selectedMatrix rows sources I s
  calc
    _ = ∑ r : rows, ∑ s : rows,
        (μ e * (w I * FourierBridge.logPhase t (Real.log (z I)))) * l r * rr s := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      dsimp [l, rr, radialLogPhase]
      ring
    _ = (μ e * (w I * FourierBridge.logPhase t (Real.log (z I)))) *
        ((∑ r : rows, l r) * (∑ s : rows, rr s)) :=
      (two_sum_product _ l rr).symm
    _ = _ := by dsimp [l, rr]; ring

theorem radialMaskedQuad_eq_integral {E : Type*} [Fintype E]
    (rows : Finset O) (sources : Finset (Ideal O))
    (mask : E → rows → Prop) [∀ e r, Decidable (mask e r)]
    (a c : rows → ℂ) (w : sources → ℂ) (μ : E → ℂ)
    (x : rows → ℝ) (z : sources → ℝ) (W b : 𝓢(ℝ, ℂ)) (R : ℝ)
    (hx : ∀ r, x r ∈ Set.Icc (1 : ℝ) 2)
    (hz : ∀ I, z I ∈ Set.Icc (1 : ℝ) 2)
    (hi : Integrable (fun t : ℝ => ‖b t‖) volume)
    (hsep : ∀ x y z : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
      y ∈ Set.Icc (1 : ℝ) 2 → z ∈ Set.Icc (1 : ℝ) 2 →
      paperRadialFourier W (R * z / (x * y)) =
        ∫ t : ℝ, radialLogPhase t x y z * b t) :
    radialMaskedQuad rows sources mask a c w μ x z W R =
      ∫ t : ℝ, b t * radialSeparatedBilinear rows sources mask a c w μ x z t := by
  unfold radialMaskedQuad
  rw [finite_radial_integral W b R
    (radialQuadCoefficient rows sources mask a c w μ)
    (fun u => x u.2.2.1) (fun u => x u.2.2.2) (fun u => z u.2.1)
    (fun u => hx u.2.2.1) (fun u => hx u.2.2.2) (fun u => hz u.2.1) hi hsep]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [radialQuad_phase_sum]

/-- Uniform dyadic radial quadform estimate. The constant depends only on the
Schwartz profile and the requested decay order, before all finite row/source
data. The displayed left side contains the actual radial Fourier kernel. -/
theorem radial_idealDivisor_bilinear_bound (W : 𝓢(ℝ, ℂ)) (decay : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ (rows : Finset O) (sources labels : Finset (Ideal O))
        (a c : rows → ℂ) (w : sources → ℂ) (μ : labels → ℂ)
        (x : rows → ℝ) (z : sources → ℝ)
        (Bheight ε : ℝ) (_hB : 0 ≤ Bheight) (hε : 0 < ε)
        (_hnonzero : ∀ r : rows, r.val ≠ 0)
        (_hnorm : ∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ≤ Bheight)
        (_hw : ∀ I, ‖w I‖ ≤ 1) (_hμ : ∀ e, ‖μ e‖ ≤ 1)
        (_hx : ∀ r, x r ∈ Set.Icc (1 : ℝ) 2)
        (_hz : ∀ I, z I ∈ Set.Icc (1 : ℝ) 2),
      ‖∑ u : labels × sources × rows × rows,
        radialQuadCoefficient rows sources
          (idealDivisorMask labels (fun r : rows => Ideal.span {r.val})) a c w μ u *
          paperRadialFourier W (R * z u.2.1 / (x u.2.2.1 * x u.2.2.2))‖ ≤
        (C / (1 + R)^decay) * selectedNorm rows sources *
          (idealDivisorConstant ε hε * Bheight^ε) *
          Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2) := by
  obtain ⟨C, hC, hsep⟩ := radial_pair_log_separation W decay
  refine ⟨C, hC, ?_⟩
  intro R hR rows sources labels a c w μ x z Bheight ε hB hε hnonzero hnorm hw hμ hx hz
  obtain ⟨b, hb, hi, hL1, _⟩ := hsep R hR
  let mask : labels → rows → Prop :=
    idealDivisorMask labels (fun r : rows => Ideal.span {r.val})
  let Dcost : ℝ := selectedNorm rows sources *
    (idealDivisorConstant ε hε * Bheight^ε) *
    Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2)
  have hD : 0 ≤ Dcost := by
    have hcost : 0 ≤ idealDivisorConstant ε hε * Bheight^ε :=
      mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg hB ε)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (selectedNorm_nonneg rows sources) hcost) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hpoint (t : ℝ) :
      ‖radialSeparatedBilinear rows sources mask a c w μ x z t‖ ≤ Dcost := by
    have ht := selectedBilinear_naturalRowDivisors_le rows sources labels
      (fun r => a r * FourierBridge.logPhase t (-Real.log (x r)))
      (fun r => c r * FourierBridge.logPhase t (-Real.log (x r)))
      (fun I => w I * FourierBridge.logPhase t (Real.log (z I))) μ
      Bheight ε hB hε hnonzero hnorm
      (fun I => by simpa only [norm_mul, FourierBridge.logPhase_norm, mul_one] using hw I) hμ
    simpa only [radialSeparatedBilinear, mask, Dcost, norm_mul,
      FourierBridge.logPhase_norm, mul_one] using ht
  have hp : 0 < (1 + R)^decay := by positivity
  have hmass : (∫ t : ℝ, ‖b t‖) ≤ C / (1 + R)^decay := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  change ‖radialMaskedQuad rows sources mask a c w μ x z W R‖ ≤ _
  rw [radialMaskedQuad_eq_integral rows sources mask a c w μ x z W b R hx hz hi hb]
  calc
    _ ≤ ∫ t : ℝ, Dcost * ‖b t‖ := by
      apply norm_integral_le_of_norm_le (hi.const_mul Dcost)
      exact Filter.Eventually.of_forall fun t => by
        change ‖b t * radialSeparatedBilinear rows sources mask a c w μ x z t‖ ≤
          Dcost * ‖b t‖
        rw [norm_mul]
        nlinarith [hpoint t, norm_nonneg (b t)]
    _ = Dcost * (∫ t : ℝ, ‖b t‖) := integral_const_mul _ _
    _ ≤ Dcost * (C / (1 + R)^decay) := mul_le_mul_of_nonneg_left hmass hD
    _ = _ := by dsimp [Dcost]; ring

end

end Qrh.JointDetector
