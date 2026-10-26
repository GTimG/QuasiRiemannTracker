/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual LOW capacity guard from checked node geometry and fixed losses. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103StepScalar.Geometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.CommonCapacity
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalLowGuard
noncomputable section
open Filter Record1252270103Finite Record1252270103StepScalar QRH.Record1252270103Graph
open OAI OAI.SevenEighths QRH.Record1252270103Low
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice

/-- Chosen from the node before any slot cardinality or moving width. -/
def step (n : Source) : ℝ := (n.allowance:ℝ)/(16*((n.L:ℝ)+1))

theorem step_positive (n : Source) (he : 0<(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ)) :
    0<step n := div_pos he (by positivity)

theorem step_budget (n : Source) (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ))
    (width frequency reserve rho plainRound : ℝ)
    (hw : width≤step n) (hf : frequency≤step n) (hr : reserve≤step n)
    (hρ : rho≤step n) (hp : plainRound≤step n) :
    (n.L:ℝ)*width+frequency+reserve+rho+2*plainRound≤(n.allowance:ℝ) := by
  have hlw := mul_le_mul_of_nonneg_left hw hL
  have hb : ((n.L:ℝ)+5)*step n≤(n.allowance:ℝ) := by
    rw [step,←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<16*((n.L:ℝ)+1))).mpr
    have hh := mul_nonneg he hL
    nlinarith only [he,hh]
  nlinarith only [hlw,hf,hr,hρ,hp,hb]

/-- The actual geometric bounds may include fixed favorable modulus factors.
Only the displayed lower bound on F and upper bound on t are used. -/
theorem guard_slack_of_geometry (K : ℚ) (n low : Source) (b : ℝ)
    (hg : RealGeometry K n low b) (hB0 : 0≤(low.B:ℝ)) (hB1 : (low.B:ℝ)≤1)
    (t F slots width frequency reserve rho plainRound logarithmic : ℝ)
    (hfrequency : 0≤frequency) (hreserve : 0≤reserve) (hrho : 0≤rho)
    (ht : t≤sourceTReal n b+(n.L:ℝ)*width)
    (hF : sourceFReal n low b-frequency-reserve≤F) (hslots : slots≤b)
    (hlog : logarithmic≤(n.allowance:ℝ))
    (hsmall : (n.L:ℝ)*width+frequency+reserve+rho+2*plainRound≤(n.allowance:ℝ)) :
    logarithmic+2*plainRound+(low.B:ℝ)*rho+2*(n.allowance:ℝ) ≤
      (low.B:ℝ)*F-t-slots := by
  have hbase := hg.parent_budget_room
  have hF' := mul_le_mul_of_nonneg_left hF hB0
  have hfreq := mul_le_mul_of_nonneg_right hB1 hfrequency
  have hres := mul_le_mul_of_nonneg_right hB1 hreserve
  have hr := mul_le_mul_of_nonneg_right hB1 hrho
  nlinarith only [hbase,hF',hfreq,hres,hr,ht,hslots,hlog,hsmall]

/-- Only the threshold depends on N and the fixed support endpoints. -/
theorem eventually_logarithmic_loss (N : ℕ) (upper plainUpper ε : ℝ)
    (hupper : 1≤upper) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      0≤3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper) ∧
      3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)≤ε := by
  filter_upwards [eventual_common_support_loss (3*N) plainUpper plainUpper upper ε hε]
    with Z hz
  have hid : commonSupportLoss (3*N) Z plainUpper plainUpper upper =
      3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper) := by
    rw [commonSupportLoss,Real.logb_mul
      (zero_lt_one.trans_le (le_max_left 1 plainUpper)).ne'
      (zero_lt_one.trans_le (le_max_left 1 plainUpper)).ne',max_eq_right hupper]
    push_cast
    ring
  exact ⟨hz.1,hid ▸ hz.2.1,hid ▸ hz.2.2⟩

/-- The exact sector-frequency loss, including its logarithmic constant, is
absorbed together with the three-allocation annular and plain clipping losses. -/
theorem eventually_fixed_losses (n : Source) (N : ℕ) (upper plainUpper ξ : ℝ)
    (he : 0<(n.allowance:ℝ)) (hupper : 1≤upper) (hξ : 0<ξ) (hξstep : ξ≤step n) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)≤(n.allowance:ℝ)) ∧
      0≤frequencyLoss Z 32 ξ ∧ frequencyLoss Z 32 ξ≤step n := by
  filter_upwards [eventually_logarithmic_loss N upper plainUpper (n.allowance:ℝ) hupper he,
    eventually_frequency_loss 32 ξ (by norm_num) hξ] with Z hz hf
  exact ⟨hz.1,hz.2.2,hf.2.1,hf.2.2.le.trans hξstep⟩

/-- This threshold is uniform over every width with checked node geometry and
every later actual allocation, profile, row and height. -/
theorem eventually_geometry_guard (n low : Source) (N : ℕ) (upper plainUpper ξ : ℝ)
    (he : 0<(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ))
    (hB0 : 0≤(low.B:ℝ)) (hB1 : (low.B:ℝ)≤1)
    (hupper : 1≤upper) (hξ : 0<ξ) (hξstep : ξ≤step n) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(K : ℚ)(b : ℝ),RealGeometry K n low b →
      ∀(t F slots width reserve rho plainRound : ℝ),
      0≤reserve → 0≤rho → width≤step n → reserve≤step n → rho≤step n → plainRound≤step n →
      t≤sourceTReal n b+(n.L:ℝ)*width →
      sourceFReal n low b-frequencyLoss Z 32 ξ-reserve≤F → slots≤b →
      (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound)+
        (low.B:ℝ)*rho+2*(n.allowance:ℝ)≤(low.B:ℝ)*F-t-slots := by
  filter_upwards [eventually_fixed_losses n N upper plainUpper ξ he hupper hξ hξstep] with Z hz
  refine ⟨hz.1,?_⟩
  intro K b hg t F slots width reserve rho plainRound hreserve hrho hw hr hρ hp ht hF hslots
  exact guard_slack_of_geometry K n low b hg hB0 hB1 t F slots width
    (frequencyLoss Z 32 ξ) reserve rho plainRound
    (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper))
    hz.2.2.1 hreserve hrho ht hF hslots hz.2.1
    (step_budget n he.le hL width _ reserve rho plainRound hw hz.2.2.2 hr hρ hp)

end
end QRH.Record1252270103Source.PhysicalLowGuard
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.step_positive
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.step_budget
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.guard_slack_of_geometry
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.eventually_logarithmic_loss
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.eventually_fixed_losses
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.eventually_geometry_guard
