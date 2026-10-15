/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Arithmetic.LocalReserves
import Candidate.Cycle62.Physical.InitialMass.GeometryMainRemainder
import Candidate.Cycle62.Moment.HighParameters

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open Filter CenteredMomentSectorLocalization

/-- The common loss unit precedes the slot dictionary and all density degrees. -/
def geometryLossUnit (Mmin εaffine : ℝ) : ℝ :=
  min (εaffine/128) (min ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))

theorem geometry_loss_unit_pos (Mmin εaffine : ℝ) (hM : 0<Mmin) (hε : 0<εaffine) :
    0<geometryLossUnit Mmin εaffine := by unfold geometryLossUnit;positivity

/-- Sixty-four units fit inside half the smallest physical reserve. -/
theorem geometry_loss_unit_reserve (Mmin εaffine M : ℝ) (hM : Mmin≤M) :
    128*geometryLossUnit Mmin εaffine≤εaffine ∧
      64*geometryLossUnit Mmin εaffine≤M*(7/60000000) := by
  have h₁ := min_le_left (εaffine/128) (min ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))
  have h₂ := (min_le_right (εaffine/128) _).trans
    (min_le_left ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))
  change geometryLossUnit Mmin εaffine≤_ at h₁ h₂
  constructor <;> linarith

/-- Every larger branch reserve can use the same loss unit. The actual
branch estimates must supply their own total loss bound. -/
theorem geometry_paid_loss (Mmin εaffine M reserve loss : ℝ)
    (hMmin : 0<Mmin)(hM : Mmin≤M)(hr : (7/30000000:ℝ)≤reserve)
    (hloss : loss≤64*geometryLossUnit Mmin εaffine) :
    -M*reserve+loss≤-M*(7/60000000) := by
  have hb := (geometry_loss_unit_reserve Mmin εaffine M hM).2
  have hMr := mul_le_mul_of_nonneg_left hr (hMmin.trans_le hM).le
  linarith

theorem geometry_high_reserve_ge_low :
    (7/30000000:ℝ)≤720486667/30493190000000 := by norm_num

/-- The fixed localization constant is absorbed before sources move. -/
theorem eventual_geometry_small_frequency (μ : ℝ)(hμ : 0<μ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (μ/64)+μ/8 ∧
      frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128 := by
  filter_upwards [(tendsto_rpow_atTop (by positivity : 0<μ/8)).eventually
    (eventually_ge_atTop (128:ℝ)),eventually_gt_atTop (1:ℝ)] with Z hz hZ
  have hlog : Real.logb Z 128≤μ/8 :=
    (Real.logb_le_iff_le_rpow hZ (by norm_num : (0:ℝ)<128)).mpr hz
  have hfreq := frequencyLoss_nonneg Z 32 (μ/64) hZ (by norm_num) (by positivity)
  refine ⟨hZ,by positivity,?_⟩
  dsimp only [frequencyLoss]
  norm_num only [show (4:ℝ)*32=128 by norm_num]
  linarith

/-- Width and padding choices are independent of the slot count. -/
theorem geometry_width_padding_budget (μ Mmax M omega : ℝ)
    (hμ : 0<μ)(hmax : 0≤Mmax)(hM : M≤Mmax)(hω : omega≤33*μ/128) :
    μ/(4*(Mmax+1))*M+μ/128≤33*μ/128 ∧
      omega+μ/(4*(Mmax+1))*M≤3*μ/4 := by
  have hp : 0<4*(Mmax+1) := by positivity
  have he := div_mul_cancel₀ μ (ne_of_gt hp)
  have hratio : 0<μ/(4*(Mmax+1)) := by positivity
  have hm := mul_le_mul_of_nonneg_left hM hratio.le
  have hb : μ/(4*(Mmax+1))*M≤μ/4 := by nlinarith
  constructor <;> linarith

/-- These losses are selected after the fixed slot count is known. Their
products with the count and the source caps still have fixed small budgets. -/
theorem geometry_dictionary_loss_budgets (μ d B : ℝ)(N : ℕ)
    (hμ : 0<μ)(hd : 0≤d)(hB : 0≤B) :
    let εplain := μ/(64*(d+1))
    let εslot := μ/(64*(d+1)*(N+1))
    let εerror := μ/(8*(N+1))
    let εmass := μ/(8*(B+1))
    0<εplain ∧ 0<εslot ∧ 0<εerror ∧ 0<εmass ∧
      2*d*εplain≤μ/32 ∧ 2*d*N*εslot≤μ/32 ∧
      (N:ℝ)*εerror≤μ/8 ∧ B*εmass≤μ/8 ∧
      μ/16+2*d*εplain+2*d*N*εslot≤μ/4 := by
  intro εplain εslot εerror εmass
  have hp : 0<εplain := by dsimp [εplain];positivity
  have hs : 0<εslot := by dsimp [εslot];positivity
  have he : 0<εerror := by dsimp [εerror];positivity
  have hm : 0<εmass := by dsimp [εmass];positivity
  have ep : εplain*(64*(d+1))=μ := div_mul_cancel₀ _ (by positivity)
  have es : εslot*(64*(d+1)*(N+1))=μ := div_mul_cancel₀ _ (by positivity)
  have ee : εerror*(8*(N+1))=μ := div_mul_cancel₀ _ (by positivity)
  have em : εmass*(8*(B+1))=μ := div_mul_cancel₀ _ (by positivity)
  have hN : (0:ℝ)≤N := Nat.cast_nonneg _
  have hp' : 2*d*εplain≤μ/32 := by nlinarith
  have hs' : 2*d*N*εslot≤μ/32 := by
    nlinarith [mul_nonneg hd hs.le,mul_nonneg hN hs.le]
  refine ⟨hp,hs,he,hm,hp',hs',?_,?_,?_⟩ <;> nlinarith

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_loss_unit_pos
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_loss_unit_reserve
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_paid_loss
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_high_reserve_ge_low
#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_geometry_small_frequency
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_width_padding_budget
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_dictionary_loss_budgets
