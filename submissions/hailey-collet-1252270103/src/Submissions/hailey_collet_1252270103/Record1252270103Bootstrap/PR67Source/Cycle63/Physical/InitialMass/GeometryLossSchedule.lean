import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.LocalReserves
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainRemainder
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.HighParameters
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Filter CenteredMomentSectorLocalization

section Ledger
variable [Cycle63.AffineLedger]

/-- The common loss unit precedes the slot dictionary and all density degrees. -/
def geometryLossUnit (Mmin εaffine : ℝ) : ℝ :=
  min (εaffine/128) (min ((Cycle63.AffineLedger.lowReserve)*Mmin/128) (min (Mmin/128) (1/128)))

theorem geometry_loss_unit_pos (Mmin εaffine : ℝ) (hM : 0<Mmin) (hε : 0<εaffine) :
    0<geometryLossUnit Mmin εaffine := by
  unfold geometryLossUnit
  exact lt_min (by positivity) (lt_min (div_pos (mul_pos Cycle63.AffineLedger.lowReserve_pos hM)
    (by norm_num)) (lt_min (by positivity) (by norm_num)))

/-- Sixty-four units fit inside half the smallest physical reserve. -/
theorem geometry_loss_unit_reserve (Mmin εaffine M : ℝ) (hM : Mmin≤M) :
    128*geometryLossUnit Mmin εaffine≤εaffine ∧
      64*geometryLossUnit Mmin εaffine≤M*((Cycle63.AffineLedger.lowReserve/2)) := by
  have h₁ := min_le_left (εaffine/128) (min ((Cycle63.AffineLedger.lowReserve)*Mmin/128) (min (Mmin/128) (1/128)))
  have h₂ := (min_le_right (εaffine/128) _).trans
    (min_le_left ((Cycle63.AffineLedger.lowReserve)*Mmin/128) (min (Mmin/128) (1/128)))
  change geometryLossUnit Mmin εaffine≤_ at h₁ h₂
  have hm := mul_le_mul_of_nonneg_left hM Cycle63.AffineLedger.lowReserve_pos.le
  constructor <;> linarith

/-- Every larger branch reserve can use the same loss unit. The actual
branch estimates must supply their own total loss bound. -/
theorem geometry_paid_loss (Mmin εaffine M reserve loss : ℝ)
    (hMmin : 0<Mmin)(hM : Mmin≤M)(hr : (Cycle63.AffineLedger.lowReserve:ℝ)≤ reserve)
    (hloss : loss≤64*geometryLossUnit Mmin εaffine) :
    -M*reserve+loss≤-M*((Cycle63.AffineLedger.lowReserve/2)) := by
  have hb := (geometry_loss_unit_reserve Mmin εaffine M hM).2
  have hMr := mul_le_mul_of_nonneg_left hr (hMmin.trans_le hM).le
  linarith

theorem geometry_high_reserve_ge_low :
    (Cycle63.AffineLedger.lowReserve:ℝ)≤Cycle63.AffineLedger.lowReserve := by norm_num

end Ledger

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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
