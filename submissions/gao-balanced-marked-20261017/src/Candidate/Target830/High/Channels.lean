import Candidate.Target830.High.ChannelCertificatesA
import Candidate.Target830.High.ChannelCertificatesC
import Candidate.Target830.Marked.ParametersBridge

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open Target830

/-- Width interpolation is exact; the density-dependent caps stay inside
all seven affine width channels. -/
theorem channel_width_identity (P : SourcePlane) (b delta : ℝ) (i : Fin 7) :
    ((1/25:ℝ)-17/500)*(channel P b delta i-highFee)=
      ((1/25:ℝ)-b)*(channel P (17/500) delta i-highFee)+
      (b-17/500)*(channel P (1/25) delta i-highFee) := by
  fin_cases i <;>
    simp [channel,highBase,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied] <;> ring

theorem channel_endpoint (P : SourcePlane) (delta : ℝ)
    (hd : P.q≤delta) (hu : delta≤7/10) (i : Fin 7) :
    highFee≤channel P (17/500) delta i ∧ highFee≤channel P (1/25) delta i := by
  cases P
  · fin_cases i
    · exact ⟨channel_A_lo_0 delta hd hu,channel_A_hi_0 delta hd hu⟩
    · exact ⟨channel_A_lo_1 delta hd hu,channel_A_hi_1 delta hd hu⟩
    · exact ⟨channel_A_lo_2 delta hd hu,channel_A_hi_2 delta hd hu⟩
    · exact ⟨channel_A_lo_3 delta hd hu,channel_A_hi_3 delta hd hu⟩
    · exact ⟨channel_A_lo_4 delta hd hu,channel_A_hi_4 delta hd hu⟩
    · exact ⟨channel_A_lo_5 delta hd hu,channel_A_hi_5 delta hd hu⟩
    · exact ⟨channel_A_lo_6 delta hd hu,channel_A_hi_6 delta hd hu⟩
  · fin_cases i
    · exact ⟨channel_C_lo_0 delta hd hu,channel_C_hi_0 delta hd hu⟩
    · exact ⟨channel_C_lo_1 delta hd hu,channel_C_hi_1 delta hd hu⟩
    · exact ⟨channel_C_lo_2 delta hd hu,channel_C_hi_2 delta hd hu⟩
    · exact ⟨channel_C_lo_3 delta hd hu,channel_C_hi_3 delta hd hu⟩
    · exact ⟨channel_C_lo_4 delta hd hu,channel_C_hi_4 delta hd hu⟩
    · exact ⟨channel_C_lo_5 delta hd hu,channel_C_hi_5 delta hd hu⟩
    · exact ⟨channel_C_lo_6 delta hd hu,channel_C_hi_6 delta hd hu⟩

theorem all_channels (P : SourcePlane) (b delta : ℝ)
    (hb : 17/500≤b ∧ b≤1/25) (hd : P.q≤delta) (hu : delta≤7/10)
    (i : Fin 7) : highFee≤channel P b delta i := by
  have h:=channel_endpoint P delta hd hu i
  have h1:=mul_nonneg (by linarith : 0≤(1/25:ℝ)-b) (sub_nonneg.mpr h.1)
  have h2:=mul_nonneg (by linarith : 0≤b-(17/500:ℝ)) (sub_nonneg.mpr h.2)
  have hh:=channel_width_identity P b delta i
  nlinarith only [h1,h2,hh]

theorem common_gamma_le (delta : ℝ) : commonGamma delta≤delta := by
  have h:=le_max_left (3/19:ℝ) (4*rho delta-5/4)
  unfold commonGamma
  linarith

theorem channel_reserves (P : SourcePlane) (b delta : ℝ)
    (hb : 17/500≤b ∧ b≤1/25) (hd : P.q≤delta) (hu : delta≤7/10) :
    highFee≤highBase P b delta+commonGamma delta*P.supplied b ∧
    highFee≤highBase P b delta+phi delta*P.supplied b ∧
    highFee≤highBase P b delta+phi delta*(2*P.supplied b+capP delta*P.frequency b)/3 ∧
    highFee≤highBase P b delta+phi delta*(2*capI delta*P.frequency b+P.supplied b)/3 ∧
    highFee≤highBase P b delta+phi delta*(2*capI delta+capP delta)*P.frequency b/3 ∧
    highFee≤highBase P b delta+P.rootCutoff*(6*rho delta-1)*P.frequency b := by
  have h (i : Fin 7):=all_channels P b delta hb hd hu i
  constructor
  · by_cases hc : (3/19:ℝ)≤4*rho delta-5/4
    · have hid : delta-(4*rho delta-5/4)=delta-4*rho delta+5/4 := by ring
      simpa [channel,commonGamma,max_eq_right hc,hid] using h 1
    · simpa [channel,commonGamma,max_eq_left (le_of_not_ge hc)] using h 0
  · exact ⟨by simpa [channel] using h 2,by simpa [channel] using h 3,
      by simpa [channel] using h 4,by simpa [channel] using h 5,
      by simpa [channel] using h 6⟩

theorem gamma_root_slope (P : SourcePlane) (delta : ℝ)
    (hd : P.q≤delta) (hu : delta≤3/4) :
    2*(P.rootCutoff*(6*rho delta-1))≤commonGamma delta := by
  have h0 : 2*(P.rootCutoff*(6*rho delta-1))≤delta-3/19 := by
    cases P
    · simpa only [mul_assoc] using slope_A_0 delta hd hu
    · simpa only [mul_assoc] using slope_C_0 delta hd hu
  have h1 : 2*(P.rootCutoff*(6*rho delta-1))≤delta-4*rho delta+5/4 := by
    cases P
    · simpa only [mul_assoc] using slope_A_1 delta hd hu
    · simpa only [mul_assoc] using slope_C_1 delta hd hu
  by_cases hc : (3/19:ℝ)≤4*rho delta-5/4
  · have hid : delta-(4*rho delta-5/4)=delta-4*rho delta+5/4 := by ring
    simpa [commonGamma,max_eq_right hc,hid] using h1
  · simpa [commonGamma,max_eq_left (le_of_not_ge hc)] using h0

theorem unmarked_high_reserve (P : SourcePlane) (b delta : ℝ)
    (hb : 17/500≤b ∧ b≤1/25) (hd : 7/10≤delta) (hu : delta≤3/4) :
    highFee≤highBase P b delta := by
  have hl : highFee≤highBase P (17/500) delta := by
    cases P
    · exact unmarked_A_lo delta hd hu
    · exact unmarked_C_lo delta hd hu
  have hh : highFee≤highBase P (1/25) delta := by
    cases P
    · exact unmarked_A_hi delta hd hu
    · exact unmarked_C_hi delta hd hu
  have hid : ((1/25:ℝ)-17/500)*(highBase P b delta-highFee)=
      ((1/25:ℝ)-b)*(highBase P (17/500) delta-highFee)+
      (b-17/500)*(highBase P (1/25) delta-highFee) := by
    simp [highBase,SourcePlane.total,SourcePlane.amp,SourcePlane.gap]
    ring
  have h1:=mul_nonneg (by linarith : 0≤(1/25:ℝ)-b) (sub_nonneg.mpr hl)
  have h2:=mul_nonneg (by linarith : 0≤b-(17/500:ℝ)) (sub_nonneg.mpr hh)
  nlinarith only [hid,h1,h2]

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.all_channels
#print axioms OAI.SevenEighths.TargetHigh830.channel_reserves
#print axioms OAI.SevenEighths.TargetHigh830.gamma_root_slope
#print axioms OAI.SevenEighths.TargetHigh830.unmarked_high_reserve
