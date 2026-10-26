import Candidate.Uneven.BootstrapCoefficients
import Candidate.Uneven.MainAChannels
import Candidate.Uneven.MainCChannels
import Candidate.Uneven.MainA2Channels
import Candidate.Uneven.MainC2Channels
import Candidate.Uneven.SaturatedGeneralPayment

/- Original module: Candidate.Uneven.BootstrapGeneralPayment. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem retained_high_payment_general {d gamma r1 r2 S F live freq base fee error high : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 33/50) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ d)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hS : 0 ≤ S) (hF : 2*S ≤ F)
    (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : S ≤ r1+r2+live) (hfrequency : F ≤ 2*(r1+r2)+freq)
    (hremoved : fee ≤ base+gamma*S)
    (hfaces : ∀i,fee ≤ base+slope d i*S+offset d i*F)
    (hhigh : high ≤ error-base-gamma*r1-d*r2) :
    high-physicalGain d live freq ≤ error-fee := by
  have hc := coefficient_nonneg hd0 hd
  have hp := FiniteGain.channel_payment hc.1 hc.2 hg0 (add_nonneg hr1 hr2)
    hlive hfreq hS hF hsupply hfrequency hremoved hfaces
  have hr := mul_le_mul_of_nonneg_right hg1 hr2
  change fee ≤ base+gamma*(r1+r2)+physicalGain d live freq at hp
  nlinarith only [hp,hhigh,hr]

end Sil.Uneven.Bootstrap
end

/- Original module: Candidate.Uneven.MainChannelPayment. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.MainSource

theorem interpolate_width {f : ℝ → ℝ} {b : ℝ}
    (hb : b∈Set.Icc widthLo widthHi)
    (he : (widthHi-widthLo)*(f b-highReserve)=
      (widthHi-b)*(f widthLo-highReserve)+(b-widthLo)*(f widthHi-highReserve))
    (hlo : highReserve ≤ f widthLo) (hhi : highReserve ≤ f widthHi) :
    highReserve ≤ f b := by
  have h0 := mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hlo)
  have h1 := mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hhi)
  norm_num [widthHi,widthLo] at he h0 h1
  nlinarith only [h0,h1,he]

theorem bootstrap_channel_reserves (P : Plane) {b d : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd0 : P.q ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase P b d+gamma d*supplied b ∧
      ∀i : Fin 7, highReserve ≤ bootstrapChannel P b d i := by
  constructor
  · apply interpolate_width (f:=fun b=>highBase P b d+gamma d*supplied b) hb
    · simp only [highBase,frequency,total,amp,gap,supplied]
      ring
    · cases P
      · exact A_bootstrap_lo_0 hd0 hd1
      · exact C_bootstrap_lo_0 hd0 hd1
      · exact A2_bootstrap_lo_0 hd0 hd1
      · exact C2_bootstrap_lo_0 hd0 hd1
    · cases P
      · exact A_bootstrap_hi_0 hd0 hd1
      · exact C_bootstrap_hi_0 hd0 hd1
      · exact A2_bootstrap_hi_0 hd0 hd1
      · exact C2_bootstrap_hi_0 hd0 hd1
  · intro i
    apply interpolate_width (f:=fun b=>bootstrapChannel P b d i) hb
    · simp only [bootstrapChannel,highBase,frequency,total,amp,gap,supplied]
      ring
    · cases P
      · fin_cases i
        · exact A_bootstrap_lo_1 hd0 hd1
        · exact A_bootstrap_lo_2 hd0 hd1
        · exact A_bootstrap_lo_3 hd0 hd1
        · exact A_bootstrap_lo_4 hd0 hd1
        · exact A_bootstrap_lo_5 hd0 hd1
        · exact A_bootstrap_lo_6 hd0 hd1
        · exact A_bootstrap_lo_7 hd0 hd1
      · fin_cases i
        · exact C_bootstrap_lo_1 hd0 hd1
        · exact C_bootstrap_lo_2 hd0 hd1
        · exact C_bootstrap_lo_3 hd0 hd1
        · exact C_bootstrap_lo_4 hd0 hd1
        · exact C_bootstrap_lo_5 hd0 hd1
        · exact C_bootstrap_lo_6 hd0 hd1
        · exact C_bootstrap_lo_7 hd0 hd1
      · fin_cases i
        · exact A2_bootstrap_lo_1 hd0 hd1
        · exact A2_bootstrap_lo_2 hd0 hd1
        · exact A2_bootstrap_lo_3 hd0 hd1
        · exact A2_bootstrap_lo_4 hd0 hd1
        · exact A2_bootstrap_lo_5 hd0 hd1
        · exact A2_bootstrap_lo_6 hd0 hd1
        · exact A2_bootstrap_lo_7 hd0 hd1
      · fin_cases i
        · exact C2_bootstrap_lo_1 hd0 hd1
        · exact C2_bootstrap_lo_2 hd0 hd1
        · exact C2_bootstrap_lo_3 hd0 hd1
        · exact C2_bootstrap_lo_4 hd0 hd1
        · exact C2_bootstrap_lo_5 hd0 hd1
        · exact C2_bootstrap_lo_6 hd0 hd1
        · exact C2_bootstrap_lo_7 hd0 hd1
    · cases P
      · fin_cases i
        · exact A_bootstrap_hi_1 hd0 hd1
        · exact A_bootstrap_hi_2 hd0 hd1
        · exact A_bootstrap_hi_3 hd0 hd1
        · exact A_bootstrap_hi_4 hd0 hd1
        · exact A_bootstrap_hi_5 hd0 hd1
        · exact A_bootstrap_hi_6 hd0 hd1
        · exact A_bootstrap_hi_7 hd0 hd1
      · fin_cases i
        · exact C_bootstrap_hi_1 hd0 hd1
        · exact C_bootstrap_hi_2 hd0 hd1
        · exact C_bootstrap_hi_3 hd0 hd1
        · exact C_bootstrap_hi_4 hd0 hd1
        · exact C_bootstrap_hi_5 hd0 hd1
        · exact C_bootstrap_hi_6 hd0 hd1
        · exact C_bootstrap_hi_7 hd0 hd1
      · fin_cases i
        · exact A2_bootstrap_hi_1 hd0 hd1
        · exact A2_bootstrap_hi_2 hd0 hd1
        · exact A2_bootstrap_hi_3 hd0 hd1
        · exact A2_bootstrap_hi_4 hd0 hd1
        · exact A2_bootstrap_hi_5 hd0 hd1
        · exact A2_bootstrap_hi_6 hd0 hd1
        · exact A2_bootstrap_hi_7 hd0 hd1
      · fin_cases i
        · exact C2_bootstrap_hi_1 hd0 hd1
        · exact C2_bootstrap_hi_2 hd0 hd1
        · exact C2_bootstrap_hi_3 hd0 hd1
        · exact C2_bootstrap_hi_4 hd0 hd1
        · exact C2_bootstrap_hi_5 hd0 hd1
        · exact C2_bootstrap_hi_6 hd0 hd1
        · exact C2_bootstrap_hi_7 hd0 hd1

theorem saturated_channel_reserves (P : Plane) {b d : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase P b d+gamma d*supplied b ∧
      ∀i : Fin 4, highReserve ≤ saturatedChannel P b d i := by
  constructor
  · apply interpolate_width (f:=fun b=>highBase P b d+gamma d*supplied b) hb
    · simp only [highBase,frequency,total,amp,gap,supplied]
      ring
    · cases P
      · exact A_saturated_lo_0 hd0 hd1
      · exact C_saturated_lo_0 hd0 hd1
      · exact A2_saturated_lo_0 hd0 hd1
      · exact C2_saturated_lo_0 hd0 hd1
    · cases P
      · exact A_saturated_hi_0 hd0 hd1
      · exact C_saturated_hi_0 hd0 hd1
      · exact A2_saturated_hi_0 hd0 hd1
      · exact C2_saturated_hi_0 hd0 hd1
  · intro i
    apply interpolate_width (f:=fun b=>saturatedChannel P b d i) hb
    · simp only [saturatedChannel,highBase,frequency,total,amp,gap,supplied]
      ring
    · cases P
      · fin_cases i
        · exact A_saturated_lo_1 hd0 hd1
        · exact A_saturated_lo_2 hd0 hd1
        · exact A_saturated_lo_3 hd0 hd1
        · exact A_saturated_lo_4 hd0 hd1
      · fin_cases i
        · exact C_saturated_lo_1 hd0 hd1
        · exact C_saturated_lo_2 hd0 hd1
        · exact C_saturated_lo_3 hd0 hd1
        · exact C_saturated_lo_4 hd0 hd1
      · fin_cases i
        · exact A2_saturated_lo_1 hd0 hd1
        · exact A2_saturated_lo_2 hd0 hd1
        · exact A2_saturated_lo_3 hd0 hd1
        · exact A2_saturated_lo_4 hd0 hd1
      · fin_cases i
        · exact C2_saturated_lo_1 hd0 hd1
        · exact C2_saturated_lo_2 hd0 hd1
        · exact C2_saturated_lo_3 hd0 hd1
        · exact C2_saturated_lo_4 hd0 hd1
    · cases P
      · fin_cases i
        · exact A_saturated_hi_1 hd0 hd1
        · exact A_saturated_hi_2 hd0 hd1
        · exact A_saturated_hi_3 hd0 hd1
        · exact A_saturated_hi_4 hd0 hd1
      · fin_cases i
        · exact C_saturated_hi_1 hd0 hd1
        · exact C_saturated_hi_2 hd0 hd1
        · exact C_saturated_hi_3 hd0 hd1
        · exact C_saturated_hi_4 hd0 hd1
      · fin_cases i
        · exact A2_saturated_hi_1 hd0 hd1
        · exact A2_saturated_hi_2 hd0 hd1
        · exact A2_saturated_hi_3 hd0 hd1
        · exact A2_saturated_hi_4 hd0 hd1
      · fin_cases i
        · exact C2_saturated_hi_1 hd0 hd1
        · exact C2_saturated_hi_2 hd0 hd1
        · exact C2_saturated_hi_3 hd0 hd1
        · exact C2_saturated_hi_4 hd0 hd1

theorem bootstrap_retained_payment (P : Plane) {b d c c2 live freq error high : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd : P.q ≤ d) (hu : d ≤ (33/50:ℝ))
    (hc : 0 ≤ c) (hc2 : 0 ≤ c2) (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : supplied b ≤ c+c2+live) (hfrequency : frequency P b ≤ 2*(c+c2)+freq)
    (hhigh : high ≤ error-highBase P b d-gamma d*c-d*c2) :
    high-Bootstrap.physicalGain d live freq ≤ error-highReserve := by
  have hd0 : 31/50 ≤ d := by
    exact (parameter_gates P).1.trans hd
  have hg0 : 0 ≤ gamma d := by unfold gamma; linarith
  have hg1 : gamma d ≤ d := by unfold gamma; linarith
  obtain ⟨_,_,_,_,_,_,_,hS,_,hF,_⟩ := scheduling_guards P hb
  have hr := bootstrap_channel_reserves P hb hd hu
  exact Bootstrap.retained_high_payment_general hd0 hu hg0 hg1 hc hc2 hS.le hF.le
    hlive hfreq hsupply hfrequency hr.1 hr.2 hhigh

theorem saturated_retained_payment (P : Plane) {b d c c2 live freq error high : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd : (33/50:ℝ) ≤ d) (hu : d ≤ (3/4:ℝ))
    (hc : 0 ≤ c) (hc2 : 0 ≤ c2) (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : supplied b ≤ c+c2+live) (hfrequency : frequency P b ≤ 2*(c+c2)+freq)
    (hhigh : high ≤ error-highBase P b d-gamma d*c-d*c2) :
    high-Saturated.physicalGain d live freq ≤ error-highReserve := by
  have hd0 : 31/50 ≤ d := by
    linarith only [hd]
  have hg0 : 0 ≤ gamma d := by unfold gamma; linarith
  have hg1 : gamma d ≤ d := by unfold gamma; linarith
  obtain ⟨_,_,_,_,_,_,_,hS,_,hF,_⟩ := scheduling_guards P hb
  have hr := saturated_channel_reserves P hb hd hu
  exact Saturated.retained_high_payment_general hd0 hu hg0 hg1 hc hc2 hS.le hF.le
    hlive hfreq hsupply hfrequency hr.1 hr.2 hhigh

end Sil.Uneven.MainSource
end

/- Original module: Candidate.Uneven.MainRemovedPayment. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.MainSource

theorem removed_channel_reserve (P : Plane) {b d : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd : P.q ≤ d) (hu : d ≤ 3/4) :
    highReserve ≤ highBase P b d+gamma d*supplied b := by
  rcases le_total d (33/50) with h | h
  · exact (bootstrap_channel_reserves P hb hd h).1
  · exact (saturated_channel_reserves P hb h hu).1


end Sil.Uneven.MainSource
end
