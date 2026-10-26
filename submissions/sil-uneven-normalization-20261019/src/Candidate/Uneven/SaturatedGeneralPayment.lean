/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.SaturatedGain

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Saturated
open PR63Adaptation

theorem channel_payment_general {d gamma R S F live freq base fee : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 3/4) (hg : 0 ≤ gamma)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hF : 2*S ≤ F)
    (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : S ≤ R+live) (hfrequency : F ≤ 2*R+freq)
    (hremoved : fee ≤ base+gamma*S)
    (hfaces : ∀i,fee ≤ base+slope d i*S+offset d i*F) :
    fee ≤ base+gamma*R+physicalGain d live freq := by
  have hgain : fee-base ≤ physicalGain d S F :=
    fourGain_lower (by intro i;linarith only [hfaces i])
  have hm : fee-base ≤ min (gamma*S) (physicalGain d S F) :=
    le_min (by linarith only [hremoved]) hgain
  have hh := four_gain_width_transport (coefficient_bounds hd0 hd).1
    (coefficient_bounds hd0 hd).2.1 hg hR hlive hfreq hS hF hsupply hfrequency
  have hp := hm.trans hh
  change fee-base ≤ gamma*R+physicalGain d live freq at hp
  linarith only [hp]

theorem retained_high_payment_general {d gamma r1 r2 S F live freq base fee error high : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 3/4) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ d)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hS : 0 ≤ S) (hF : 2*S ≤ F)
    (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : S ≤ r1+r2+live) (hfrequency : F ≤ 2*(r1+r2)+freq)
    (hremoved : fee ≤ base+gamma*S)
    (hfaces : ∀i,fee ≤ base+slope d i*S+offset d i*F)
    (hhigh : high ≤ error-base-gamma*r1-d*r2) :
    high-physicalGain d live freq ≤ error-fee := by
  have hp := channel_payment_general hd0 hd hg0 (add_nonneg hr1 hr2) hS hF hlive hfreq
    hsupply hfrequency hremoved hfaces
  have hr := mul_le_mul_of_nonneg_right hg1 hr2
  nlinarith only [hp,hhigh,hr]

end Sil.Uneven.Saturated
