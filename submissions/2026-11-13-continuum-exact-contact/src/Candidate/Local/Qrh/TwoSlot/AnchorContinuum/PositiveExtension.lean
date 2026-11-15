/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Uniform cost of extending the positive-source conductor interval. The
admitted count envelope and both physical capacity branches are retained. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveCount

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Set
open Qrh.TwoSlot.AnchorZeroLoss
local instance : Affine.Return.ImprovedCountScheme exactLine := exactScheme

theorem envelopeAt_upper {K d p : ℝ} (hK : (7/10:ℝ) ≤ K)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    envelopeAt K d p ≤ 2 := by
  have he := Affine.Return.ImprovedCount.envelope_le_base (line := exactLine) K d p
  change envelopeAt K d p ≤ QRH.Record12518109Return.countingR K d p at he
  have hden := QRH.Record12518109Return.rowDen_pos hK
    (show 0 ≤ d ∧ d ≤ 5/6 by constructor <;> linarith [hd.1,hd.2]) hp
  have hc := QRH.Record12518109Return.countingCoefficient_pos hK hp
  have hmul := mul_nonneg hd.1 hc.le
  have hV : 0 ≤ (5/6:ℝ)-d := by linarith [hd.2]
  have hr : d*QRH.Record12518109Return.countingCoefficient K p*
      (5/6-d)/(2*QRH.Record12518109Return.rowDen K d p) ≤ (5/6-d)/2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hden)).mpr
    dsimp [QRH.Record12518109Return.rowDen]
    nlinarith [sq_nonneg ((5/6:ℝ)-d)]
  unfold QRH.Record12518109Return.countingR at he
  linarith [hd.1]

/-- Increasing conductor loses at most half its increase in capacity. -/
theorem target_capacity_extension {s t D : ℝ} (hs : 0 ≤ s)
    (hD : stationaryCutoff ≤ D) :
    targetCapacity s t stationaryCutoff-(D-stationaryCutoff)/2 ≤ targetCapacity s t D := by
  have hden : 0 < 2+10*s := by positivity
  have hm := min_le_left ((3/40:ℝ)*stationaryCutoff)
    ((2*targetY t-(1+s)*stationaryCutoff)/(2+10*s))
  have hn := min_le_right ((3/40:ℝ)*stationaryCutoff)
    ((2*targetY t-(1+s)*stationaryCutoff)/(2+10*s))
  have hn' := (le_div_iff₀ hden).mp hn
  have hsg := mul_nonneg hs (sub_nonneg.mpr hD)
  unfold targetCapacity
  apply le_min
  · linarith
  · apply (le_div_iff₀ hden).mpr
    nlinarith only [hn',hsg]

/-- All changes in the physical row along the extended conductor range cost
at most twice the conductor increase. No continuity of a selected branch is used. -/
theorem target_row_extension {s t K D d p : ℝ} (hs : 0 ≤ s)
    (hK : (7/10:ℝ) ≤ K) (hD : stationaryCutoff ≤ D)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    targetRow K t D (targetCapacity s t D) d p ≤
      targetRow K t stationaryCutoff (targetCapacity s t stationaryCutoff) d p+
        2*(D-stationaryCutoff) := by
  have hc := target_capacity_extension (t := t) hs hD
  have he := envelopeAt_upper hK hd hp
  have hdp : 0 ≤ d*p := mul_nonneg hd.1 hp.1
  have hdpmax : d*p ≤ (3/8:ℝ) := by
    have hh := mul_le_mul hd.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hh ⊢
    exact hh
  have hm := mul_nonneg hdp (sub_nonneg.mpr hc)
  have hn := mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr he)
  have ho := mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hdpmax)
  have hsplit :
      targetRow K t D (targetCapacity s t D) d p-
        targetRow K t stationaryCutoff (targetCapacity s t stationaryCutoff) d p =
      -(9/100:ℝ)*(D-stationaryCutoff)+
        (d*p/2)*(targetCapacity s t stationaryCutoff-targetCapacity s t D)+
        (3/4)*(D-stationaryCutoff)*envelopeAt K d p := by
    unfold targetRow targetRowWithFixedCount
    ring
  nlinarith only [hsplit,hm,hn,ho,sub_nonneg.mpr hD]

/-- Quantitative positive-source return on the extended conductor interval,
at the actual target count parameter. -/
theorem extended_target_rows {s t Δ D d p : ℝ} (hs : 0 ≤ s) (ht : theta ≤ t)
    (hΔ : 0 ≤ Δ) (hcon : D ∈ Icc (19/25:ℝ) (stationaryCutoff+Δ))
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    targetRow (2*t-1) t D (targetCapacity s t D) d p ≤
      theta+15*s/16-(49/25)*(t-theta)+2*Δ := by
  by_cases hD : D ≤ stationaryCutoff
  · have hr := target_count_rows hs ht ⟨hcon.1,hD⟩ hd hp
    linarith
  · have hD' : stationaryCutoff ≤ D := le_of_not_ge hD
    have hK : (7/10:ℝ) ≤ 2*t-1 := by
      have hh := kappa_bounds.1
      unfold kappa at hh
      linarith
    have he := target_row_extension (t := t) hs hK hD' hd hp
    have hr := target_count_rows hs ht
      (show stationaryCutoff ∈ Icc (19/25:ℝ) stationaryCutoff by
        constructor; linarith [stationaryCutoff_bounds.1]; exact le_rfl) hd hp
    linarith [hcon.2]

/-- All three positive costs can be chosen before the arithmetic data, below
any requested bound, while retaining strict rows on the extended interval. -/
theorem exists_positive_extended_return
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    {t ε : ℝ} (ht : theta < t) (hε : 0 < ε) :
    ∃ s Δ fee : ℝ, 0 < s ∧ s < ε ∧ s ≤ 1/1000000000 ∧
      0 < Δ ∧ Δ ≤ ε ∧ 0 < fee ∧ fee ≤ ε ∧
      QRH.Record12518109Existence.UniformUnitFaceSource (PositiveSource.face s) ∧
      ∀ D ∈ Icc (19/25:ℝ) (stationaryCutoff+Δ),
        ∀ d ∈ Icc (0:ℝ) (3/4), ∀ p ∈ Icc (0:ℝ) (1/2),
          targetRow (2*t-1) t D (targetCapacity s t D) d p < t-fee := by
  let b := min ((t-theta)/16) ε
  have hb : 0 < b := lt_min (by linarith) hε
  have hbg : b ≤ (t-theta)/16 := min_le_left _ _
  have hbε : b ≤ ε := min_le_right _ _
  obtain ⟨s,hs,hslt,hsmax,hsrc⟩ := PositiveSource.arbitrarily_small hβ hb
  refine ⟨s,b,b,hs,hslt.trans_le hbε,hsmax,hb,hbε,hb,hbε,hsrc,?_⟩
  intro D hD d hd p hp
  have hr := extended_target_rows hs.le ht.le hb.le hD hd hp
  linarith

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.target_row_extension
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.extended_target_rows
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.exists_positive_extended_return
