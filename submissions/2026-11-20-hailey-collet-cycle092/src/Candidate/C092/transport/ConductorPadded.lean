/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Extend every top direct price through the actual row padding using the
literal capacity. The second bound on R can be supplied by counting the
whole row ball, independently of the chosen detector route. -/
import Candidate.C092.transport.ConductorRouteCover

namespace QRH.Cycle092.Direct
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.Coverage QRH.PhysicalCertificate QRH.ContactCertificate
open QRH.Cycle092.ActualMixedPrice

theorem capacity_lower_slope {cap s y d D : ℝ} (hcap : 0 ≤ cap) (hs : 0 ≤ s) (hD : d ≤ D) :
    cappedCapacity cap y s d -(D-d)/2 ≤ cappedCapacity cap y s D := by
  let den := 2+10*s
  have hden : 0 < den := by dsimp [den]; linarith
  have hslope : (1+s)/den ≤ 1/2 := (div_le_iff₀ hden).mpr (by dsimp [den]; linarith)
  have h₀ : cappedCapacity cap y s d ≤ cap*d := min_le_left _ _
  have h₁ : cappedCapacity cap y s d ≤ (2*y-(1+s)*d)/den := min_le_right _ _
  apply le_min
  · linarith [mul_le_mul_of_nonneg_left hD hcap]
  · have heq : (2*y-(1+s)*d)/den-(1+s)/den*(D-d)=(2*y-(1+s)*D)/den := by ring
    change _ ≤ (2*y-(1+s)*D)/den
    linarith only [h₁,heq,mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hD)]

theorem upper_padding_cost {base delta p R d D : ℝ} (y : ℝ) (hδ : 0 ≤ delta*p)
    (hδ' : delta*p ≤ 1) (hR : R ≤ 2) (hd : d ≤ D) :
    conductorPrice base delta p R (cappedCapacity physicalCap y sourceCost D) D ≤
    conductorPrice base delta p R (cappedCapacity physicalCap y sourceCost d) d + 2*(D-d) := by
  have hdiff := capacity_lower_slope (y:=y) (show 0 ≤ physicalCap by norm_num [physicalCap])
    (show 0 ≤ sourceCost by unfold sourceCost; positivity) hd
  have hweight := mul_le_mul_of_nonneg_left hdiff hδ
  have hsmall := mul_le_mul_of_nonneg_right hδ' (sub_nonneg.mpr hd)
  have hr := mul_le_mul_of_nonneg_right hR (sub_nonneg.mpr hd)
  unfold conductorPrice
  nlinarith only [hweight,hsmall,hr,hd]

/-- Above the last edge the complete original certificate cover still holds.
One true direct endpoint suffices; the padding is paid once in Z units. -/
theorem top_padded_cover {h x D : ℝ} {point : Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : h ≤ D) (hd : D ≤ h+rowPad) (hp : originalDomain.Contains point) :
    (∃ l : DirectLeaf, endpointMember 3 l point ∧ ∀ R : ℝ,
      R ≤ leafCount l point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) → R ≤ 2 →
      conductorPrice (priceBase h point.1 point.2) point.1 point.2 R
        (cappedCapacity physicalCap (yLength h) sourceCost D) D ≤ theta-1/125000000+2*rowPad) ∨
        ExteriorPaid h x D point ∨ MixedPaid h x D point := by
  have hd' : (1/100:ℝ) ≤ D := (by norm_num [hLower] : (1/100:ℝ) ≤ hLower).trans (hh.trans hD)
  rcases full_original_price_cover 3 hh hh' hx hd' hd hp with hdir|h
  · obtain ⟨i,he,l,hl,hp',hc⟩ := direct_paid_count hh hdir
    refine Or.inl ⟨l,⟨i,he,hl,hp'⟩,?_⟩
    intro R hR hR'
    have hu₀ : 0 ≤ point.1 := by simpa [originalDomain] using hp.1
    have hv₀ : 0 ≤ point.2 := by simpa [originalDomain] using hp.2.2.1
    have hu : point.1 ≤ 3/4 := by simpa [originalDomain] using hp.2.1
    have hv : point.2 ≤ 1/2 := by simpa [originalDomain] using hp.2.2.2
    have hp₁ : point.1*point.2 ≤ 1 := (mul_le_mul hu hv hv₀ (by norm_num)).trans (by norm_num)
    have hpad := upper_padding_cost (base:=priceBase h point.1 point.2) (R:=R) (yLength h) (mul_nonneg hu₀ hv₀) hp₁ hR' hD
    apply hpad.trans
    have hh0 : 0 ≤ h := (by norm_num [hLower] : 0 ≤ hLower).trans hh
    let k := leafCount l point.1 point.2 (g0 (wValue x)) (g1 (wValue x))
    change conductorPrice _ _ _ k (cappedCapacity physicalCap (yLength h) sourceCost h) h ≤ _ at hc
    have hn : conductorPrice (priceBase h point.1 point.2) point.1 point.2 R
      (cappedCapacity physicalCap (yLength h) sourceCost h) h ≤ theta-1/125000000 := by
      apply le_trans _ hc
      unfold conductorPrice; nlinarith only [mul_le_mul_of_nonneg_left (show R ≤ k from hR) hh0]
    linarith
  · exact Or.inr h

#print axioms top_padded_cover
end
end QRH.Cycle092.Direct
