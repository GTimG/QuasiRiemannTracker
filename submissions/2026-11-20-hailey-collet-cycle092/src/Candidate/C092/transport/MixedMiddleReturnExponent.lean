/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact second/fourth physical telescope, including the LOWER true dilation
and the current ordinary tangent left over from the centered count. -/
import Candidate.C092.transport.ActualMixedPriceAll
import Candidate.C092.transport.StrongPairSource
import Candidate.C092.transport.SelectedNonfloorPrice

set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open QRH.Cycle090 QRH.Cycle092 QRH.ContactCertificate
open QRH.Cycle092.Mixed

/-- Exact algebra retaining both genuine contact coefficients. -/
theorem middle_telescope (δ p R nref z m pen cap L inv v g₀ g₁ : ℝ)
    (hR : R=1-δ*(p*(1+2*g₀)+2*(1-p*(1+2*g₁))*m)) :
    δ*p*(L-sourceWidth nref z)+inv-δ*z/2+(R+1)/2-
        δ*(pen-(1-p*(1+2*g₁))*(z-m))/2-δ*v/2 =
    (δ*p*(L-cap/2)+inv+(3*R+1)/4)-
      δ*(p*(g₁*z-g₀/2+sourceGain z)+pen/2)+
        δ*p*(cap+nref-1/2)/2-δ*v/2 := by
  rw [hR]
  unfold sourceWidth
  ring

/-- The real lower dilation pays the reference extension, with the positive
(1-p) coefficient damping retained. No count face is relabeled. -/
theorem middle_gain_of_reference {δ p R nref z m pen cap L inv v g₀ g₁ n0 collar : ℝ}
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hp' : p ≤ 1) (hv : 0 ≤ v)
    (hcap : cap ≤ n0-1/2) (href : nref ≤ 1-n0+v+collar)
    (hR : R=1-δ*(p*(1+2*g₀)+2*(1-p*(1+2*g₁))*m)) :
    δ*p*(L-sourceWidth nref z)+inv-δ*z/2+(R+1)/2-
      δ*(pen-(1-p*(1+2*g₁))*(z-m))/2-δ*v/2  ≤ 
    (δ*p*(L-cap/2)+inv+(3*R+1)/4)-
      δ*(p*(g₁*z-g₀/2+sourceGain z)+pen/2-p*collar/2)-δ*(1-p)*v/2 := by
  rw [middle_telescope δ p R nref z m pen cap L inv v g₀ g₁ hR]
  have h := mul_le_mul_of_nonneg_left (show cap+nref-1/2 ≤ v+collar by linarith)
    (mul_nonneg hδ hp)
  nlinarith only [h]

/-- The physical Q capacity itself satisfies the zero-shift reference bound. -/
theorem actual_capacity_reference {n0 cost : ℝ} (hn0 : 1/2 ≤ n0) (hc : 0 ≤ cost) :
    min physicalCap ((2*n0-1-cost)/(2+10*cost))  ≤  n0-1/2 := by
  apply (min_le_right _ _).trans
  apply (div_le_iff₀ (by positivity : 0<2+10*cost)).mpr
  nlinarith only [hc,mul_nonneg hc (show 0 ≤ n0-1/2 by linarith)]

/-- Once the literal analytic middle power is obtained, Q's checked physical
reserve pays the exact current debit including padding and the common fee. -/
theorem physical_reserve {r : TopData.Row} (hr : r∈TopData.rows)
    {h x D ξ z : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : (1/100:ℝ) ≤ D) (hDh : D ≤ h+rowPad)
    (hξ : 0 ≤ ξ) (hξ' : ξ ≤ (Mixed.rowGamma r.box r.B:ℝ))
    (hz : widthLo ≤ z) (hz' : z ≤ widthHi) :
    Physical.price h point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) D-
      D*point.1*ActualMixedPrice.gain r point.2 x ξ z+
      paddingDebit+(1/100000000000000:ℝ) < theta-1/1000000000000 := by
  have hs := ActualMixedPrice.all_rows_uniform_physical_reserve hr hh hh' hp hx hD hDh hξ hξ' hz hz'
  have he : Physical.price h point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) D-theta  ≤ 
      ActualMixedPrice.excess h point.1 point.2 x D := by
    have hh := le_max_right 0 (Physical.price h point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) D-theta+inwardDebit)
    change _  ≤  max 0 _
    have hfee : 0 ≤ inwardDebit := by norm_num [inwardDebit]
    linarith
  dsimp [ActualMixedPrice.saving] at hs
  linarith

#print axioms middle_gain_of_reference
#print axioms physical_reserve
end
end QRH.Cycle092.MixedMiddleReturn
