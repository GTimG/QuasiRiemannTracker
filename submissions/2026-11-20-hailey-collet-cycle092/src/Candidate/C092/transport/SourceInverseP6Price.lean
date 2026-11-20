/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The exact source-side P6 powers are paid at their same enlarged radius.
Only the final scalar comparison pays the conductor-radius offset. -/
import Candidate.C092.transport.SourceInverseP6LongActual
import Candidate.C092.transport.SourceInverseP6Masks

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open QRH.Cycle092.MediumInversePrice

theorem actual_inverse_power_paid {y e ν : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ,0 < fee ∧
    ∀ (n d r L wi wl ε εm εshort εnative bi bl ni qi error : ℝ) (ki kl : ℕ),
      n ≤ sourceRatio*y → 0 ≤ d → 367/500 ≤ r → (c.inverse:ℝ) ≤ r → r ≤ 1 →
      L ≤ sourceWidth n y-(u:ℝ) →
      2*NativeFourthEffective.credit n d-ni ≤ (kl:ℝ)*wl →
      inverseQuota r-qi ≤ (ki:ℝ)*wi → ni ≤ fee → qi ≤ fee →
      d*εshort+(d*(2*ε+(ki:ℝ)*bi+εm)+d*εnative+(kl:ℝ)*bl)/2 ≤ error → error ≤ fee →
      d+ν*y+e*(L-(kl:ℝ)*wl/2)-d*(ν*r+e*((ki:ℝ)*wi))/2+
        d*εshort+(d*(2*ε+(ki:ℝ)*bi+εm)+d*εnative+(kl:ℝ)*bl)/2 < d+radialAllowance d := by
  obtain ⟨fee,hfee,_,hpay⟩ := uniform_corrected_inverse_cell_fee c hy he hν hν1 hg hp
  refine ⟨fee,hfee,?_⟩
  intro n d r L wi wl ε εm εshort εnative bi bl ni qi error ki kl hn hd hr0 hr hr1 hL hn' hi hni hqi hloss hefee
  have h := hpay n hn r d hr0 hr hr1 hd L ((kl:ℝ)*wl) ((ki:ℝ)*wi) ni qi error hL hn' hi hni hqi hefee
  unfold repeatedPrice at h
  linarith

theorem actual_long_inverse_power_paid {y e ν : ℝ} (c : Cutoff)
    (hy0 : (369/1000:ℝ) ≤ y) (hy : y ≤ sourceY) (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ,0 < fee ∧
    ∀ (n d r L wl ε εm εshort εnative bl ni error : ℝ) (kl : ℕ),
      n ≤ sourceRatio*y → 0 ≤ d → 1 ≤ r → r ≤ (c.inverse:ℝ)+(c.ordinary:ℝ) →
      L ≤ sourceWidth n y-(u:ℝ) →
      2*NativeFourthEffective.credit n d-ni ≤ (kl:ℝ)*wl → ni ≤ fee →
      d*εshort+(d*(2*ε+εm)+d*εnative+(kl:ℝ)*bl)/2 ≤ error → error ≤ fee →
      d+ν*y+e*(L-(kl:ℝ)*wl/2)-d*QRH.Cycle092.Source.longDeficit ν r/2+
        d*εshort+(d*(2*ε+εm)+d*εnative+(kl:ℝ)*bl)/2 < d+radialAllowance d := by
  obtain ⟨fee,hfee,hpay⟩ := uniform_corrected_long_cell_fee c hy0 hy he hν hν1 hg hp
  refine ⟨fee,hfee,?_⟩
  intro n d r L wl ε εm εshort εnative bl ni error kl hn hd hr0 hr1 hL hn' hni hloss hefee
  have h := hpay n hn r d hr0 hr1 hd L ((kl:ℝ)*wl) (QRH.Cycle092.Source.longDeficit ν r)
    ni 0 error hL hn' (by linarith) hni (by linarith) hefee
  unfold countedPrice at h
  linarith

theorem actual_radius_offset_once {power V d δ : ℝ}
    (hp : power < d+radialAllowance d) (hVd : V ≤ d) (hdV : d ≤ V+3*δ) :
    power < V+radialAllowance V+3*δ :=
  hp.trans_le (QRH.Cycle092.MediumReplace.Source.enlarged_price hVd hdV)

#print axioms actual_inverse_power_paid
#print axioms actual_long_inverse_power_paid
#print axioms actual_radius_offset_once
end
end QRH.Cycle092.SourceInverseP6
