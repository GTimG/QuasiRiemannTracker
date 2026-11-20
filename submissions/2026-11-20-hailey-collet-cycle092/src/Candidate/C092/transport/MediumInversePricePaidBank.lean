/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A checked P.2 cell supplies actual finite inverse sources and one uniform
strict payment budget before rows, scale, and inverse witnesses are chosen. -/
import Candidate.C092.transport.MediumInversePriceSourceBank
import Candidate.C092.transport.MediumInversePriceUniformScalar

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open OAI OAI.SevenEighths
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open Qrh.MarkedAnchor.Interface.Contract

theorem paid_genuine_inverse_bank
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {y e ν : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧ fee ≤ 1/2 ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/1000 ∧ 3*δ ≤ fee/4 ∧
    ∃ J : ℕ, ∃ bank : Fin J → AnchorRect,
      (∀ i, UniformInverseRectSource canonicalFamily (bank i)) ∧
      (∀ r : ℝ, 367/500 ≤ r → r ≤ 1 →
        inverseQuota r ≤ fee/4 ∨
          (0 ≤ inverseQuota r-fee/4 → ∃ i, (bank i).Admissible r (inverseQuota r-fee/4) 1)) ∧
      (∀ n : ℝ, n ≤ sourceRatio*y → ∀ r V : ℝ, 367/500 ≤ r → (c.inverse : ℝ) ≤ r → r ≤ 1 → 0 ≤ V →
        ∀ (live nativeWidth inverseWidth nativeLoss inverseLoss error : ℝ),
          live ≤ sourceWidth n y-(u : ℝ) →
          2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth →
          inverseQuota r-inverseLoss ≤ inverseWidth →
          nativeLoss ≤ fee → inverseLoss ≤ fee → error ≤ fee →
        repeatedPrice y e ν V r live nativeWidth inverseWidth+error < radialAllowance V) := by
  obtain ⟨fee,hfee,hhalf,hpay⟩ := uniform_corrected_inverse_cell_fee c hy he hν hν1 hg hp
  obtain ⟨δ,hδ,hsmall,hδfee,J,bank,hsource,hcover⟩ :=
    finite_genuine_inverse_sources hβ (show 0 < fee/4 by positivity)
  exact ⟨fee,hfee,hhalf,δ,hδ,hsmall,hδfee,J,bank,hsource,hcover,hpay⟩

#print axioms paid_genuine_inverse_bank
end
end QRH.Cycle092.MediumInversePrice
