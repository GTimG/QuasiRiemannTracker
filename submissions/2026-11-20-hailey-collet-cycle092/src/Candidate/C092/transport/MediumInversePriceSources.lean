/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual E19/E25 inverse suppliers from the pinned Bebel/Sil/Collet source
closure, applied with genuine positive open-rectangle decrements. -/
import Candidate.C092.transport.MediumInversePriceScalar
import Candidate.C092.transport.MediumInversePriceGuards
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorContinuum.IdealCurve
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorContinuum.ContactSource
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Driver.Parent

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer ProbeHighRowFamily
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract
open Qrh.TwoSlot.AnchorContinuum

theorem genuine_ideal_rect
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {R δ : ℝ} (hR0 : 3/4 ≤ R) (hR1 : R < 7/9) (hδ : 0 < δ) :
    UniformInverseRectSource canonicalFamily (anchorRect R (Curve.Z (7/9) R) δ) := by
  have h := ideal_anchor pr103Face hβ (Reserve.reserveParametricSource hβ)
    (Driver.pr103_parent hβ) hR0 hR1
  simpa only [ideal] using (h δ hδ).1

theorem genuine_tangent_rect
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {R δ : ℝ} (hR0 : 1467/2000 ≤ R) (hR1 : R ≤ 311/400) (hδ : 0 < δ) :
    UniformInverseRectSource canonicalFamily
      (anchorRect R (Contact.exactLine.g0-Contact.exactLine.g1*R) δ) :=
  ((Contact.tangent_full_moments hβ R hR0 hR1) δ hδ).1

theorem tangent_above_checker {R : ℝ} (hR : 0 ≤ R) :
    5805911/100000000-(379981/5000000)*R ≤
      Contact.exactLine.g0-Contact.exactLine.g1*R := by
  have hc := Contact.tangent_coefficient_bounds
  have hm := mul_le_mul_of_nonneg_right hc.2.2.2.le hR
  dsimp [Contact.exactLine]
  linarith

theorem genuine_curved_anchor
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {r R δ ζ : ℝ} (hr : 3/4 ≤ r) (hδ : 0 < δ)
    (hRlo : r+δ ≤ R) (hRhi : R ≤ r+2*δ) (hRtop : R < 7/9)
    (hζ : 3*δ ≤ ζ) (hz : 0 ≤ QRH.Cycle092.Source.inverseQuota r-ζ) :
    UniformInverseRectSource canonicalFamily (anchorRect R (Curve.Z (7/9) R) δ) ∧
      (anchorRect R (Curve.Z (7/9) R) δ).Admissible r
        (QRH.Cycle092.Source.inverseQuota r-ζ) 1 := by
  exact ⟨genuine_ideal_rect hβ (by linarith) hRtop hδ,
    curved_anchor_admissible hr hδ hRlo hRhi hRtop.le hζ hz⟩

theorem genuine_tangent_anchor
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {r R δ ζ : ℝ} (hr : 0 ≤ r) (hrtop : r < 3/4) (hδ : 0 < δ)
    (hR0 : 1467/2000 ≤ R) (hR1 : R ≤ 311/400)
    (hRlo : r+δ ≤ R) (hRhi : R ≤ r+2*δ) (hζ : 3*δ ≤ ζ)
    (hz : 0 ≤ QRH.Cycle092.Source.inverseQuota r-ζ) :
    UniformInverseRectSource canonicalFamily
      (anchorRect R (Contact.exactLine.g0-Contact.exactLine.g1*R) δ) ∧
      (anchorRect R (Contact.exactLine.g0-Contact.exactLine.g1*R) δ).Admissible r
        (QRH.Cycle092.Source.inverseQuota r-ζ) 1 := by
  exact ⟨genuine_tangent_rect hβ hR0 hR1 hδ,
    tangent_anchor_admissible hr hrtop hδ hRlo hRhi hζ
      (tangent_above_checker (by linarith)) hz⟩

theorem ideal_repeated_inverse_count
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {R δ : ℝ} (hR0 : 3/4 ≤ R) (hR1 : R < 7/9) (hδ : 0 < δ) (εm : ℝ) (hεm : 0 < εm) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ Kbig : ℕ,
    ∀ (D : Cycle25.Weighted.MomentData) (S : Cycle25ProbeFinalAssembly.WeightedSourceData D),
      D.t=εm → (∀ j, D.ell j ≤ mesh/200) →
    ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a ε cutoff T allowance : ℝ) (i : ℕ)
      (B : Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a ε cutoff T allowance i),
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
      B.profile=(fun _ x => (S.w x : ℂ)) → B.upper=(fun _ => 2) →
      B.widths=(fun j => D.ell j/d) → (∀ j, (B.external j).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height : ℝ, 0 ≤ height → 1/2 ≤ a →
      (∀ j, |(B.external j).im| ≤ height) →
      2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let base := B.fiber bin label left right hne;
    ∀ rows : Finset FreeRow, rows ⊆ base.rows → rows.Nonempty →
    ∀ slot : Fin D.N, slot∈base.slots →
      (7/37 : ℝ) ≤ (Kbig : ℝ)*base.widths slot →
    ∀ (selected : Finset (Fin Kbig)) (e buffer : ℝ),
      (anchorRect R (Curve.Z (7/9) R) δ).Admissible base.r ((selected.card : ℝ)*base.widths slot) 1 →
      (∀ u∈rows,(Z^d)^(e*base.widths slot-buffer) ≤
        ‖HeckeDetectorPhysicalSelection.physical S.modulus ⊤ (fun u : FreeRow => u.val)
          base.profile base.upper base.widths base.external (Z^d) u slot‖^2) →
    (rows.card : ℝ) ≤ (12*(1+height)*(C*(1+height)^J))*
      (Z^d)^(1-(2*a-1)*base.r-e*((selected.card : ℝ)*base.widths slot)+
        2*ε+(selected.card : ℝ)*buffer+D.t) := by
  exact original_rect_repeated_inverse_count _ (genuine_ideal_rect hβ hR0 hR1 hδ) εm hεm

theorem tangent_repeated_inverse_count
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {R δ : ℝ} (hR0 : 1467/2000 ≤ R) (hR1 : R ≤ 311/400) (hδ : 0 < δ) (εm : ℝ) (hεm : 0 < εm) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ Kbig : ℕ,
    ∀ (D : Cycle25.Weighted.MomentData) (S : Cycle25ProbeFinalAssembly.WeightedSourceData D),
      D.t=εm → (∀ j, D.ell j ≤ mesh/200) →
    ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a ε cutoff T allowance : ℝ) (i : ℕ)
      (B : Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a ε cutoff T allowance i),
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
      B.profile=(fun _ x => (S.w x : ℂ)) → B.upper=(fun _ => 2) →
      B.widths=(fun j => D.ell j/d) → (∀ j, (B.external j).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height : ℝ, 0 ≤ height → 1/2 ≤ a →
      (∀ j, |(B.external j).im| ≤ height) →
      2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let base := B.fiber bin label left right hne;
    ∀ rows : Finset FreeRow, rows ⊆ base.rows → rows.Nonempty →
    ∀ slot : Fin D.N, slot∈base.slots →
      (7/37 : ℝ) ≤ (Kbig : ℝ)*base.widths slot →
    ∀ (selected : Finset (Fin Kbig)) (e buffer : ℝ),
      (anchorRect R (Contact.exactLine.g0-Contact.exactLine.g1*R) δ).Admissible base.r ((selected.card : ℝ)*base.widths slot) 1 →
      (∀ u∈rows,(Z^d)^(e*base.widths slot-buffer) ≤
        ‖HeckeDetectorPhysicalSelection.physical S.modulus ⊤ (fun u : FreeRow => u.val)
          base.profile base.upper base.widths base.external (Z^d) u slot‖^2) →
    (rows.card : ℝ) ≤ (12*(1+height)*(C*(1+height)^J))*
      (Z^d)^(1-(2*a-1)*base.r-e*((selected.card : ℝ)*base.widths slot)+
        2*ε+(selected.card : ℝ)*buffer+D.t) := by
  exact original_rect_repeated_inverse_count _ (genuine_tangent_rect hβ hR0 hR1 hδ) εm hεm

#print axioms genuine_ideal_rect
#print axioms genuine_tangent_rect
#print axioms ideal_repeated_inverse_count
#print axioms tangent_repeated_inverse_count
end
end QRH.Cycle092.MediumInversePrice
