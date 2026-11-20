/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual event-free P6 suppliers on a finite bank of checked length/response
labels. Scalar fees, the common genuine rectangle bank and all physical
source meshes precede Slot, arithmetic data and live rows. -/
import Candidate.C092.transport.P2CommonSourceMetadataTypes
import Candidate.C092.transport.TerminalActualInverseApplyFiniteBank
import Candidate.C092.transport.StrongPairRegularTerminalNativeCaps

set_option autoImplicit false
set_option linter.unusedVariables false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorZeros
open CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentInductionEnergy
open QRH.Cycle092.PairMarkAnchor QRH.Cycle092.LowActual
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open Qrh.MarkedAnchor.Interface QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.MediumInversePrice QRH.Cycle092.TinyCore
open QRH.Cycle092.TerminalActualRow QRH.Cycle092.RegularColoredForward
open QRH.Cycle092.SourceInverseP6
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataBank_d293fbc320237ef7_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- One finite genuine source bank with a common positive physical mesh.
Native cap/quota guards and their payment are proved at every genuine bank
radius. The final physical suppliers still quantify Slot AFTER this mesh. -/
theorem common_early_actual_class_bank {Key : Type} [Fintype Key]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (n y el ν : Key→ℝ) (cut : Key→Cutoff) (bcell : Key→ℚ)
    (hy0 : ∀ k,sourceY0 ≤ y k) (hy1 : ∀ k,y k ≤ sourceY) (hyn : ∀ k,y k ≤ n k)
    (hn : ∀ k,n k ≤ sourceRatio*y k) (he : ∀ k,0 ≤ el k)
    (hν0 : ∀ k,el k ≤ ν k) (hν1 : ∀ k,ν k ≤ 3/4)
    (hg : ∀ k,CutoffGuard (bcell k) (cut k))
    (hp : ∀ k,PaidWithBand (y k) (el k) (ν k) (cut k))
    {loss : ℝ} (hloss : 0 < loss) (heightLoss : ℝ) (hheightLoss : 0 ≤ heightLoss)
 :
    ∃ feeM feeU commonFee : Key→ℝ,
      (∀ k,0 < feeM k ∧ 0 < feeU k ∧ 0 < commonFee k ∧ commonFee k ≤ feeM k ∧ commonFee k ≤ feeU k) ∧
    ∃ ζ : ℝ,0 < ζ ∧ (∀ k,ζ ≤ commonFee k/2) ∧
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1/1000 ∧ 3*δ ≤ ζ ∧
    ∃ J : ℕ,∃ bank : Fin J → Contract.AnchorRect,
      (∀ j,Contract.UniformInverseRectSource Contract.canonicalFamily (bank j)) ∧
      (∀ r : ℝ,367/500 ≤ r → r ≤ 1 →
        inverseQuota r ≤ ζ ∨ (0 ≤ inverseQuota r-ζ → ∃ j,(bank j).Admissible r (inverseQuota r-ζ) 1)) ∧
    ∀ (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (dBank : Finset ℝ) (hdb : ∀ d∈dBank,(98/100:ℝ) ≤ d ∧ dmin ≤ d ∧ d ≤ dmax)
    (price : ℝ) (hprice0 : 0 ≤ price) (hpriceBudget : price*dmax ≤ loss/4),
    ∃ quota : Key→dBank→ℝ,
      (∀ k d,0 ≤ terminalNativeCap (n k) d.val ∧ terminalNativeCap (n k) d.val < 1/2 ∧
        0 < quota k d ∧ quota k d < 3/20 ∧ quota k d < (1-2*terminalNativeCap (n k) d.val)/2 ∧
        2*NativeFourthEffective.credit (n k) d.val-d.val*quota k d ≤ commonFee k/4 ∧
        ∀ {U X : ℝ},0 < U → length U X ≤ n k → length (U^d.val) X ≤ terminalNativeCap (n k) d.val) ∧
    ∃ im nm : Key→dBank→Fin J→ℝ,∃ nu : Key→dBank→ℝ,
      (∀ k d j,0 < im k d j ∧ 0 < nm k d j) ∧ (∀ k d,0 < nu k d) ∧
    ∃ mesh : ℝ,0 < mesh ∧
      (∀ k d j,mesh ≤ im k d j ∧ mesh ≤ nm k d j) ∧ (∀ k d,mesh ≤ nu k d) ∧
      (∀ k d j,TerminalActualClassMarkedPhysical (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeM k)
        (bank j) εm nativeError (terminalNativeCap (n k) d.val) (quota k d) dmin dmax price (im k d j) (nm k d j)) ∧
      (∀ k d,TerminalActualClassUnmarkedPhysical (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeU k)
        εm nativeError (terminalNativeCap (n k) d.val) (quota k d) dmin dmax price (nu k d)) := by
  obtain ⟨feeM,feeU,fc,hfee,hM,hU,ζ,hζ,hζf,δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover⟩ :=
    terminal_finite_actual_class_inverse_bank hβ n y el ν cut bcell
      (by intro k;simpa only [sourceY0] using hy0 k) hy1 hn he hν0 hν1 hg hp hloss heightLoss hheightLoss
  refine ⟨feeM,feeU,fc,hfee,ζ,hζ,hζf,δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover,?_⟩
  intro εm nativeError hεm hnativeError dmin dmax hdmin hdmax dBank hdb price hprice0 hpriceBudget
  have hnat (k : Key) (d : dBank) := terminal_native_source_parameters (hy0 k) (hy1 k) (hyn k) (hn k)
    (hdb d.val d.property).1 (hfee k).2.2.1
  choose quota hN0 hN hq hqcap hqmean hbudget hlength using hnat
  have hm (k : Key) (d : dBank) (j : Fin J) :
      ∃ im nm : ℝ,0 < im ∧ 0 < nm ∧
        TerminalActualClassMarkedPhysical (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeM k)
          (bank j) εm nativeError (terminalNativeCap (n k) d.val) (quota k d) dmin dmax price im nm := by
    simpa only [TerminalActualClassMarkedPhysical] using
      hM k hβ (bank j) (hsource j) εm nativeError hεm hnativeError (hN k d).le
        (hq k d).le (hqcap k d) (hqmean k d) dmin dmax hdmin hdmax price hprice0 hpriceBudget
  have hu (k : Key) (d : dBank) :
      ∃ nu : ℝ,0 < nu ∧
        TerminalActualClassUnmarkedPhysical (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeU k)
          εm nativeError (terminalNativeCap (n k) d.val) (quota k d) dmin dmax price nu := by
    simpa only [TerminalActualClassUnmarkedPhysical] using
      hU k hβ εm nativeError hεm hnativeError (hN k d).le
        (hq k d).le (hqcap k d) (hqmean k d) dmin dmax hdmin hdmax price hprice0 hpriceBudget
  choose im nm him hnm hmarked using hm
  choose nu hnu hunmarked using hu
  let meshes : (Key×dBank×Fin J)⊕(Key×dBank)→ℝ :=
    Sum.elim (fun p=>min (im p.1 p.2.1 p.2.2) (nm p.1 p.2.1 p.2.2)) (fun p=>nu p.1 p.2)
  have hmeshes : ∀ k,0 < meshes k := by
    intro k
    cases k with
    | inl p => exact lt_min (him p.1 p.2.1 p.2.2) (hnm p.1 p.2.1 p.2.2)
    | inr p => exact hnu p.1 p.2
  obtain ⟨mesh,hmesh,hfloor⟩ := terminal_positive_mesh_floor meshes hmeshes
  refine ⟨quota,
    fun k d=>⟨hN0 k d,hN k d,hq k d,hqcap k d,hqmean k d,hbudget k d,hlength k d⟩,
    im,nm,nu,fun k d j=>⟨him k d j,hnm k d j⟩,hnu,mesh,hmesh,?_,?_,hmarked,hunmarked⟩
  · intro k d j
    have h := hfloor (Sum.inl (k,d,j))
    exact ⟨h.trans (min_le_left _ _),h.trans (min_le_right _ _)⟩
  · intro k d
    exact hfloor (Sum.inr (k,d))

#print axioms common_early_actual_class_bank
end
end QRH.Cycle092.StrongPair
