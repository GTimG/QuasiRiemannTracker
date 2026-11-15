/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Canonical physical class count, including the masked selection mean, without
a fixed-fee schedule. Adapted from PR137 PublicCount and MaskedSourceCount
(Sil, Hailey Collet and predecessor authors, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSourceCount
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.MaskedSourceCount

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators
open Filter
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open Cycle25DetectorRowCount
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

theorem canonical_source_count (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (F : SourceData)
    (counts : CountParameters F.modulus ⊤ D.t) (τ sigma : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t)
    (herror : 159*D.ε+609*D.t ≤ sigma) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d a C0 : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀ z : ℂ, z.re = 17/50 → |z.im| ≤ Z^(2*τ) →
      SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := canonicalFamily D F Z z
      ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
        (fun j => D.length j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j => D.length j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧ (rows'.card : ℝ) ≤ C*C0*
        (Z^d)^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope D.momentKappa
          (2*a-1) (q/(2*a-1))+sigma) := by
  obtain ⟨C,hC,hcount⟩ := physical_source_amplitude_count D F counts τ n hτ hτzero hτheight hτ2
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hdp : 0 < d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  rw [physical_eq_canonical D F Z d hZp hdp.ne'] at hb
  have hbound := hb bin hne
  refine ⟨hbound.1,hbound.2.1,?_⟩
  apply hbound.2.2.trans
  apply Cycle61DetectorCount.source_error_absorption Z d D.t D.ε _ sigma (C*C0)
    hZ.le hd D.t_pos.le
  · exact mul_nonneg (by linarith) (by linarith)
  · exact herror

/-- The physical count for the same full amplitude class at the mean used by
whole-slot selection. Source moments remain the genuine field input. -/
theorem masked_source_count (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (F : SourceData)
    (counts : CountParameters F.modulus ⊤ D.t) (τ sigma : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t)
    (herror : 159*D.ε+609*D.t ≤ sigma) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d a C0 : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀ z : ℂ, z.re = 17/50 → |z.im| ≤ Z^(2*τ) →
      SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := canonicalFamily D F Z z
      ∀ main : Finset (Fin D.N),
      ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
        (fun j => D.length j/d) Q bin
      let q := weightedMean Finset.univ (fun j => D.length j/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧ (rows'.card : ℝ) ≤ C*C0*
        (Z^d)^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope D.momentKappa
          (2*a-1) (q/(2*a-1))+sigma) := by
  obtain ⟨K,hK,hcount⟩ := canonical_source_count D F counts τ sigma n hτ hτzero hτheight hτ2 herror
  refine ⟨K,hK,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0 < d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  have hcard := (hb bin hne).2.2
  exact masked_class_count rows Finset.univ main (Z^d) (2*a-1) D.momentKappa D.t D.t_pos
    (fun j => D.length j/d) (canonicalFamily D F Z z) bin (by linarith) (by linarith)
    D.momentKappa_lo D.momentKappa_hi (Real.one_le_rpow hZ.le hdpos.le)
    (fun j _ => (div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum]; exact div_pos Geometry.ell_pos hdpos)
    (K*C0) sigma (by positivity) hne hcard

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.canonical_source_count
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.masked_source_count
