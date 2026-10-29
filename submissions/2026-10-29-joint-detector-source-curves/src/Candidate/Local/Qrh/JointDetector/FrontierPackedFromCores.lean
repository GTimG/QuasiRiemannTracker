/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed selected cutoff .500000001, same original-row event and full amplitude supremum.
Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.FrontierRepeatedWeightedHigh
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.WholeCountFromCores
import Candidate.Local.Qrh.JointDetector.FrontierSelectedCount

namespace Qrh.JointDetector.FrontierRepeatedMarks
noncomputable section
open Set RepeatedMarks
open OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree

/-- Compose the literal physical-core count with the full natural lift and
weighted HIGH supplier. In combined stages the selected norm is applied to
the same original row event before taking the amplitude supremum. -/
theorem wholeWeightedHigh_of_physicalCoreCount
    (B L c floor : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 1) (hL : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hf : (2/5:ℝ) ≤ floor)
    (combined : Bool) (hselectedFloor : combined = true → (50001/100000:ℝ) ≤ floor)
    (hnorm : FrontierNaturalCount.ActualSelectedSlotNorm)
    (high : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hhigh : ∀ q (hq : q ∈ Ioc (0:ℝ) (3/4)), floor ≤ q → ∀ P s M,
      high q P s M = (repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).high P s M)
    (hcore : PhysicalCoreCount floor B L c) :
    WeightedSupplier.WholeWeightedHigh floor high := by
  have hrep := wholeRepeatedCountOn_of_physicalCoreCount hf hB0 hB hL hc0 hc hcore
  cases combined with
  | false =>
    exact FrontierRepeatedWeightedHigh.wholeWeightedHigh_of_repeated B L c floor
      hB0 hB hL hc0 hc hf high hhigh hrep
  | true =>
    have hsel := FrontierSelectedCount.wholeSelectedCountOn_of_actualSelectedSlotNorm
      hnorm floor (hselectedFloor rfl)
    have hboth := FrontierRepeatedWeightedHigh.wholeCombinedCountOn_of_repeated_selected
      floor B L c hrep hsel
    exact FrontierRepeatedWeightedHigh.wholeWeightedHigh_of_combined B L c floor
      hB0 hB hL hc0 hc hf high hhigh hboth

/-- Generic packed leaf, preserving the real parent source and arbitrary
bounded moving density cut. The physical core theorem remains explicit
until its arithmetic construction has been supplied. -/
theorem priced_source_of_physicalCoreCount
    (B L c floor : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 1) (hL : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hf : (2/5:ℝ) ≤ floor)
    (combined : Bool) (hselectedFloor : combined = true → (50001/100000:ℝ) ≤ floor)
    (hnorm : FrontierNaturalCount.ActualSelectedSlotNorm)
    (high : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hhigh : ∀ q (hq : q ∈ Ioc (0:ℝ) (3/4)), floor ≤ q → ∀ P s M,
      high q P s M = (repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).high P s M)
    (hcore : PhysicalCoreCount floor B L c)
    (B0 L0 c0 Mmin Mmax Lplain : ℝ) (hL0 : 0 < L0)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 0 < B0 ∧ B0 ≤ 1 ∧ 0 < c0) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax)
    (hparent : QRH.Record1252270103Source.GlobalSource B0 L0 c0)
    (qfun : ℝ → ℝ) (hqfun : ∀ w, qfun w ∈ Icc floor (3/4))
    (price : Price)
    (hprice : ∀ w P s M, price.f w P s M =
      max (qfun w*deletionNeed B0 L0 c0 P s M) (high (qfun w) P s M)) :
    PricedPackedSource price Mmin Mmax Lplain := by
  apply WeightedSupplier.priced_source_of_weighted_high floor high (by linarith)
    (wholeWeightedHigh_of_physicalCoreCount B L c floor hB0 hB hL hc0 hc hf
      combined hselectedFloor hnorm high hhigh hcore)
    B0 L0 c0 Mmin Mmax Lplain hL0 hβ hface h0 h1 hparent qfun hqfun price hprice

#print axioms wholeWeightedHigh_of_physicalCoreCount
#print axioms priced_source_of_physicalCoreCount
end
end Qrh.JointDetector.FrontierRepeatedMarks
