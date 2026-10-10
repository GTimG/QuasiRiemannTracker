import Cycle25.Numerator.SourcePrimeBins
import Cycle25.Assembly.Weighted.SourceScalar
import Cycle25.Assembly.Count.WeightedSourceMaskedCount

/-! Actual source amplitude estimates on the retained external rectangle. -/
noncomputable section
open scoped Classical BigOperators
open Filter
namespace Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25.Weighted Cycle25WeightedHighFinalAssembly Cycle25NumeratorHighFinalAssembly HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem actual_source_prime_upper {Δ:ℝ} (D:HighParameters.HighData Δ)
    (F:WeightedSourceData D.toMomentData) (τ:ℝ) (n:ℕ)
    (hτ:0 < τ) (hheight:4*τ < (1/200:ℝ)*D.cost) :
    ∀ᶠZ:ℝ in atTop,∀(rows:Finset FreeRow) (d a:ℝ) (i:ℕ),
      1/2≤d → d≤h+rowExtension → 51/100≤a → a≤7/8 → i≤n →
      ∀η:Character,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t)) →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      ∀p∈FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),∀u∈rows,∀j:Fin D.N,
      let Q := HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j))
        ((17/50:ℂ)+p.2*Complex.I)
      ‖Q‖≤(Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) ((2*a-1)/2) D.t Q+D.t) := by
  filter_upwards [weighted_source_prime_bins D F τ n hτ hheight] with Z hbins
  intro rows d a i hd hdmax ha hatop hi η hrows hnext p hp u hu j
  have hd' : d≤7/8 := by norm_num [rowExtension] at hdmax;linarith [Cycle25.h_interval.2]
  have hb := hbins d (by linarith) hd' η u (hrows u hu).1 (hrows u hu).2.1
    (hrows u hu).2.2 a i hi ha (by linarith) (hnext u hu) ((17/50:ℂ)+p.2*Complex.I)
    (by norm_num) (by simpa using hp.2) j
  have he : a-1/2=(2*a-1)/2 := by ring
  simpa only [he] using hb.2.2.2.1

end Cycle25.Numerator
end
