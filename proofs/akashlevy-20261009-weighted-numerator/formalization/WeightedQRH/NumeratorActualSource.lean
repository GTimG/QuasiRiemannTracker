import WeightedQRH.NumeratorSourceCollect
import WeightedQRH.NumeratorActualSourceHelpers
import WeightedQRH.HighRows.WeightedSourceRawCells

/-! The actual source row bound. Every count, phase, coefficient, polynomial
moment, local Euler, and scalar estimate is supplied by a checked theorem. -/
noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators
open Filter
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open WeightedHighFinalAssembly ProbeFinalAssemblyCertifiedBands
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- The raw analytic input for the actual full-w source follows from the
certified moments and source estimates, without an added analytic hypothesis. -/
theorem actual_raw_fullW_input : RawFullWAnalyticInput := by
  intro hβ D hfine F counts
  have hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta := by
    have ht : (51/100:ℝ)<theta := by norm_num [theta]
    exact (ht.trans hβ).le
  obtain ⟨Jw,hJw,C,hC,hcollect⟩ := source_integrated_amplitude_classes D F hbeta hfine
  obtain ⟨Cs,hCs,hscalar⟩ := weighted_source_scalar_on_rows D F
  refine ⟨Jw,hJw,?_⟩
  intro τ hτ hτzero hτheight hτt hτ2 hτeps hτJ n η
  obtain ⟨K,hK,hcount⟩ := weighted_source_masked_amplitude_count D F counts τ n hτ hτzero hτheight hτ2
  refine ⟨C*Cs*K,by have := zero_lt_one.trans_le hK;positivity,?_⟩
  filter_upwards [eventually_uniform_source_conductor (1/2) (by norm_num) hcollect,
    hcount η,actual_source_prime_upper D F τ n hτ hτheight,
    source_prime_reconstruction_geometry F η,weighted_source_pools_nonempty D F,
    weighted_source_height_le τ n hτ,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hcollect hcount hupper hgeo hpools hheight hT hZ
  intro C0 hC0 hmom
  unfold RawSourceDyadBound
  intro rows d a i hd hdmax ha hatop hδ hi hsource hrows hrow hfreq hnext hcurrent p hp
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hd' : d≤7/8 := by norm_num [h,rowExtension] at hdmax;linarith
  have hz : ((17/50:ℂ)+p.2*Complex.I).re=17/50 := by norm_num
  have hx : ((((a+16*D.e):ℝ):ℂ)+p.1*Complex.I).re=a+16*D.e := by simp
  have hzim : |((17/50:ℂ)+p.2*Complex.I).im|≤((3*i+1:ℕ):ℝ)*Z^τ := by simpa using hp.2
  have hupper' := hupper rows d a i hd hdmax ha.le hatop hi η
    (fun u hu=>(hsource u hu).2) hnext p hp
  have hscalar' := hscalar η rows Z τ d a i hZ0 hT ha.le hatop hfreq
    (fun u hu=>(hrows u hu).2) hnext p hp
  have hcounts := hcount d a C0 (by linarith) hd' ha hatop hC0 rows hsource i hi hnext hcurrent
    ((17/50:ℂ)+p.2*Complex.I) hz (hzim.trans (hheight i hi).2) hmom
  have hbase : ∀j,sourcePrimePool F Z j := fun j=>⟨(hpools j).choose,(hpools j).choose_spec⟩
  have hc := hcollect d hd
  -- The remaining line instantiates the literal finite-collection theorem.
  exact hc.2 Z d hZ hd hdmax rfl η
    ((((a+16*D.e):ℝ):ℂ)+p.1*Complex.I) ((17/50:ℂ)+p.2*Complex.I)
    a (((3*i+1:ℕ):ℝ)*Z^τ) ha.le hatop hδ hx hz (hheight i hi).1 hzim rows hrows hrow
    hgeo.2.1 hgeo.2.2.1 hgeo.2.2.2.1 hgeo.2.2.2.2.1 hgeo.2.2.2.2.2 hbase
    Cs K C0 hCs.le hK hC0 (by
      dsimp only
      intro J bin hne
      simpa only [add_assoc] using (hcounts (Finset.univ\J) bin hne).2.2) hscalar' hupper'

end WeightedQRH.Numerator
end
