import WeightedQRH.HighRows.MaskedCount
import WeightedQRH.HighRows.SourceAmplitudeClasses
import WeightedQRH.HighRows.HighData
import WeightedQRH.MomentSourceMoments
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceCount

/-! Source specialization of the original certified amplitude-class row count.
This stops before any physical numerator estimate. -/
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace OAI.SevenEighths.WeightedHighFinalAssembly
open ProbeFinalAssembly ProbeHighRowFamily WeightedHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem weighted_source_amplitude_count {Δ : ℝ}
    (D : WeightedQRH.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      weighted_SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
        (fun _=>2) (fun j=>D.ell j/d) (fun _=>z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.ell j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*Z^(3*D.t)*
          (Z^d)^(WeightedQRH.rowCount (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by
  obtain ⟨K,hK,hcount⟩ := adaptive_source_count_from_raw_moments F.modulus ⊤ le_top F.S
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t_pos (Sum Bool (RayQuotient.Characters F.modulus ⊤)) D.N n
    (1/200) (7/8) τ D.t (2*τ) D.t D.t
    (by norm_num) (by norm_num) hτ D.t_pos (by linarith) D.t_pos counts
  refine ⟨K+1,by linarith,?_⟩
  intro η
  have hbatches := WeightedHighRowFamily.actual_source_amplitude_batches F.modulus ⊤ le_top F.S F.exclusions F.maximal η
    (1/200) (7/8) τ D.ε D.e D.κ D.cost D.t D.t D.t n
    (by norm_num) (by norm_num) (by norm_num) hτ hτzero hτheight
    D.epsilon_pos D.e_pos D.e_small D.kappa_pos D.kappa_small D.cost_pos.le
    D.t_pos D.t_pos.le D.t_pos (by nlinarith only [D.detector_budget])
  filter_upwards [hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hc hb hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  let Q := physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
    (fun _=>2) (fun j=>D.ell j/d) (fun _=>z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (fun j=>D.ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (Z^(d-D.t)+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hrows u hu).2.2.2]⟩
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hb d hd hd' (Z^(d-D.t)+1) rows (hne.mono hsub) hband
      (fun u hu=>(hrows u hu).2.2.1) (fun u hu=>(hrows u hu).2.2.2)
      a i hi ha (by linarith) hnext hcurrent D.N D.ell (fun j=>(D.slots_bounds j).1)
      (fun j=>(D.slots_bounds j).2.2) D.slots_sum (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun _=>z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=
      sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := (hmom rows d a hd hd' ha (by linarith) hrows i z hz hzim)
    q B hBsub hBd hRev hSlots hWidths hW hUpper hExternal hMesh hBin hBfam
  have hcard := hc d hd hd' a D.ε 0 D.t C0 q i hi ha (by linarith)
    D.epsilon_pos.le D.epsilon_small (by norm_num) (by norm_num) D.t_pos (by linarith)
    B (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun j=>D.ell j/d) Q bin (by linarith)
    (fun j _=>(div_pos (D.slots_bounds j).1 hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];positivity) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  rw [WeightedQRH.adaptive_count_identity (by linarith : 0 < 2*a-1)
    (by linarith : 2*a-1 ≤ 3/4) hqb.1 hqb.2] at hcard
  have he : 159*D.ε+D.t+D.t+7*D.t=159*D.ε+9*D.t := by ring
  rw [he] at hcard
  apply hcard.trans
  have hC0pos : 0 ≤ C0 := by linarith
  have hcp : 0 ≤ (Z^d)^(WeightedQRH.rowCount (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hcp
  apply mul_le_mul
  · nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  · positivity
  · positivity

end OAI.SevenEighths.WeightedHighFinalAssembly
end
