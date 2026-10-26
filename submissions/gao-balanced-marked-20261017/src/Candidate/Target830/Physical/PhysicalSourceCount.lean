/- Actual fresh-D source/class count. Predecessor attribution retained. Apache-2.0. -/
import Candidate.Target830.Physical.MomentGates
import Candidate.Target830.Physical.SourceBatches
import Candidate.Cycle63.Assembly.Count.ArithmeticIdentity
import Candidate.Cycle25.Assembly.Count.SourceAmplitudeClasses
import Candidate.Cycle25.Assembly.Count.SourceParametersCount

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace OAI.SevenEighths.Target830.Physical
open Cycle25ProbeFinalAssembly Cycle25ProbeHighRowFamily Cycle25WeightedHighRowFamily
open ProbeFinalAssembly ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem physical_source_amplitude_count (D : BaselineData) (F : SourceData) (hκold : D.momentKappa≤kappa0)
    (counts : DetectorCount.CountParameters F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
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
      SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
        (fun _=>2) (fun j=>D.length j/d) (fun _=>z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*Z^(3*D.t)*
          (Z^d)^(Count.count D.momentKappa (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by
  obtain ⟨K,hK,hcount⟩ := SourceCount.balanced_source_count_affine F.modulus ⊤
    D.t (Sum Bool (RayQuotient.Characters F.modulus ⊤)) D.N n
    (1/200) (7/8) τ D.t (2*τ) D.t D.t
    (by norm_num) (by norm_num) hτ D.t_pos (by linarith) D.t_pos counts
  refine ⟨K+1,by linarith,?_⟩
  intro η
  have hbatches := SourceBatches.actual_source_amplitude_batchesA F.modulus ⊤ le_top F.S F.exclusions F.maximal η
    (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t D.t D.t D.momentKappa n
    (by norm_num) (by norm_num) D.momentKappa_lo hκold hτ hτzero hτheight
    D.epsilon_pos D.e_pos D.e_small D.witnessKappa_pos D.witnessKappa_small D.cost_pos.le
    D.t_pos D.t_pos.le D.t_pos (by nlinarith only [D.detector_budget])
  filter_upwards [hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hc hb hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  let Q := physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
    (fun _=>2) (fun j=>D.length j/d) (fun _=>z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (fun j=>D.length j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (Z^(d-D.t)+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hrows u hu).2.2.2]⟩
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hb d hd hd' (Z^(d-D.t)+1) rows (hne.mono hsub) hband
      (fun u hu=>(hrows u hu).2.2.1) (fun u hu=>(hrows u hu).2.2.2)
      a i hi ha (by linarith) hnext hcurrent D.N D.length D.slots_pos
      D.slots_small (by rw [D.slots_sum]; norm_num [ell,theta]) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun _=>z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=
      sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := (hmom rows d a hd hd' ha (by linarith) hrows i z hz hzim)
    q B hBsub hBd hRev hSlots hWidths hW hUpper hExternal hMesh hBin hBfam
  have hν1 : D.t ≤ 1/100000 := by linarith [D.t_small]
  have hcard := hc d hd hd' a D.ε D.momentKappa D.t C0 q i hi ha (by linarith) (by linarith)
    D.epsilon_pos.le D.epsilon_small D.momentKappa_lo hκold D.t_pos hν1 (by linarith)
    B (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean (fun bin j J K hne=>(hraw bin j J K hne).1)
    (fun bin j J K hne=>(hraw bin j J K hne).2)
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun j=>D.length j/d) Q bin (by linarith)
    (fun j _=>(div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum]; exact div_pos (show (0:ℝ)<ell by norm_num [ell,theta]) hdpos) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have he : Count.count D.momentKappa (2*a-1) (q/(2*a-1))+159*D.ε+D.t+D.t+7*D.t=Count.count D.momentKappa (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t) := by ring
  rw [he] at hcard
  apply hcard.trans
  have hC0pos : 0 ≤ C0 := by linarith
  have hcp : 0 ≤ (Z^d)^(Count.count D.momentKappa (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hcp
  apply mul_le_mul
  · nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  · positivity
  · positivity

end OAI.SevenEighths.Target830.Physical
end


#print axioms OAI.SevenEighths.Target830.Physical.physical_source_amplitude_count
