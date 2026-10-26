import Candidate.Target830.Physical.CountChoice
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
import Candidate.Cycle25.Assembly.Count.SourceBatch
import Candidate.Cycle25.Assembly.Count.Endpoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import Candidate.Affine.Balanced
import Candidate.Target830.Physical.MomentGates
import Candidate.Cycle63.Assembly.Count.ArithmeticIdentity
import Candidate.Cycle25.Assembly.Count.SourceAmplitudeClasses
import Candidate.Cycle25.Assembly.Count.SourceParametersCount
import Candidate.Cycle63.Assembly.Count.SourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
import Candidate.Cycle63.Assembly.Count.Errors
import Candidate.Target830.Count.Concrete
import Candidate.Target836.Detector836.Masked

/- Original module: Candidate.Target830.Physical.SourceBatches. -/
section

namespace OAI

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.Target830.Physical.SourceBatches
open ProbeHighRowFamily Cycle25WeightedHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The same batches at the region-aware cutoff `cutoffA`. -/
theorem actual_source_amplitude_batchesA (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth κplain : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hkplain : 7/10≤κplain) (hkplain1 : κplain≤ kappa0) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤7/8 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → (7/37)*dmax≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
      W upper (fun j=> ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (DetectorCount.cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
    W upper (fun j=> ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hqb := HeckeDetectorAmplitudeFirst.classMean_bounds rows Finset.univ (Z^d) (2*a-1)
    binWidth hb (fun j=> ell j/d) Q bin (by linarith)
    (fun j _=>(div_pos (hell j) (by linarith : 0< d)).le)
    (by rw [←Finset.sum_div]; exact div_pos (by nlinarith) (by linarith)) hne'
  have hdelta : 0<2*a-1 := by linarith
  have hcut := DetectorCount.cutoff_bounds (δ:=2*a-1) (p:=q/(2*a-1))
    hdelta.le (by linarith) (div_nonneg hqb.1 hdelta.le)
    ((div_le_iff₀ hdelta).mpr (by linarith [hqb.2])) hkplain hkplain1
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=> hcal u (hsub hu)) (fun u hu=> hrow u (hsub hu)) a i hi ha (by linarith)
      (fun u hu=> hnext u (hsub hu)) (fun u hu=> hcurrent u (hsub hu))
      (DetectorCount.cutoff (2*a-1) (q/(2*a-1)) κplain) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=> ell j/d) Q bin u hu'
end SevenEighths.Target830.Physical.SourceBatches

end

end OAI


#print axioms OAI.SevenEighths.Target830.Physical.SourceBatches.actual_source_amplitude_batchesA
end

/- Original module: Candidate.Target830.Physical.PhysicalSourceCount. -/
section
/- Actual fresh-D source/class count. Predecessor attribution retained. Apache-2.0. -/

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

theorem physical_source_amplitude_count (D : BaselineData) (F : SourceData) (hκold : D.momentKappa≤ kappa0)
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
      let Q := physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
        (fun _=>2) (fun j=> D.length j/d) (fun _=> z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=> D.length j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=> D.length j/d) bin
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
  let Q := physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
    (fun _=>2) (fun j=> D.length j/d) (fun _=> z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (fun j=> D.length j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=> D.length j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (Z^(d-D.t)+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hrows u hu).2.2.2]⟩
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hb d hd hd' (Z^(d-D.t)+1) rows (hne.mono hsub) hband
      (fun u hu=>(hrows u hu).2.2.1) (fun u hu=>(hrows u hu).2.2.2)
      a i hi ha (by linarith) hnext hcurrent D.N D.length D.slots_pos
      D.slots_small (by rw [D.slots_sum]; norm_num [ell,theta]) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun _=> z) bin hne
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
    (fun j=> D.length j/d) Q bin (by linarith)
    (fun j _=>(div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum]; exact div_pos (show (0:ℝ)< ell by norm_num [ell,theta]) hdpos) hne
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
end

/- Original module: Candidate.Target830.Physical.CanonicalCount. -/
section
/- Actual fresh-D source/class count. Predecessor attribution retained. Apache-2.0. -/

namespace OAI.SevenEighths.Target830.Physical
noncomputable section
set_option autoImplicit false
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection ProbeHighRowFamily

def canonicalFamily (D : BaselineData) (F : SourceData) (Z : ℝ) (z : ℂ) : FreeRow→Fin D.N→ℂ :=
  fun u j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
    (fun y=>(F.w y:ℂ)) 2 (Z^(D.length j)) z

theorem physical_eq_canonical (D : BaselineData) (F : SourceData) (Z d : ℝ)
    (hZ : 0< Z) (hd : d≠0) (z : ℂ) :
    physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=> D.length j/d) (fun _=> z) (Z^d) = canonicalFamily D F Z z := by
  funext u j
  exact source_physical_amplitude F.modulus ⊤ D.length (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j
end
end OAI.SevenEighths.Target830.Physical

#print axioms OAI.SevenEighths.Target830.Physical.physical_eq_canonical
end

/- Original module: Candidate.Target830.Physical.PublicCount. -/
section
/- Actual fresh-D source/class count. Predecessor attribution retained. Apache-2.0. -/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace OAI.SevenEighths.Target830.Physical
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
theorem canonical_source_count_with_error (D : BaselineData) (F : SourceData) (hκold : D.momentKappa≤ kappa0)
    (counts : DetectorCount.CountParameters F.modulus ⊤ D.t) (τ σ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) (herror : 159*D.ε+609*D.t≤σ) :
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
      let Q := canonicalFamily D F Z z
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=> D.length j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=> D.length j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*
          (Z^d)^(Count.count D.momentKappa (2*a-1) (q/(2*a-1))+σ) := by
  obtain ⟨C,hC,hcount⟩ := physical_source_amplitude_count D F hκold counts τ n hτ hτzero hτheight hτ2
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZp : 0< Z := zero_lt_one.trans hZ
  have hdp : 0< d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  rw [physical_eq_canonical D F Z d hZp hdp.ne'] at hb
  have hbound := hb bin hne
  refine ⟨hbound.1,hbound.2.1,?_⟩
  apply hbound.2.2.trans
  apply Cycle63DetectorCount.source_error_absorption Z d D.t D.ε _ σ (C*C0) hZ.le hd D.t_pos.le
  · exact mul_nonneg (by linarith) (by linarith)
  · exact herror

end OAI.SevenEighths.Target830.Physical
end

#print axioms OAI.SevenEighths.Target830.Physical.canonical_source_count_with_error
end

/- Original module: Candidate.Target830.Physical.MaskedCount. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical
noncomputable section
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open OAI.SevenEighths.Cycle25DetectorRowCount
open scoped Classical BigOperators
theorem masked_amplitude_class_count830 {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(Count.count κ δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ)+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(Count.count κ δ (q/δ)+loss) := by
  dsimp only
  have hg : ∀j∈slots,0 ≤ HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ∧
      HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j hj
    rw [←amplitude_class_value rows slots U (δ/2) mesh hm width Q bin u hu j hj]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width
    (HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin) δ hw hL hg
  refine ⟨hq0,hq.trans hqtop,?_⟩
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply Count.count_antitone hk hk1 hδ.le hδtop
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    have h' : HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin ≤ δ/2 := hqtop
    linarith


end
end OAI.SevenEighths.Target830.Physical
#print axioms OAI.SevenEighths.Target830.Physical.masked_amplitude_class_count830
end

/- Original module: Candidate.Target830.Physical.MaskedSourceCount. -/
section

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set
namespace OAI.SevenEighths.Target830.Physical.Source
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Physical
open Cycle25DetectorRowCount HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
theorem source_masked_count_with_error (D : BaselineData) (F : SourceData) (hκold : D.momentKappa≤ kappa0)
    (counts : DetectorCount.CountParameters F.modulus ⊤ D.t) (τ σ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) (herror : 159*D.ε+609*D.t≤ σ) :
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
      let Q := canonicalFamily D F Z z
      ∀main : Finset (Fin D.N),
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=> D.length j/d) Q bin
      let q := weightedMean Finset.univ (fun j=> D.length j/d) (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*
          (Z^d)^(Count.count D.momentKappa (2*a-1) (q/(2*a-1))+σ) := by
  obtain ⟨K,hK,hcount⟩ := canonical_source_count_with_error D F hκold counts τ σ n hτ hτzero hτheight hτ2 herror
  refine ⟨K,hK,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0< d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  have hcard := (hb bin hne).2.2
  have hm := masked_amplitude_class_count830 rows Finset.univ main
    (Z^d) (2*a-1) D.momentKappa D.t D.t_pos (fun j=> D.length j/d)
    (canonicalFamily D F Z z) bin (by linarith) (by linarith) D.momentKappa_lo D.momentKappa_hi
    (Real.one_le_rpow hZ.le hdpos.le) (fun j _=>(div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];exact div_pos (show (0:ℝ)< ell by norm_num [ell,theta]) hdpos)
    (K*C0) σ (by positivity) hne hcard
  exact hm


end OAI.SevenEighths.Target830.Physical.Source
end
#print axioms OAI.SevenEighths.Target830.Physical.Source.source_masked_count_with_error
end
