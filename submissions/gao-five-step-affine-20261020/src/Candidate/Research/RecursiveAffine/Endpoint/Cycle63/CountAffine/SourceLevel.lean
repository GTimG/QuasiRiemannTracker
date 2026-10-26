/- Source batches, source moment contract and source-parameter count at the cutoff `cutoffA`.
Adapted from Collet's Cycle25 source layer and the detector-affine submission of DaysSky
(both Apache-2.0). Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
import Candidate.Cycle25.Assembly.Count.SourceBatch
import Candidate.Cycle25.Assembly.Count.Endpoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorBudget
import Candidate.Research.RecursiveAffine.Endpoint.Cycle25.Assembly.Count.Parameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_CountAffine_SourceLevel : Cycle63.AffineLedger := Cycle153.Root.rootLedger


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.Cycle153EndpointWeightedHighRowFamily
open OAI.SevenEighths.Cycle25WeightedHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance sourceLevelFinite : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The source amplitude batches at the cutoff `cutoffA`. -/
theorem actual_source_amplitude_batchesA (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth κplain : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hkplain : 7/10≤κplain) (hkplain1 : κplain≤3/4) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠ Z : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤7/8 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0<ell j) → (∀j,ell j≤dmin*mesh) → (7/37)*dmax≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
      W upper (fun j=>ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=>ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=>ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (Cycle153EndpointAffineCount.cutoffA (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=>ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
    W upper (fun j=>ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=>ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=>ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hqb := HeckeDetectorAmplitudeFirst.classMean_bounds rows Finset.univ (Z^d) (2*a-1)
    binWidth hb (fun j=>ell j/d) Q bin (by linarith)
    (fun j _=>(div_pos (hell j) (by linarith : 0<d)).le)
    (by rw [←Finset.sum_div]; exact div_pos (by nlinarith) (by linarith)) hne'
  have hdelta : 0<2*a-1 := by linarith
  have hcut := Cycle153EndpointAffineCount.cutoffA_bounds (δ:=2*a-1) (p:=q/(2*a-1)) (κ:=κplain)
    hdelta.le (by linarith) (div_nonneg hqb.1 hdelta.le)
    ((div_le_iff₀ hdelta).mpr (by linarith [hqb.2])) hkplain hkplain1
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=>hcal u (hsub hu)) (fun u hu=>hrow u (hsub hu)) a i hi ha (by linarith)
      (fun u hu=>hnext u (hsub hu)) (fun u hu=>hcurrent u (hsub hu))
      (Cycle153EndpointAffineCount.cutoffA (2*a-1) (q/(2*a-1)) κplain) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=>ell j/d) Q bin u hu'

end SevenEighths.Cycle153EndpointWeightedHighRowFamily

namespace SevenEighths.Cycle153EndpointProbeHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance sourceLevelFinite2 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The source fiber moments at the cutoff `cutoffA`: Collet's moments and the affine
marked plain moment, on every fiber of every source batch. -/
def SourceMomentsAtA {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (κplain c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (Cycle153EndpointAffineCount.cutoffA (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm ∧
      Cycle153EndpointDetectorRawFiber.AffineMarkedMoment (B.fiber bin j J K hne) C height εm

end SevenEighths.Cycle153EndpointProbeHighRowFamily

namespace SevenEighths.Cycle153EndpointProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open Cycle153EndpointProbeHighRowFamily
open ProbeHighRowFamily

/-- The source-parameter count at `cutoffA`, from the `affine` field of the count parameters. -/
theorem balanced_source_count_affine
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (εm : ℝ) (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth)
    (counts : Cycle153EndpointProbeHighRowFamily.CountParameters M H εm) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε κplain ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → 2*a-1≤3/4 → a≤1 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/100 → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (Cycle153EndpointAffineCount.cutoffA (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain counts.c counts.k
          (C*Z^momentCost) (Z^heightCost) εm) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle153EndpointDetectorRawFiber.AffineMarkedMoment (B.fiber bin j J K hne) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*
        (Z^d)^(Cycle153Endpoint.Arithmetic.Bernstein.countingR κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.affine
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε κplain ν C q i hi ha haδ ha' hε hε' hk hk1 hν hν1 hC Slot B hslots hbin hne hq hmom haff
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) κplain ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hk hk1 hν hν1 (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom haff
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (Cycle153EndpointAffineCount.cutoffA (2*a-1) (q/(2*a-1)) κplain) (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

end SevenEighths.Cycle153EndpointProbeFinalAssembly
end
end OAI
