/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Generalizes the preserved Cycle25 source-amplitude batch construction only
in its cutoff. The original retained source detector family and rows persist. -/
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.SourceBatch
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.Endpoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators Topology
open Filter OAI OAI.SevenEighths
namespace QRH.Record1252270103Return.GenericCount
open ProbeHighRowFamily Cycle25WeightedHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_source_amplitude_batches_at_cutoff (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (cutoff : ℝ → ℝ → ℝ)
    (hcutoff : ∀ δ p : ℝ, 0 ≤ δ → δ ≤ 3/4 → 0 ≤ p → p ≤ 1/2 →
      1 ≤ cutoff δ p ∧ cutoff δ p ≤ 3/2)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0<margin) (hm : 0≤mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
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
        (Z^d) a ε (cutoff (2*a-1) (q/(2*a-1))) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
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
  have hcut := hcutoff (2*a-1) (q/(2*a-1))
    hdelta.le (by linarith) (div_nonneg hqb.1 hdelta.le)
    ((div_le_iff₀ hdelta).mpr (by linarith [hqb.2]))
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=>hcal u (hsub hu)) (fun u hu=>hrow u (hsub hu)) a i hi ha (by linarith)
      (fun u hu=>hnext u (hsub hu)) (fun u hu=>hcurrent u (hsub hu))
      (cutoff (2*a-1) (q/(2*a-1))) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=>ell j/d) Q bin u hu'
end QRH.Record1252270103Return.GenericCount

end


#print axioms QRH.Record1252270103Return.GenericCount.actual_source_amplitude_batches_at_cutoff
