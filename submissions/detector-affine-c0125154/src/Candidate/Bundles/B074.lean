/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B001
import Candidate.Bundles.B047
import Candidate.Bundles.B071
import Candidate.Bundles.B073
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorBatch
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceBatch
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSupportedWitness

/- BEGIN ORIGINAL Cycle61.Numerator.Source.Combined; sha256 395c46afda2043a460dd75ad8520a2c38100989befb2d753b86135b401839b34 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                       
                                          
                                     

noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein Cycle61.Numerator.Capacity Cycle61.Numerator.Fourth
open Cycle61.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle61DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem source_integrated_all_bands (D : BaselineData)
    (hgap : theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (bPhi mesh affineError : ℝ) (haff : 0<affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j ≤  mesh/200)
    (eps sigma : ℝ) (heps : 0<eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200) :
    ∃Jw : ℝ,0  ≤  Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  d0  ≤  d  →  d  ≤  dPlus  →  U=Z^d  → 
      ∀(η : Character) (x z : ℂ) (a height : ℝ),(51/100:ℝ)  ≤  a  →  a  ≤  7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0  ≤  height  →  |z.im|  ≤  height  → 
      ∀rows : Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)  ≤  rowNorm u ∧ rowNorm u  ≤  U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀J : Finset (Fin D.N),∀P : ∀i:J,sourcePrimePool F Z i.val,
        Function.Injective (fun i=>(P i).val))  → 
      (∀P : ∀i,sourcePrimePool F Z i,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i  →  IsCoprime P.val η.modulus)  → 
      (∀i P,P∈sourcePrimePool F Z i  →  (4:ℝ)  ≤  P.val.absNorm)  → 
      (∀i,∀P∈F.S,(P.absNorm:ℝ)  ≤  Z^(D.length i))  → 
      (∀i,sourcePrimePool F Z i)  → 
      ∀Cs K C0 : ℝ,0  ≤  Cs  →  1  ≤  K  →  1  ≤  C0  → 
      let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
        F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      (∀J : Finset (Fin D.N),∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
        let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
        let q := weightedMean Finset.univ (fun s=>D.length s/d)
          (maskedGain (Finset.univ\J) (binValue Finset.univ ((2*a-1)/2) D.t bin))
        rows'.Nonempty  →  (rows'.card:ℝ)  ≤  K*C0*Z^(3*D.t)*
          U^(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma))  → 
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖  ≤ 
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*
          U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  → 
      (∀u∈rows,∀s,‖Q u s‖  ≤  (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) F.W (Z^Cycle61.Arithmetic.y) x z‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^Jw*
          Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  obtain ⟨Jn,hJn,Cn,hCn,hn⟩ := source_integrated_amplitude_classes D hgap hbetatop hkap F hbeta
    bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine eps sigma heps hsigma hbudget hfine
  obtain ⟨Jo,hJo,Co,hCo,ho⟩ := old_source_integrated_amplitude_classes D hgap hbetatop hkap F hbeta
    eps sigma heps hsigma (by linarith [haff]) hfine
  refine ⟨Jn+Jo,add_nonneg hJn hJo,Cn+Co,add_pos hCn hCo,?_⟩
  filter_upwards [hn,ho] with U hn ho
  refine ⟨hn.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him rows hrows hrow
    hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0
  dsimp only
  intro hcount hscalar hupper
  by_cases hdn : dMinus≤d
  · have hh := hn.2 Z d hZ hdn hdmax hUZ η x z a height ha hatop hx hz hH him rows
      hrows hrow hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0 hcount hscalar hupper
    apply hh.trans
    gcongr <;> linarith
  · have hh := ho.2 Z d hZ hd (le_of_not_ge hdn) hUZ η x z a height ha hatop hx hz hH him rows
      hrows hrow hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0 hcount hscalar hupper
    apply hh.trans
    gcongr <;> linarith
end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.Combined -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.SlotWidths; sha256 06834a05c1ff19356870c584ff732efbd3201d82e20ba95a29218f2b00df3d86 -/
section
                                                         
namespace OAI.SevenEighths.Cycle25WeightedHighRowFamily
noncomputable section
open scoped BigOperators
lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin dmax mesh : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤d) (hdmax : d≤dmax)
    (hell : ∀j,0<ell j) (hsmall : ∀j,ell j≤dmin*mesh)
    (hsupply : (7/37)*dmax≤∑j,ell j) :
    (∀j,0<ell j/d) ∧ (∀j,ell j/d≤ mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0<d := hdmin.trans_le hd
  have hm : 0≤ mesh := by
    by_contra hn
    have hneg : mesh<0 := lt_of_not_ge hn
    have hsum : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hneg.le)
    have hmax : 0<dmax := hd0.trans_le hdmax
    nlinarith
  refine ⟨fun j=>div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div]
    apply (le_div_iff₀ hd0).mpr
    nlinarith
end
end OAI.SevenEighths.Cycle25WeightedHighRowFamily

end
/- END ORIGINAL Cycle25.Assembly.Count.SlotWidths -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.SourceBatch; sha256 1b046c8026aa4ee7458ac17ac5126501e829989e19a1d7d824c85ce209a110f3 -/
section
                                        
                                                       
                                                         
                                                                 

/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.Cycle25WeightedHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_source_batch (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀tstar : ℝ,1≤tstar → tstar≤3/2 →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0<ell j) → (∀j,ell j≤dmin*mesh) → (7/37)*dmax≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=>ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hmargin hbudget
  filter_upwards [hw,eventually_ge_atTop (1:ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u=>hnext u.val u.property) (fun u=>hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0,h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u∈rows) : rowNorm u≤Z^d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp,hwm,hsp⟩ := physical_slot_widths ell d dmin dmax mesh hdmin hd hd' hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z^d) a ε tstar (Z^τ)
    ((Z^d)^(τ/(2*dmax))) i (fun u hu=>w ⟨u,hu⟩) hnorm
    Finset.univ W upper (fun j=>ell j/d) z mesh binWidth hm hb (fun j _=>hwp j) (fun j _=>hwm j) hsp
  refine ⟨B,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro u hu j
  dsimp [B,retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]
end SevenEighths.Cycle25WeightedHighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.SourceBatch -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.SourceAmplitudeClasses; sha256 12486589a4b78ee673e2e3a239b59f3ca3c316ed04f06d2a69cfdfb0a1d73ee2 -/
section
                                                                  
                                         
                                      
                                                               

/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.Cycle25WeightedHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_source_amplitude_batches (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth κplain : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hkplain : 7/10≤κplain) (hkplain1 : κplain≤3/4) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0<binWidth)
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
        (Z^d) a ε (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
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
  have hcut := Cycle25DetectorRowCount.cutoff_bounds (δ:=2*a-1) (p:=q/(2*a-1))
    hdelta.le (by linarith) (div_nonneg hqb.1 hdelta.le)
    ((div_le_iff₀ hdelta).mpr (by linarith [hqb.2])) hkplain hkplain1
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=>hcal u (hsub hu)) (fun u hu=>hrow u (hsub hu)) a i hi ha (by linarith)
      (fun u hu=>hnext u (hsub hu)) (fun u hu=>hcurrent u (hsub hu))
      (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=>ell j/d) Q bin u hu'
/-- The same batches at the region-aware cutoff `cutoffA`. -/
theorem actual_source_amplitude_batchesA (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth κplain : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hkplain : 7/10≤κplain) (hkplain1 : κplain≤3/4) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0<binWidth)
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
        (Z^d) a ε (DetectorAffineCount.cutoffA (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
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
  have hcut := DetectorAffineCount.cutoffA_bounds (δ:=2*a-1) (p:=q/(2*a-1))
    hdelta.le (by linarith) (div_nonneg hqb.1 hdelta.le)
    ((div_le_iff₀ hdelta).mpr (by linarith [hqb.2])) hkplain hkplain1
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=>hcal u (hsub hu)) (fun u hu=>hrow u (hsub hu)) a i hi ha (by linarith)
      (fun u hu=>hnext u (hsub hu)) (fun u hu=>hcurrent u (hsub hu))
      (DetectorAffineCount.cutoffA (2*a-1) (q/(2*a-1)) κplain) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=>ell j/d) Q bin u hu'
end SevenEighths.Cycle25WeightedHighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.SourceAmplitudeClasses -/
