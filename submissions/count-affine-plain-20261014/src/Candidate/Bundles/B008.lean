/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B003
import Candidate.Bundles.B007
import OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
import OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedRestrictedField
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorBudget
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedRestrictedField; sha256 e83517d588c09275aa5432b5116004210ac73b96ba6dd22b4b9583e7a9f07f5d -/
section
                                                                                
                                                              
                                                                      
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25ProbeDetectorPlainUnmarkedRestrictedField
open ProbeDetectorPlainUnmarkedRestrictedField Cycle25ProbeFinalAssembly
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch Cycle25ProbeHighRowFamily
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open Cycle25CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open Cycle25CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound

open Cycle25ProbeDetectorPlainUnmarkedField
open ProbeDetectorPlainUnmarkedField

theorem weighted_source_batch_plain_unmarked (D:Cycle25.Weighted.MomentData)
    (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (weighted_sourceFixedIdeal S) η₀) (1/4) (9/4) weighted_radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ) ≤ d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0 ≤ height→∀j k:ℕ,j+k ≤ 2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value ≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value ≤ C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=>sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=>internalQ (weighted_sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=>henergy (η₀ label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0 ≤ ∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0<Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label ≤ Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0 ≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0<C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp ≤ C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ) ≤ d→
      ZeroAt (Q label) (1/4) (9/4) weighted_radialSupportUpper 0 1 2 (weighted_stageError D)
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [weighted_source_batch_plain_retained S η,weighted_source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1<Z^d:=weighted_source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖ ≤ height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(weighted_detectorProfiles F.reverse j k σ t).control control ^2 ≤ Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value ≤ weighted_retainedSourceEnergy (weighted_initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=weighted_retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+weighted_delta D+weighted_stageError D) ≤ 
      (Z^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (weighted_final_exponent_budget D _)
  have hfinal:value ≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _ ≤ (A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+D.t):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [weighted_unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.Cycle25ProbeDetectorPlainUnmarkedRestrictedField

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedRestrictedField -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.SourceParametersCount; sha256 d66b458cd29ff806f1e6079d28c157cf988bd4671d6ebf4fe28f3041f5925532 -/
section
                                                           
                                        
                                                                        

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open Cycle25ProbeHighRowFamily
open ProbeHighRowFamily

theorem balanced_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (_hH : RayOrthogonality.globalUnits M≤H) (_S : Finset (Ideal O))
    (φ : ℝ→ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ)
    (_hφp : tsupport φ⊆Ioi 0) (_hφ0 : ∀y,0≤φ y) (_hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (_ha₀ : 0<a₀) (_hab₀ : a₀≤b₀) (_hB₀ : 0<B₀)
    (_hφs : Function.support φ⊆Ioo a₀ b₀) (_hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (_hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) (counts : Cycle25ProbeHighRowFamily.CountParameters M H εm) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε κplain ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → 2*a-1≤3/4 → a≤1 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain counts.c counts.k (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(rowCount (2*a-1) (q/(2*a-1)) κplain+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.balanced
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε κplain ν C q i hi ha haδ ha' hε hε' hk hk1 hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) κplain ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hk hk1 hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.SourceParametersCount -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.SourceMomentInput; sha256 8746e9a4f08421c4f99308b01449ddb5b6f8b00f2587b487c0a0287f579f255b -/
section
                                                               
                                                   

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle25ProbeHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def SourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (κplain c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm

end SevenEighths.Cycle25ProbeHighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.SourceMomentInput -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentInput; sha256 40bc477e73c2151476ead10b86258d3264efd09e8bfb4a36f5cdef94de923559 -/
section
                                                                    
                                               
                                  
                                                             
                                                                   
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters Cycle25ProbeHighRowFamily
open HeckeInverseAmplification

def weighted_SourceMomentBound {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (κplain : ℝ) (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100<a → a ≤ 7/8 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im| ≤ height →
    Cycle25ProbeHighRowFamily.SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z κplain counts.c counts.k C height D.t

lemma weighted_SourceMomentBound.mono_constant {D : Cycle25.Weighted.MomentData}
    {F : WeightedSourceData D} {κplain : ℝ}
    {counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤Z) (h : weighted_SourceMomentBound F κplain counts η Z τ C height)
    (hC : C≤C') : weighted_SourceMomentBound F κplain counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots hwidth
    hprof hupp hext hmesh hbin hfam bin j J K hne
  have hm := h rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots
    hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  refine ⟨ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _) hm.original hC,?_⟩
  intro selected hsel hcap j k hj s hs t ht
  exact (hm.plain_marked selected hsel hcap j k hj s hs t ht).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentInput -/
