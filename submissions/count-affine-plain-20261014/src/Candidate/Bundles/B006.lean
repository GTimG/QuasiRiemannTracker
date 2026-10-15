/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B005
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.State
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RelativeCapacityRemoval
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedEnergy

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorEnergyInitialState; sha256 bbd21e169c322784e435cf00e3d900d514618266c89cae982b5ad958e1220ba1 -/
section
                                                                     
                                                                        
                                               
                                                                   
                                                                          
                                                                         
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorEnergyInitialState Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open Cycle25CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def weighted_initialKeep (η:Character)(Q:Ideal O)(z:O):Prop:=
  z≠0 ∧ ¬FixedInducingRow η Q (fixedBadMask*idealGenerator 1) 1 z

def weighted_initialState (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1 ≤ U)(hδ:0 ≤ δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0 ≤ (Φ x).re)(hη:(η.modulus.absNorm:ℝ) ≤ U^δ):NaturalState U 0 bΦ where
  character:=η
  fixedModulus:=Q
  puncture:=1
  radial := {
    keep := weighted_initialKeep η Q
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth:=1
  characterWidth:=δ
  base_ge_one:=hU
  row_nonneg:=by norm_num
  character_nonneg:=hδ
  scale_eq:=by simp
  modulus_bound:=hη
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=hs
  row_ne_zero:=fun _ h=>h.1
  nonexceptional:=fun _ h=>h.2

lemma weighted_initialState_width (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1 ≤ U)(hδ:0 ≤ δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0 ≤ (Φ x).re)(hη:(η.modulus.absNorm:ℝ) ≤ U^δ):
    (weighted_initialState η Q Φ bΦ U δ hU hδ hs hp hη).width=1+δ:=rfl

def weighted_detectorProfiles (reverse:Bool)(j k:ℕ)(σ t:ℝ):Profiles (1/4) (9/4) where
  profile:=fun n=>detectorSchwartz reverse (if n=0 then j else k) σ t
  support:=by
    intro n x hx
    have he:(detectorSchwartz reverse (if n=0 then j else k) σ t:ℝ→ℂ)=
      HeckeInverseAmplification.twistProfile
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          ((HeckeDetectorRowwisePolynomial.logProfile^[if n=0 then j else k])
            HeckeDetectorDyadicProfiles.positiveAnnular)) σ
          (HeckeDetectorCoefficientTransfer.orientedFrequency reverse t):=by
      funext y;exact detectorSchwartz_apply _ _ _ _ _
    rw [he] at hx
    exact detector_profile_support _ _ _ _ hx

theorem weighted_radialMajorant_support_bound:
    ∃bΦ:ℝ,0<bΦ ∧ Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ:=by
  obtain ⟨b,hb⟩:=radialMajorant_compact.isCompact.bddAbove
  refine ⟨max 1 b,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)

variable {D:Cycle25.Weighted.MomentData}

theorem weighted_source_label_modulus_eventually (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (η:Character)(δ:ℝ)(hδ:0<δ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d:ℝ,(1/200:ℝ) ≤ d→
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
         ≤ (Z^d)^δ:=by
  have hc:∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
         ≤ Z^((1/200)*δ):=by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro label d hd
  apply (hz label).trans
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right hd hδ.le)

lemma weighted_source_keep_iff (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character)(u:FreeRow):
    weighted_initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val↔¬weighted_sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma weighted_source_fixed_gates (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    internalQ (weighted_sourceFixedIdeal F) η≠0 ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ F.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ η.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)⟩

end SevenEighths.Cycle25CenteredMomentDetectorEnergyInitialState

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorEnergyInitialState -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainSlotProfile; sha256 03e71e4132a6213e5aa9d49e479e27c618992d7d60e697cf57cc46dbbb70b4b9 -/
section
                                                                   
                                                              
                                                                          
                                                                  
                                                             
                                                         
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.Cycle25CenteredMomentDetectorPlainSlotProfile
open CenteredMomentDetectorPlainSlotProfile Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary
open CenteredMomentRetainedEnergy
variable {D:Cycle25.Weighted.MomentData}

lemma weighted_conjugate_source_support (F:Cycle25ProbeFinalAssembly.WeightedSourceData D):
    Function.support (fun x=>conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)

end SevenEighths.Cycle25CenteredMomentDetectorPlainSlotProfile

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainSlotProfile -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainCapacity; sha256 570385c605b5b80f1abfcfe65a2b53a1f5ee07958367219c401d56037e24c350 -/
section
                                                                
                                                            
                                                                  
                                                                   
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.Cycle25CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainCapacity Cycle25ProbeFinalAssembly
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary Cycle25CenteredMomentDetectorPlainSlotProfile
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSlotProfile
local notation "O"=>HeckeFamily.O
variable {D:Cycle25.Weighted.MomentData}

theorem weighted_physical_annular_all (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η₀:Character)
    (P:ℝ)(hP:0<P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=>conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

end SevenEighths.Cycle25CenteredMomentDetectorPlainCapacity

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainCapacity -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainExceptional; sha256 52b57dd70e7c1c84a3b2885a5b0682faea409db2bbe9b8d5667c329897a312bf -/
section
                                                                   
                                                         
                                                                   
                                                                     
                                                                               
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainExceptional Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open Cycle25CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def weighted_retainedSourceEnergy (keep:O→Prop)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy keep (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

theorem weighted_retained_positive_energy_le_source
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0 ≤ (Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0<U)
    (hkeep:∀u∈F.rows,keep u.val):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2) ≤ 
      weighted_retainedSourceEnergy keep F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=>fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted keep Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      exact hkeep u hu) (fun z=>hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=>Subtype.val_injective hxy)]
    _ ≤ _:=div_le_div_of_nonneg_right hb ht.le

variable {D:Cycle25.Weighted.MomentData}

theorem weighted_source_fibers_eventually_retained (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        weighted_initialKeep η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (weighted_sourceExceptional S η₀))=∅:=by
  filter_upwards [weighted_eventually_source_no_exceptional S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      weighted_initialKeep η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) u.val:=by
    intro u hu
    apply (weighted_source_keep_iff S η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact ((weighted_source_keep_iff S η₀ u).mp (hk u hu)) hex

theorem weighted_source_batch_plain_retained (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2) ≤ 
        weighted_retainedSourceEnergy (weighted_initialKeep η₀ (internalQ (weighted_sourceFixedIdeal S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [weighted_source_fibers_eventually_retained S η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1) 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0<Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus ≤ Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
  have hη:∀s∈selected,∀I∈primePool S.modulus ⊤ (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((I.absNorm:ℝ)/((Z^d)^(F.widths s)))≠0→IsCoprime I η₀.modulus:=by
    intro s hs I hI hn
    change I∈primePool S.modulus ⊤ (B.upper s) ((Z^d)^(B.widths s)) at hI
    change B.profile s ((I.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hn
    rw [hwidth] at hI
    rw [hwidth,hprofile] at hn
    exact hcop label s d hd (fun x=>(S.w x:ℂ)) (B.upper s)
      (by
        intro x hx
        have hn:S.w x≠0:=by simpa using hx
        exact (S.support hn).1.le) I hI hn
  rw [fiber_plain_energy_eq F η₀ hdataF hMm hU selected j k σ t hη]
  exact weighted_retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end SevenEighths.Cycle25CenteredMomentDetectorPlainExceptional

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainExceptional -/
