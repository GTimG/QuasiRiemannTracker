/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B003
import Submissions.gao_cycle61_plane_20261013.Bundles.B006
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorPlainMarkedFineField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMomentParameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainUnmarkedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersHighDataFine

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainMarkedState; sha256 b16175cfc16bdf30acc9abe2ff09db6709de71516f2dddb8c12a625202c42958 -/
section
                                                                   
                                                            
                                                                       
                                                                
                                               
                                                            
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainMarkedState Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary Cycle25CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainStateDictionary CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource Cycle25CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainCapacity
open Cycle25CenteredMomentDetectorPlainSlotProfile Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainSlotProfile CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {D:Cycle25.Weighted.MomentData}

theorem weighted_source_slot_coefficient (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(η:Character)(s:Slot)
    (hreal:(F.external s).re=17/50)(hU:0<U)(I:Ideal O):
    idealCoeff η.inverse I*slotWindow F s ((I.absNorm:ℝ)/(U^(F.widths s)))=
      idealCoeff η.inverse I*annularWeight (fun x=>conj (S.W x))
        (U^(F.widths s)) (33/50) (-(F.external s).im) I := by
  have he:=weighted_physical_annular_all S η (U^(F.widths s)) (Real.rpow_pos_of_pos hU _)
    (F.external s) I
  rw [hreal] at he
  norm_num at he
  simpa only [physicalSlotCoefficient,slotWindow,hprofile] using he

theorem weighted_retained_eq_initial_energy (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(hupper:∀s,F.upper s=2)
    (η:Character)(Q:Ideal O)(selected:Finset Slot)
    (hreal:∀s∈selected,(F.external s).re=17/50)
    (Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)(hU:1 ≤ U)(hδ:0 ≤ δ)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0 ≤ (Φ x).re)
    (hη:(η.modulus.absNorm:ℝ) ≤ U^δ)(j k:ℕ)(σ t:ℝ):
    let state:=weighted_initialState η Q Φ bΦ U δ hU hδ hs hp hη
    weighted_retainedSourceEnergy state.radial.keep F η selected j k σ t Φ=
      energy state.character state.mask 1 0
        ((weighted_detectorProfiles F.reverse j k σ t).profile 0)
        ((weighted_detectorProfiles F.reverse j k σ t).profile 1)
        (fun s:selected=>CenteredMomentPrimeSlot.primePool M H 2 (U^(F.widths s.val)))
        (fun (s:selected) I=>idealCoeff η.inverse I*
          annularWeight (fun x=>conj (S.W x)) (U^(F.widths s.val)) (33/50)
            (-(F.external s.val).im) I)
        (fun s:selected=>U^(F.widths s.val)) (U^F.m) (U^F.m)
        state.radial.keep state.radial.profile state.radial.scale := by
  dsimp only
  change retainedSourceEnergy _ F η selected j k σ t Φ = _
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  have hc:(fun (s:selected) I=>idealCoeff η.inverse I*
      slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))=
      (fun (s:selected) I=>idealCoeff η.inverse I*
        annularWeight (fun x=>conj (S.W x)) (U^(F.widths s.val)) (33/50)
          (-(F.external s.val).im) I):=by
    funext s I
    exact weighted_source_slot_coefficient S F hprofile η s.val (hreal s.val s.property)
      (zero_lt_one.trans_le hU) I
  rw [hc]
  simp only [hupper,plainProfile_eq_detectorSchwartz,weighted_initialState,NaturalState.mask,
    weighted_detectorProfiles,reduceIte,Fin.one_eq_zero_iff]
  norm_num

theorem weighted_plain_length_eq [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1<U):
    length U (U^F.m)=F.m := by
  have hm:0 ≤ F.m:=(F.lengths hU).2.2.2.2
  rw [length,max_eq_right (Real.one_le_rpow hU.le hm),
    Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem weighted_marked_capacity [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1<U)
    (selected:Finset Slot)(κ δ:ℝ)(hδ:0 ≤ δ)
    (hcap:2*F.m+6*κ*(∑s∈selected,F.widths s) ≤ 1):
    length U (U^F.m)+length U (U^F.m)+6*κ*(∑s:selected,F.widths s.val) ≤ 1+δ := by
  rw [weighted_plain_length_eq F hU,Finset.sum_coe_sort]
  linarith

theorem weighted_source_batch_marked_initial (κplain:ℝ) (S:Cycle25ProbeFinalAssembly.WeightedSourceData D):
    ∃bΦ:ℝ,0<bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ) ≤ d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*κplain*(∑s∈selected,F.widths s) ≤ 1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (weighted_sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=weighted_initialKeep η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*κplain*(∑s:selected,F.widths s.val) ≤ state.width ∧
        (∀s:selected,0<F.widths s.val ∧ F.widths s.val ≤ F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2) ≤ 
          energy state.character state.mask 1 0
            ((weighted_detectorProfiles F.reverse j k σ t).profile 0)
            ((weighted_detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=>CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=>idealCoeff η₀.inverse I*
              annularWeight (fun x=>conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=weighted_radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [weighted_source_label_modulus_eventually S η δ hδ,weighted_source_batch_plain_retained S η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0<d:=by linarith
  have hU:1<Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ) ≤ (Z^d)^δ:=hz.2 label d hd
  let state:=weighted_initialState η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact weighted_marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=weighted_retained_eq_initial_energy S F hprof hupper η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) selected
      (fun s _=>hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end SevenEighths.Cycle25CenteredMomentDetectorPlainMarkedState

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainMarkedState -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainMomentParameters; sha256 f1c8b6c7a31d648d8cef660833b7fc85b9a4f4edf0087ddbe051e6fa321fd2e9 -/
section
                                                                        
                                                            
                                                                   
                                                                     
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainMomentParameters Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentDetectorEnergyInitialState Cycle25CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O


def weighted_delta (D:Cycle25.Weighted.MomentData):ℝ := D.t/4
def weighted_stageError (D:Cycle25.Weighted.MomentData):ℝ := D.t/4
def weighted_kappaPlain (_D:Cycle25.Weighted.MomentData):ℝ := 3/4

theorem weighted_fixed_parameters (D:Cycle25.Weighted.MomentData):
    0<weighted_delta D ∧ weighted_delta D ≤ 1/4 ∧ 0<weighted_stageError D ∧
    weighted_delta D+weighted_stageError D ≤ D.t ∧ 3/4 ≤ weighted_kappaPlain D ∧ 0<weighted_kappaPlain D := by
  dsimp [weighted_delta,weighted_stageError,weighted_kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma weighted_source_base_gt_one (_D:Cycle25.Weighted.MomentData)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ) ≤ d):1<Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma weighted_witness_length_cap (D:Cycle25.Weighted.MomentData):
    1/2+75*D.ε ≤ (23/40:ℝ) := by linarith [D.epsilon_small]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem weighted_actual_fiber_lengths (D:Cycle25.Weighted.MomentData)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1<U):
    0 ≤ F.m ∧ F.m ≤ 1/2+75*D.ε ∧ F.m ≤ 23/40 ∧
    1 ≤ U^F.m ∧ U^F.m ≤ U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (weighted_witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m ≤ 1 by linarith)
  · exact weighted_plain_length_eq F hU

lemma weighted_width_bands (D:Cycle25.Weighted.MomentData)(m:ℝ)(hm:m ≤ 23/40):
    1 ≤ 1+weighted_delta D ∧ 1+weighted_delta D ≤ 2 ∧
    1 ≤ max 1 (2*m)+weighted_delta D ∧ max 1 (2*m)+weighted_delta D ≤ 2 := by
  have hδ:0<weighted_delta D:=(weighted_fixed_parameters D).1
  have hd:weighted_delta D ≤ 1/4:=(weighted_fixed_parameters D).2.1
  have hmax:max 1 (2*m) ≤ 23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem weighted_unmarked_state_admission (D:Cycle25.Weighted.MomentData)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1<U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0 ≤ (Φ x).re)
    (hη:(η.modulus.absNorm:ℝ) ≤ U^(weighted_delta D)):
    let s:=state F η Q Φ bΦ (weighted_delta D) hU.le (weighted_fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=weighted_initialKeep η Q ∧
    s.width=max 1 (2*F.m)+weighted_delta D ∧ 1 ≤ s.width ∧ s.width ≤ 2 ∧
    1 ≤ U^F.m ∧ U^F.m ≤ U ∧ 2*length U (U^F.m) ≤ s.width := by
  dsimp only
  have hf:=weighted_actual_fiber_lengths D F hU
  have hw:=weighted_width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (weighted_delta D) hU.le (weighted_fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+weighted_delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (weighted_fixed_parameters D).1.le)

theorem weighted_source_label_fixed_allowance (D:Cycle25.Weighted.MomentData)
    (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ) ≤ d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
         ≤ (Z^d)^(weighted_delta D) :=
  weighted_source_label_modulus_eventually S η (weighted_delta D) (weighted_fixed_parameters D).1

lemma weighted_final_exponent_budget (D:Cycle25.Weighted.MomentData)(base:ℝ):
    base+weighted_delta D+weighted_stageError D ≤ base+D.t := by
  linarith [(weighted_fixed_parameters D).2.2.2.1]

end SevenEighths.Cycle25CenteredMomentDetectorPlainMomentParameters

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainMomentParameters -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainMarkedFineField; sha256 a36785ace0c72bd5d27f464306710cabe94a40c0c2a7c69a2d303ae5f5089de9 -/
section
                                                                        
                                                                 
                                                         
                                                                        
                                                                     
                                                                      
                                                               
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField
open ProbeDetectorPlainMarkedFineField Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly
open QuadraticInitialBound CenteredMomentDetectorDictionary
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentInductionEnergy
open Cycle25CenteredMomentDetectorEnergyInitialState Cycle25CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open Cycle25CenteredMomentDetectorPlainMomentParameters Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorPlainMomentParameters CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource

def weighted_PositiveFineSourceInput {D:Cycle25.Weighted.MomentData}(S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(κplain mesh:ℝ):Prop:=
  ∀bΦ:ℝ,0<bΦ→∃degree:ℕ,∃seminorms:Finset (ℕ×ℕ),
    ∀η₀:Character,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      PositiveAt (α:=Fin D.N) S.modulus ⊤ le_top (fun x=>conj (S.W x))
        2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 (weighted_stageError D)
        κplain U η₀ (weighted_sourceFixedIdeal S) degree seminorms C

theorem weighted_source_batch_plain_marked_fine {D:Cycle25.Weighted.MomentData}
    (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(κplain mesh:ℝ)(hmesh:0<mesh)(hfine:∀j,D.ell j ≤ mesh/200)
    (henergy:weighted_PositiveFineSourceInput S κplain mesh):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
    ∀d:ℝ,(1/200:ℝ) ≤ d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0 ≤ height→(∀s,|(B.external s).im| ≤ height)→
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots→
      2*F.m+6*κplain*(∑s∈selected,F.widths s) ≤ 1→
    ∀j k:ℕ,j+k ≤ 2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2) ≤ 
        (C*(1+height)^J)*(Z^d)^(1+D.t):=by
  obtain ⟨bΦ,hbΦ,hsource⟩:=weighted_source_batch_marked_initial κplain S
  obtain ⟨degree,seminorms,henergy⟩:=henergy bΦ hbΦ
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩:=
    CenteredMomentDetectorPlainProfileControl.source_height_factor seminorms
  refine ⟨J+degree,?_⟩
  intro η
  let data:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η
  choose C hC hbound using fun label=>henergy (data label)
  choose U₀ hU₀ using fun label=>Filter.eventually_atTop.mp (hbound label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0<Csum:=by
    have h:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label ≤ Csum:=by
    have h:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le)
      (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ) ≤ d→U₀ label ≤ Z^d:=by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  let Cfinal:=Csum*(1+diagonalControl radialMajorant)*Cprofile
  have hdiag:0 ≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  refine ⟨Cfinal,by dsimp [Cfinal];positivity,?_⟩
  filter_upwards [hsource η (weighted_delta D) (weighted_fixed_parameters D).1,hscale] with Z hs hscale
  refine ⟨hs.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal F selected hselected hcap j k hjk σ hσ t ht
  have hU:1<Z^d:=weighted_source_base_gt_one D Z d hs.1 hd
  obtain ⟨state,hchar,hQ,hpuncture,hΦ,hK,hkeep,hwidthstate,hcapacity,hwidths,hrow⟩:=
    hs.2 rows hrows d hd a D.ε tstar T allowance i B hB hdata hprof hwidth hupper hreal
      bin label left right hne selected hselected hcap
  have hf:=weighted_actual_fiber_lengths D F hU
  have hstate:state.width ≤ 2:=by rw [hwidthstate];exact (weighted_width_bands D F.m hf.2.2.1).2.1
  have hw (s:selected):0 ≤ F.widths s.val:=(hwidths s).1.le
  have hwcap (s:selected):F.widths s.val ≤ mesh:=by
    change B.widths s.val ≤ mesh
    rw [hwidth]
    apply (div_le_iff₀ (show 0<d by linarith)).mpr
    exact (hfine s.val).trans (by nlinarith)
  have hpos:=hU₀ label (Z^d) (hscale label d hd) selected (fun _=>1)
    (fun s=>F.widths s.val) (fun _=>(33/50:ℝ)) (fun s=>-(F.external s.val).im)
    0 height hw hwcap (fun _=>le_rfl) (fun _=>le_rfl) hheight
    (fun s=>by change |-(B.external s.val).im| ≤ height; simpa only [abs_neg] using hexternal s.val)
    state hQ hstate (weighted_detectorProfiles F.reverse j k σ t) ((Z^d)^F.m) ((Z^d)^F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1) hcapacity
  have heq:=CenteredMomentDetectorPlainRelativeClass.energy_eq S.modulus ⊤ le_top
    state.character (data label) (fun (_:selected)=>1) state.mask 1
    ((weighted_detectorProfiles F.reverse j k σ t).profile 0)
    ((weighted_detectorProfiles F.reverse j k σ t).profile 1)
    (fun _=>2) (fun s:selected=>(Z^d)^(F.widths s.val))
    (fun s I=>HeckePrimeAnnular.annularWeight (fun x=>conj (S.W x))
      ((Z^d)^(F.widths s.val)) (33/50) (-(F.external s.val).im) I)
    0 ((Z^d)^F.m) ((Z^d)^F.m) state.radial.keep state.radial.profile state.radial.scale
  have hnorm:=hprofile degree F.reverse j k hjk σ hσ height t hheight (abs_le.mpr ht)
  have hp:0 ≤ (weighted_detectorProfiles F.reverse j k σ t).control seminorms ^2:=sq_nonneg _
  have hexp:state.width+weighted_stageError D ≤ 1+D.t:=by
    rw [hwidthstate];linarith [(weighted_fixed_parameters D).2.2.2.1]
  calc
    _ ≤ _:=hrow j k σ t
    _ ≤ C label*diagonalControl state.radial.profile*
        (weighted_detectorProfiles F.reverse j k σ t).control seminorms ^2*
        (1+|(0:ℝ)|+height)^degree*(Z^d)^(state.width+weighted_stageError D):=by
      exact heq.le.trans hpos
    _ ≤ (Cfinal*(1+height)^(J+degree))*(Z^d)^(1+D.t):=by
      rw [hΦ]
      have hpow:=Real.rpow_le_rpow_of_exponent_le hU.le hexp
      calc
        _=(C label*diagonalControl radialMajorant)*
          ((weighted_detectorProfiles F.reverse j k σ t).control seminorms ^2*
            (1+|(0:ℝ)|+height)^degree)*(Z^d)^(state.width+weighted_stageError D):=by ring
        _ ≤ (Csum*(1+diagonalControl radialMajorant))*
          (Cprofile*(1+height)^(J+degree))*(Z^d)^(1+D.t):=by
          apply mul_le_mul _ hpow (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
          apply mul_le_mul _ hnorm (by positivity) (by positivity)
          exact mul_le_mul (hClabel label) (by linarith) hdiag hCsum.le
        _=_:=by dsimp [Cfinal];ring
end SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainMarkedFineField -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedField; sha256 7eee9d4bfc75a28c489a0c82661ed081a57f16167b28bd95a54926e83672034a -/
section
                                        
                                                                      
                                                                 
                                                                        
                                                                      
                                                               
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25ProbeDetectorPlainUnmarkedField
open ProbeDetectorPlainUnmarkedField Cycle25ProbeFinalAssembly
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
local notation "O" => HeckeFamily.O

def weighted_radialSupportUpper : ℝ := Classical.choose weighted_radialMajorant_support_bound

theorem weighted_radialSupportUpper_spec : 0<weighted_radialSupportUpper ∧
    Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic weighted_radialSupportUpper :=
  Classical.choose_spec weighted_radialMajorant_support_bound

lemma weighted_unmarked_power_eq (U m e:ℝ)(hU:1 ≤ U):
    U^(max 1 (2*m)+e)=max U ((U^m)^2)*U^e := by
  have hpos:0<U:=zero_lt_one.trans_le hU
  rw [Real.rpow_add hpos]
  congr 1
  have hs:(U^m)^2=U^(2*m):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hpos.le]
    congr 1
    norm_num
    ring
  rw [hs]
  by_cases hm:1 ≤ 2*m
  · rw [max_eq_right hm,max_eq_right]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm
  · have hm':2*m ≤ 1:=le_of_not_ge hm
    rw [max_eq_left hm',max_eq_left]
    · exact Real.rpow_one U
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm'


theorem weighted_retained_unmarked_bound (D:Cycle25.Weighted.MomentData)
    {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
    {U a tstar T heightAllowance:ℝ}{i:ℕ}
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(hU:1<U)
    (hη:(η.modulus.absNorm:ℝ) ≤ U^(weighted_delta D))
    (degree:ℕ)(S:Finset (ℕ×ℕ))(A:ℝ)
    (hzero:ZeroAt Q (1/4) (9/4) weighted_radialSupportUpper 0 1 2 (weighted_stageError D) U degree S A)
    (j k:ℕ)(σ t:ℝ):
    weighted_retainedSourceEnergy (weighted_initialKeep η Q) F η ∅ j k σ t radialMajorant  ≤ 
      A*diagonalControl radialMajorant*(weighted_detectorProfiles F.reverse j k σ t).control S ^2*
        U^(max 1 (2*F.m)+weighted_delta D+weighted_stageError D) := by
  let s:=state F η Q radialMajorant weighted_radialSupportUpper (weighted_delta D) hU.le
    (weighted_fixed_parameters D).1.le weighted_radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hs:=weighted_unmarked_state_admission D F η Q radialMajorant weighted_radialSupportUpper hU
    weighted_radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hwidth:s.width=max 1 (2*F.m)+weighted_delta D:=hs.2.2.2.2.2.2.1
  have hband:s.width ≤ 2:=hs.2.2.2.2.2.2.2.2.1
  have hscale:1 ≤ U^F.m ∧ U^F.m ≤ U:=⟨hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.1⟩
  have hz:=hzero s rfl hband (weighted_detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m)
    (zero_lt_one.trans_le hscale.1) (zero_lt_one.trans_le hscale.1)
    (by simpa only [Real.rpow_one] using hscale.2)
    (by simpa only [Real.rpow_one] using hscale.2)
  change retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t radialMajorant ≤ _
  rw [actual_source_eq F η Q radialMajorant weighted_radialSupportUpper (weighted_delta D) hU.le
    (weighted_fixed_parameters D).1.le weighted_radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t]
  have hrad:s.radial.profile=radialMajorant:=rfl
  simpa only [hwidth,hrad,norm_zero,add_zero,one_pow,mul_one, weighted_detectorProfiles, detectorProfiles] using hz

end SevenEighths.Cycle25ProbeDetectorPlainUnmarkedField

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedField -/
