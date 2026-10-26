import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.MomentDetectorPlainExceptional
import Candidate.Cycle25.Assembly.SourceData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.MomentDetectorPlainMarkedState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainMarkedState Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary
open CenteredMomentDetectorPlainStateDictionary CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainSlotProfile CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {D:WeightedQRH.MomentData}

theorem weighted_source_batch_marked_initial (κplain:ℝ) (S:OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D):
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
        state.character=η₀ ∧ state.fixedModulus=internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_initialKeep η₀ (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*κplain*(∑s:selected,F.widths s.val) ≤ state.width ∧
        (∀s:selected,0<F.widths s.val ∧ F.widths s.val ≤ F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2) ≤ 
          energy state.character state.mask 1 0
            ((OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_detectorProfiles F.reverse j k σ t).profile 0)
            ((OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=>CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=>idealCoeff η₀.inverse I*
              annularWeight (fun x=>conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_label_modulus_eventually S η δ hδ,OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.weighted_source_batch_plain_retained S η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0<d:=by linarith
  have hU:1<Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ) ≤ (Z^d)^δ:=hz.2 label d hd
  let state:=OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_initialState η₀ (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState.weighted_marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState.weighted_retained_eq_initial_energy S F hprof hupper η₀ (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) η₀) selected
      (fun s _=>hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end SevenEighths.Cycle25CenteredMomentDetectorPlainMarkedState

end

end OAI
