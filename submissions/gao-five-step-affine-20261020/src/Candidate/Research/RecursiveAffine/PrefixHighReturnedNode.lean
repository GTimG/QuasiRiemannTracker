/- Literal own-HIGH node of the recursive source tree. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PrefixHighSourceProducer
import Candidate.Research.RecursiveAffine.RegionalReturned

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RecursiveHighProvider
noncomputable section
open Cycle153HighProvider Cycle153SourceReturn
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open Cycle63Moment Cycle63Moment.LowBranch Cycle63InitialMass
open ConcretePrimeRowBridge CompletedGauss Cycle63FinalNatural
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot

variable {Base : Type} {base : Character → Base → Character}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable [Cycle63.AffineLedger]

/-- Apply the proved universal source producer at one actual physical node.
The hypotheses are its native source domain and literal accumulated-prefix
presentation. Neither a HIGH record nor a source energy bound is supplied
as input. The output is the actual record, payment, class cap and HIGH
source operator from the same existential witness. In particular the
record cannot be selected independently of its source coefficient.

`hgiven` is the uniform producer conclusion constructed by
`twoLevelHighProducer`, after its fixed source constants and threshold have
been chosen. It is not a premise asserting the desired returned count or
recursive parent energy bound. LOW descendants remain the caller's actual
finite source carriers. -/
theorem actual_prefix_high_returned_node
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule) (ap bp bΦ Bmask mesh ε τlow B lossNeeded : ℝ)
    (hap : 0<ap) (Ψ : 𝓢(ℝ,ℂ)) (SH : Finset (ℕ×ℕ)) (dh : ℕ) (Kclass Kh : ℝ)
    (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (Z : ℝ)
    (hgiven : DepthTwoHighGivenAt (base:=base) (α:=α) M H hH W hW hWs hβlo hβhi
      g ap bp bΦ Bmask mesh ε τlow B lossNeeded hap Ψ SH dh Kclass Kh η₀ Q hQM hQ72 Z)
    (hZ : 1<Z) (hT : 2<Z^g.τ) (T : Finset α)
    (θ : T→RayQuotient.Characters M H) (w σ freq : T→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50)) (t height : ℝ)
    (hw : ∀i,0 ≤ w i) (hmesh : ∀i,w i ≤ mesh)
    (hheight : 0 ≤ height) (hfreq : ∀i,|freq i| ≤ height)
    (state : NaturalState Z Bmask bΦ) (hfixed : state.fixedModulus=internalQ Q η₀)
    (hwidth : state.width ≤ 1) (p : Profiles ap bp)
    (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hwindow : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i))
    (v : O) (τT Tz : ℝ) (hτT : τlow ≤ τT)
    (hpresentation : PrefixHighPresented (base η₀) τT Z state v Tz)
    (hvbound : ((Ideal.span {v}).absNorm:ℝ) ≤ Z^(B-130))
    (len ampP loss : ℝ) :
    let s:=affineInput M H hH η₀ θ W hW.continuous 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p hap
      (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    let amp:=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i,w i)))
    ∀(hlen : Real.logb Z (CenteredMomentAmplificationChildInput.volume s) ≤ len)
      (hamp : amp ≤ ampP) (hloss : lossNeeded+ε ≤ loss),
    ∃ part : ReturnedPartAt M H hH Cycle63.AffineLedger.q
        (fun η=>extendFixedDictionary (base η)) η₀ Z B Tz v,
      part.scale=state.rowWidth ∧ part.length=len ∧ part.amp=ampP ∧ part.loss=loss ∧
      (∀b,(Fintype.card (part.record b).Class:ℝ) ≤ Kclass) ∧
      GeometryAffineHighGiven (α:=T) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT ap bp s p state.puncture 1
        state.rowWidth amp Ψ (profile_zero_of_pos p hap 0) (profile_zero_of_pos p hap 1) SH dh height
        (Kh*(Z^(-(state.rowWidth+3*g.δ-amp+ε))*part.value+1)) := by
  intro s amp hlen hamp hloss
  obtain ⟨unit,Hb,hpays,hcard,hphysical⟩ :=
    hgiven hZ hT T θ w σ freq hσ t height hw hmesh hheight hfreq state hfixed hwidth
      p X₁ X₂ hX₁ hX₂ hwindow v τT Tz hτT hpresentation hvbound len ampP loss hlen hamp hloss
  let part : ReturnedPartAt M H hH Cycle63.AffineLedger.q
      (fun η=>extendFixedDictionary (base η)) η₀ Z B Tz v :=
    { unit:=unit,record:=Hb,scale:=state.rowWidth,length:=len,amp:=ampP,loss:=loss,pays:=hpays }
  refine ⟨part,rfl,rfl,rfl,rfl,hcard,?_⟩
  exact hphysical

end
end OAI.SevenEighths.Cycle153RecursiveHighProvider
#print axioms OAI.SevenEighths.Cycle153RecursiveHighProvider.actual_prefix_high_returned_node
