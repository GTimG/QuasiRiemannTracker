/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual original finite rows build the natural detector state at their true
radius, with padding equality transported explicitly. -/
import Candidate.C092.transport.RegularColoredTerminalLeafContext
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainFiberSource CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.P2CommonSourceMetadata
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafStateInput_89c26be7e6ba53e1_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem terminal_original_state_input (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (Bmask collar : ℝ) (hBmask : Bmask=0) (hc : 0 < collar) :
    ∀ᶠ U : ℝ in atTop,1 < U ∧ ∀(V Mcap : ℝ),0 ≤ V → V+collar ≤ Mcap →
    ∃s : NaturalState U Bmask A.bΦ,
      s.width ≤ Mcap ∧ s.character=A.ηShort ∧ s.puncture=1 ∧
      s.fixedModulus ≤ M ∧ s.fixedModulus ≤ A.baseShort.modulus ∧
      s.mask=fixedBadMask*idealGenerator 1 ∧
      (∀z : O,s.radial.keep z ↔ initialKeep s.character (internalQ A.QShort A.baseShort) z) ∧
      ∀rows : Finset FreeRow,
      (∀z∈rows,initialKeep A.ηShort (internalQ A.QShort A.baseShort) z.val) →
      (∀z∈rows,rowNorm z ≤ U^V) →
        (∀z∈rows,s.radial.keep z.val) ∧
        (∀z∈rows,s.radial.profile (‖eisEmbedding z.val‖^2/s.radial.scale)≠0) := by
  subst Bmask
  filter_upwards [TerminalActualRow.fixed_character_conductor A.ηShort hc] with U hU
  refine ⟨hU.1,?_⟩
  intro V Mcap hV hcap
  let s := TerminalActualRow.state A.ηShort (internalQ A.QShort A.baseShort) A.bΦ U V collar hU.1.le hV hc.le A.hΦ hU.2
  refine ⟨s,hcap,rfl,rfl,inf_le_left.trans A.hQSM,inf_le_right,rfl,(fun _=>Iff.rfl),?_⟩
  intro rows hk hr
  have hh (z : FreeRow) (hz : z∈rows) := TerminalActualRow.state_row_support A.ηShort
    (internalQ A.QShort A.baseShort) A.bΦ U V collar hU.1.le hV hc.le A.hΦ hU.2 z (hk z hz) (hr z hz)
  exact ⟨(fun z hz=>(hh z hz).1),(fun z hz=>by rw [(hh z hz).2];norm_num)⟩

#print axioms terminal_original_state_input
end
end QRH.Cycle092.RegularColoredForward
