/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual unchanged prime slots at the relative detector base, and the natural
state at the true sparse-row radius. -/
import Candidate.C092.transport.RegularColoredTerminalLeafAttainers
import Candidate.C092.transport.RegularColoredTerminalLeafSelection
import Candidate.C092.transport.TerminalActualRowState
import Candidate.C092.transport.StrongPairOrdinaryNearForward
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentWholeSlotDeletion CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional
open ConcretePrimeRowBridge ConcreteTraceCRT ProbeHighRowFamily
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOriginalScale_1d2a468592bb01b7_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The detector is opened at U^d with width w/d, while every prime scale,
pool, annular coefficient and literal slot remains the original one. -/
theorem terminal_relative_descriptor {Slot : Type} [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η base : Character) (W : ℝ→ℂ) (U d : ℝ) (hU : 0<U) (hd : 0<d)
    (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ) (hσ : ∀j,σ j=33/50)
    (t : ℝ) (z : FreeRow) (j : Slot) :
    descriptor M H hH η base W U θ w v t z j=
      normalizedSlot η (fixedBadMask*idealGenerator 1) 1 z.val
        (originalPools M H 2 (U^d) (fun j=>w j/d) j)
        (originalCoefficients M H hH base θ W (U^d) (fun j=>w j/d) σ v j) t
        ((U^d)^(w j/d)) := by
  rw [descriptor_short_anchor M H hH η base W U θ w σ v t z j (hσ j)]
  unfold originalPools QRH.Cycle092.WholeSlot.originalCoefficients
  rw [scale_rescale hU hd]

/-- The original physical response is unchanged by the relative-base
presentation. In particular zero-width slots are kept exactly. -/
theorem terminal_relative_response {Slot : Type} [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η base : Character) (W : ℝ→ℂ) (U d pay : ℝ) (hU : 0<U) (hd : 0<d)
    (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ) (hσ : ∀j,σ j=33/50)
    (t : ℝ) (z : FreeRow) (physical : Slot→ℂ)
    (hphysical : ∀j,‖physical j‖=‖descriptor M H hH η base W U θ w v t z j‖) :
    response U pay w (fun j=>‖physical j‖^2)=
      response U pay (fun j=>d*(w j/d)) (fun j=>‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 z.val
        (originalPools M H 2 (U^d) (fun j=>w j/d) j)
        (originalCoefficients M H hH base θ W (U^d) (fun j=>w j/d) σ v j) t
        ((U^d)^(w j/d))‖^2) := by
  have hw : (fun j=>d*(w j/d))=w := by funext j;field_simp
  rw [hw]
  exact response_norm_congr U pay w physical _ (fun j=>(hphysical j).trans
    (congrArg norm (terminal_relative_descriptor M H hH η base W U d hU hd θ w σ v hσ t z j)))

/-- The full common original mark product transports to the detector
base on the SAME finite sparse rows and selected original slots. -/
theorem terminal_relative_energy {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (ηLong ηShort baseShort : Character) (W : ℝ→ℂ) (U d : ℝ) (hU : 0<U) (hd : 0<d)
    (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ) (hσ : ∀j,σ j=33/50)
    (t : ℝ) (T : Finset Slot) (rows : Finset FreeRow) (physical : Slot→FreeRow→ℂ)
    (hphysical : ∀z∈rows,∀j∈T,‖physical j z‖=‖descriptor M H hH ηShort baseShort W U θ w v t z j‖)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ) :
    finiteEnergyOn T rows ηLong ηShort W₁ W₂ t₁ t₂ X₁ X₂ physical=
      finiteEnergyOn T rows ηLong ηShort W₁ W₂ t₁ t₂ X₁ X₂
        (fun j z=>normalizedSlot ηShort (fixedBadMask*idealGenerator 1) 1 z.val
          (originalPools M H 2 (U^d) (fun j=>w j/d) j)
          (originalCoefficients M H hH baseShort θ W (U^d) (fun j=>w j/d) σ v j) t
          ((U^d)^(w j/d))) := by
  exact finiteEnergyOn_norm_congr T rows ηLong ηShort W₁ W₂ t₁ t₂ X₁ X₂ physical _
    (fun z hz j hj=>(hphysical z hz j hj).trans (congrArg norm
      (terminal_relative_descriptor M H hH ηShort baseShort W U d hU hd θ w σ v hσ t z j)))

/-- Relative source widths reconstruct the original total and every
original finite subproduct exactly. -/
theorem terminal_relative_widths {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (w : Slot→ℝ) {d dmin mesh quota : ℝ} (hd : 0<d) (hdmin : dmin≤d)
    (hm : 0 ≤ mesh) (hw : ∀j,0≤w j) (hmesh : ∀j,w j≤dmin*mesh)
    (hquota : (∑j,w j)≤quota) :
    (∀j,0≤w j/d) ∧ (∀j,w j/d ≤ mesh) ∧ (∀j,d*(w j/d)=w j) ∧
      (∑j,d*(w j/d))≤quota ∧ (∀T : Finset Slot,(∑j∈T,w j)≤quota) := by
  have heq (j : Slot) : d*(w j/d)=w j := by field_simp
  refine ⟨(fun j=>div_nonneg (hw j) hd.le),(fun j=>?_),heq,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    calc
      w j ≤ dmin*mesh := hmesh j
      _ ≤ mesh*d := by nlinarith only [mul_le_mul_of_nonneg_right hdmin hm]
  · simpa only [heq] using hquota
  · intro T
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun j _ _=>hw j)).trans hquota

/-- One fixed-character event constructs the true radial state on every
later actual finite row set and every chosen conductor-bank member. -/
theorem terminal_original_state_event (η base : Character) (Q : Ideal O)
    (M : Ideal O) (hQM : Q≤M) (bΦ collar : ℝ) (hc : 0<collar)
    (hΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ) :
    ∀ᶠ U : ℝ in atTop,∃hU : 1<U,∃hmod : (η.modulus.absNorm:ℝ)≤U^collar,
    ∀V d : ℝ,∀hV : 0≤V,V+2*collar≤d →
    let s := TerminalActualRow.state η (internalQ Q base) bΦ U V collar hU.le hV hc.le hΦ hmod;
      s.width≤d-collar ∧ s.width+0+collar≤d ∧ s.character=η ∧
      s.fixedModulus≤M ∧ s.fixedModulus≤base.modulus ∧ s.puncture=1 ∧
      s.mask=fixedBadMask*idealGenerator 1 ∧
      (∀z : O,s.radial.keep z ↔ initialKeep η (internalQ Q base) z) ∧
      ∀rows : Finset FreeRow,(∀z∈rows,initialKeep η (internalQ Q base) z.val) →
        (∀z∈rows,rowNorm z≤U^V) →
        (∀z∈rows,s.radial.keep z.val) ∧
        (∀z∈rows,s.radial.profile (‖eisEmbedding z.val‖^2/s.radial.scale)≠0) ∧
        (∀z∈rows,rowNorm z≤U^d) := by
  filter_upwards [TerminalActualRow.fixed_character_conductor η hc] with U hU
  refine ⟨hU.1,hU.2,?_⟩
  intro V d hV hVd
  dsimp only
  refine ⟨by change V+collar≤d-collar;linarith,
    by change V+collar+0+collar≤d;linarith,rfl,inf_le_left.trans hQM,inf_le_right,rfl,rfl,
    (fun _=>Iff.rfl),?_⟩
  intro rows hkeep hrow
  have hsupport (z : FreeRow) (hz : z∈rows) := TerminalActualRow.state_row_support
    η (internalQ Q base) bΦ U V collar hU.1.le hV hc.le hΦ hU.2 z (hkeep z hz) (hrow z hz)
  exact ⟨(fun z hz=>(hsupport z hz).1),(fun z hz=>by rw [(hsupport z hz).2];norm_num),
    (fun z hz=>(hrow z hz).trans (Real.rpow_le_rpow_of_exponent_le hU.1.le (by linarith)))⟩

#print axioms terminal_relative_response
#print axioms terminal_relative_energy
#print axioms terminal_relative_descriptor
#print axioms terminal_relative_widths
#print axioms terminal_original_state_event
end
end QRH.Cycle092.RegularColoredForward
