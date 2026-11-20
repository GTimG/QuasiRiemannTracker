/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original calibrated maximum supplies a genuine finite inverse repetition
bank, with a fixed width floor before scale, arrays or attaining descriptors. -/
import Candidate.C092.transport.SourceInverseP6Bank
import Candidate.C092.transport.OriginalAttainingMark

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6Attaining_7ca3ea7be5111081_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_attaining_repeat_bank {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (b : ℝ) (hb : 0 < b) :
    let Kbig := ⌈(7/37 : ℝ)/b⌉₊+1
    ∃ F : ℝ,0 < F ∧ ∀ U pay : ℝ,1 < U → 1 ≤ pay → F*U^b ≤ pay →
    ∀ (η η₀ : Character) (z : O) (t : ℝ)
      (θ : ι→RayQuotient.Characters M H) (w v : ι→ℝ),
      (∀ j,0 ≤ w j) →
    let pools := originalPools M H 2 U w
    let coeff := originalCoefficients M H hH η₀ θ W U w (fun _ => (33/50:ℝ)) v
    let amp := fun j => ‖normalizedSlot η fixedBadMask 1 z (pools j) (coeff j) t (U^(w j))‖^2
    0 < response U pay w amp →
    ∀ (ρ : AnchorRect) (r ζ mesh : ℝ),367/500 ≤ r → 0 ≤ ζ →
      ρ.Admissible r (QRH.Cycle092.Source.inverseQuota r-ζ) 1 → (∀ j,w j ≤ mesh) →
    ∃ j : ι,b < w j ∧ amp j=pay*U^(response U pay w amp*w j) ∧
      U^(response U pay w amp*w j) ≤ amp j ∧ (7/37:ℝ) ≤ (Kbig:ℝ)*w j ∧
    ∃ selected : Finset (Fin Kbig),
      ρ.Admissible r ((selected.card:ℝ)*w j) 1 ∧
      QRH.Cycle092.Source.inverseQuota r-(ζ+mesh) < (selected.card:ℝ)*w j := by
  dsimp only
  obtain ⟨F,hF,hattain⟩ := QRH.Cycle092.AttainingMark.original_attaining_width (ι:=ι) M H hH W hW hWs
  refine ⟨F,hF,?_⟩
  intro U pay hU hpay hpay' η η₀ z t θ w v hw
  intro he ρ r ζ mesh hr hζ ha hmesh
  obtain ⟨j,hj,hamp⟩ := hattain U pay b hU hb.le hpay' η η₀ fixedBadMask 1 z t θ w
    (fun _ => (33/50:ℝ)) v hw (fun _ => by norm_num) he
  obtain ⟨hsupply,selected,hadm,hlower⟩ := QRH.Cycle092.MediumInversePrice.admitted_inverse_repeat_selection
    hr hζ ha hb hj.le (hmesh j)
  dsimp only at hamp
  refine ⟨j,hj,hamp,?_,hsupply,selected,hadm,hlower⟩
  rw [hamp]
  exact le_mul_of_one_le_left (Real.rpow_nonneg (zero_lt_one.trans hU).le _) hpay

#print axioms actual_attaining_repeat_bank
end
end QRH.Cycle092.SourceInverseP6
