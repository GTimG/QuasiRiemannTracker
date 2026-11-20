/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite authentic two-anchor energies. A common physical mark is represented
at each anchor by an exact norm equality, not by a new analytic bound. -/
import Candidate.C092.transport.StrongPairSmallSelect

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

/-- Exact finite deletion with its buffer/cardinality charge. All constants
precede the moving scale; no row gate is absorbed into a smooth profile. -/
theorem small_payment {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (J T : Finset Slot) (hTJ : T ⊆ J) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ)
    (mark : Slot→FreeRow→ℂ) (Cslot U e buffer V loss expo K : ℝ) (w : Slot→ℝ)
    (hU : 1 ≤ U) (hCslot : 0 ≤ Cslot) (hK : 0 ≤ K)
    (hlow : ∀ z∈s,∀ i∈J\T,‖mark i z‖^2 ≤ (Cslot*U^buffer)*U^(e*w i))
    (hretained : finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤ K*U^(V+loss))
    (hpaid : V+loss+buffer*((J\T).card:ℝ)+e*(∑ i∈J\T,w i) ≤ expo) :
    finiteEnergyOn J s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      ((max 1 Cslot)^(Fintype.card Slot)*K)*U^expo := by
  have hUp : 0<U:=zero_lt_one.trans_le hU
  have hdelete:=finite_delete_on J T hTJ s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark
    (Cslot*U^buffer) U e w hUp (by positivity) hlow
  have hpow : Cslot^(J\T).card ≤ (max 1 Cslot)^(Fintype.card Slot) :=
    (pow_le_pow_left₀ hCslot (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (Finset.card_le_univ _))
  calc
    _ ≤ ((Cslot*U^buffer)^(J\T).card*U^(e*∑ i∈J\T,w i))*(K*U^(V+loss)) :=
      hdelete.trans (mul_le_mul_of_nonneg_left hretained (by positivity))
    _ = (Cslot^(J\T).card*K)*U^(V+loss+buffer*((J\T).card:ℝ)+e*(∑ i∈J\T,w i)) := by
      rw [mul_pow,←Real.rpow_mul_natCast hUp.le]
      rw [Real.rpow_add hUp (V+loss+buffer*((J\T).card:ℝ)) (e*∑ i∈J\T,w i),
        Real.rpow_add hUp (V+loss) (buffer*((J\T).card:ℝ))]
      ring
    _ ≤ _ := by
      have hr:=Real.rpow_le_rpow_of_exponent_le hU hpaid
      gcongr

#print axioms small_payment
end
end QRH.Cycle092.StrongPair
