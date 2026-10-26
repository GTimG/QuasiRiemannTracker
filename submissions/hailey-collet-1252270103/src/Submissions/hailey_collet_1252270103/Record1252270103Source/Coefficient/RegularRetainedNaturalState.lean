/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual second-row state admission uses Cycle61 and OpenAI/math geometry.
SecondInputDatum is only a geometric carrier: no ordinary block value or
ordinary column nonvanishing is required by these declarations. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondRowState

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentCommonRadialData
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open ActualEisensteinCubic CenteredMomentFirstAmplificationChoice CenteredMomentSecondRadicalBudget
open CenteredMomentSectorLocalization
open Cycle61FinalNatural Cycle61InitialMass
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

def enlargedRetainedPuncture (d : SecondInputDatum α) (second : Bool) (J : Ideal O) :
    Ideal O := (d.R * (if second then d.D else d.C)) * J

theorem enlarged_retained_puncture_ne (d : SecondInputDatum α) (second : Bool)
    (J : Ideal O) (hR : d.R ≠ 0) (hJ : J ≠ 0) :
    enlargedRetainedPuncture d second J ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero hR _) hJ
  cases second
  · exact d.hC.1
  · exact d.hD.1

/-- The extra puncture may vary with every retained row and Newton assignment. -/
def enlargedRetainedState (d : SecondInputDatum α) (second : Bool)
    (Z Bmask : ℝ) (hZ : 1 < Z) (ψ : RayCharacter) (Q J : Ideal O)
    (hR : d.R ≠ 0) (hJ : J ≠ 0)
    (hPN : ((enlargedRetainedPuncture d second J).absNorm : ℝ) ≤ Z ^ Bmask) :
    NaturalState Z Bmask 2 :=
  retainedState Z Bmask hZ (d.τ ψ) Q (enlargedRetainedPuncture d second J)
    (enlarged_retained_puncture_ne d second J hR hJ) hPN d.radius d.C d.D d.inactive

theorem enlarged_retained_state_fields (d : SecondInputDatum α) (second : Bool)
    (Z Bmask : ℝ) (hZ : 1 < Z) (ψ : RayCharacter) (Q J : Ideal O)
    (hR : d.R ≠ 0) (hJ : J ≠ 0)
    (hPN : ((enlargedRetainedPuncture d second J).absNorm : ℝ) ≤ Z ^ Bmask) :
    let st := enlargedRetainedState d second Z Bmask hZ ψ Q J hR hJ hPN
    st.character = d.τ ψ ∧ st.fixedModulus = Q ∧
      st.puncture = (d.R * (if second then d.D else d.C)) * J ∧
      st.mask = fixedBadMask * idealGenerator ((d.R * (if second then d.D else d.C)) * J) ∧
      st.width = Real.logb Z (retainedScale d.radius d.C d.D d.inactive) +
        Real.logb Z ((d.τ ψ).modulus.absNorm : ℝ) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Both reflected directions use the literal retained row, its original
nonexceptional filter and the same ball plateau. -/
theorem actual_enlarged_retained_state {Label : Type*} [Fintype Label]
    (d : Label → SecondInputDatum α) (r : secondLiveRows (fun l => (d l).block))
    (second : Bool) (Z Bmask : ℝ) (hZ : 1 < Z) (ψ : RayCharacter) (Q J : Ideal O)
    (hR : (d r.val.1).R ≠ 0) (hJ : J ≠ 0)
    (hPN : ((enlargedRetainedPuncture (d r.val.1) second J).absNorm : ℝ) ≤ Z ^ Bmask)
    (m : O) (hm : m ≠ 0) (hml : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (hkeep : CenteredMomentRestrictedEnergy.nonexceptional (d r.val.1).input.η ψ Q m
      (d r.val.1).block.frequency (if second then -r.val.2.2.2.val else r.val.2.2.2.val)) :
    let v := d r.val.1
    let st := enlargedRetainedState v second Z Bmask hZ ψ Q J hR hJ hPN
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    st.radial.keep z ∧
      1 ≤ (st.radial.profile (‖eisEmbedding z‖ ^ 2 / st.radial.scale)).re ∧
      st.radial.profile (‖eisEmbedding z‖ ^ 2 / st.radial.scale) ≠ 0 ∧
      st.width ≤ Real.logb Z v.radius + Real.logb Z (v.input.η.modulus.absNorm : ℝ) -
        Real.logb Z (normValue (commonFrequencyGenerator v.C v.D)) +
        Real.logb Z ((∏ p ∈ v.inactive, p.val).absNorm : ℝ) +
        Real.logb Z (4 * (fixedFactor : ℝ)) := by
  intro v st z
  let P := enlargedRetainedPuncture v second J
  have hP : P ≠ 0 := enlarged_retained_puncture_ne v second J hR hJ
  have hwidth := actual_second_live_state_width d r Z Bmask hZ ψ Q P hP hPN
  have hmajor := actual_second_live_state_majorant d r Z Bmask hZ ψ Q P hP hPN
  have hadmit : st.radial.keep z ∧
      st.radial.profile (‖eisEmbedding z‖ ^ 2 / st.radial.scale) ≠ 0 := by
    cases second
    · exact actual_second_live_state_admission d r Z Bmask hZ ψ Q P hP hPN m hm hml hm2 hkeep
    · exact actual_second_reflected_state_admission d r Z Bmask hZ ψ Q P hP hPN m hm hml hm2 hkeep
  refine ⟨hadmit.1, ?_, hadmit.2, hwidth⟩
  cases second
  · exact hmajor
  · change 1 ≤ (st.radial.profile (‖eisEmbedding (-r.val.2.2.2.val)‖ ^ 2 / st.radial.scale)).re
    rw [map_neg, norm_neg]
    exact hmajor

/-- Multiplication of the actual three puncture factors gives its polynomial cap. -/
theorem enlarged_retained_puncture_norm (d : SecondInputDatum α) (second : Bool)
    (J : Ideal O) (Z BR BC BJ : ℝ) (hZ : 0 < Z)
    (hR : (d.R.absNorm : ℝ) ≤ Z ^ BR)
    (hC : ((if second then d.D else d.C).absNorm : ℝ) ≤ Z ^ BC)
    (hJ : (J.absNorm : ℝ) ≤ Z ^ BJ) :
    ((enlargedRetainedPuncture d second J).absNorm : ℝ) ≤ Z ^ (BR + BC + BJ) := by
  unfold enlargedRetainedPuncture
  simp only [map_mul, Nat.cast_mul]
  rw [Real.rpow_add hZ, Real.rpow_add hZ]
  exact mul_le_mul (mul_le_mul hR hC (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _))
    hJ (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))

#print axioms enlargedRetainedPuncture
#print axioms enlarged_retained_puncture_ne
#print axioms enlargedRetainedState
#print axioms enlarged_retained_state_fields
#print axioms actual_enlarged_retained_state
#print axioms enlarged_retained_puncture_norm
end
end OAI.SevenEighths.Record1252270103Source
