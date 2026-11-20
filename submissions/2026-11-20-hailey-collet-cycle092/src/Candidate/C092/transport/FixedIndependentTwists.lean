/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Absorb each fixed ordinary-column ray weight into its own H8 character.
The inducing modulus is enlarged only by that fixed character's modulus. -/
import Candidate.C092.transport.FixedH8Squared
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedRayInducingTransport
set_option autoImplicit false
noncomputable section
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeRowClosure
open CenteredMomentFixedRayInducingTransport CenteredExceptionalProfile
namespace QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O

def FixedCubeDatum.twistColumn (D : FixedCubeDatum) (ω : Character) : FixedCubeDatum where
  η := D.η.product ω
  Q := D.Q ⊓ ω.modulus
  hQ := Ideal.inf_ne_bot_of_ne_bot D.hQ ω.modulus_ne_bot
  m := D.m
  A := D.A
  z := D.z
  hm := D.hm
  hA := D.hA
  hz := D.hz
  hml := D.hml
  hm2 := D.hm2
  fixed := by
    apply fixedInducingRow_product_of D.η ω _ D.m D.A D.z inf_le_right
    obtain ⟨χ,ψ,hprim,hinduces,hQ,hχ⟩ := D.fixed
    exact ⟨χ,ψ,hprim,hinduces,inf_le_left.trans hQ,hχ⟩

theorem actualCoefficient_twist (D : FixedCubeDatum) (ω : Character) (I : Ideal O) :
    (D.twistColumn ω).actualCoefficient I = idealCoeff ω I * D.actualCoefficient I := by
  unfold FixedCubeDatum.actualCoefficient; dsimp only [FixedCubeDatum.twistColumn]
  rw [idealCoeff_product]; ring

theorem independent_pair_coefficients (D₁ D₂ : FixedCubeDatum) (ω₁ ω₂ : Character) (I J : Ideal O) :
    (D₁.twistColumn ω₁).actualCoefficient I*(D₂.twistColumn ω₂).actualCoefficient J =
      (idealCoeff ω₁ I * idealCoeff ω₂ J)*(D₁.actualCoefficient I*D₂.actualCoefficient J) := by
  rw [actualCoefficient_twist,actualCoefficient_twist]; ring

theorem twist_conductor_le (D : FixedCubeDatum) (ω : Character) :
    rowConductorBound (D.twistColumn ω).η D.m 1 (D.A*D.z) ≤
      ω.modulus.absNorm*rowConductorBound D.η D.m 1 (D.A*D.z) := by
  change rowConductorBound (D.η.product ω) _ _ _ ≤ _
  unfold rowConductorBound
  have h := HeckePrimeScale.product_modulus_bound D.η ω
  calc
    _ ≤ D.η.modulus.absNorm*ω.modulus.absNorm*(Ideal.span {D.m}).absNorm*(Ideal.span {(72:O)}).absNorm*
        ((Ideal.span {(1:O)}).absNorm^4*(Ideal.span {D.A*D.z}).absNorm) := by gcongr
    _ = _ := by ring

theorem uniform_twist_conductor (ω : Character) (B δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ U : ℝ in atTop, 1 ≤ U ∧ ∀ D : FixedCubeDatum,
      (rowConductorBound D.η D.m 1 (D.A*D.z):ℝ) ≤ U^B →
      (rowConductorBound (D.twistColumn ω).η D.m 1 (D.A*D.z):ℝ) ≤ U^(B+δ) := by
  filter_upwards [(tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop (ω.modulus.absNorm:ℝ)),
    eventually_gt_atTop (1:ℝ)] with U hω hU
  refine ⟨hU.le,?_⟩
  intro D hD
  have h : (rowConductorBound (D.twistColumn ω).η D.m 1 (D.A*D.z):ℝ) ≤
      ω.modulus.absNorm*(rowConductorBound D.η D.m 1 (D.A*D.z):ℝ) := by exact_mod_cast twist_conductor_le D ω
  rw [Real.rpow_add (zero_lt_one.trans hU),mul_comm (U^B) (U^δ)]
  exact h.trans (mul_le_mul hω hD (Nat.cast_nonneg _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _).le)

#print axioms independent_pair_coefficients
#print axioms uniform_twist_conductor
end QRH.Cycle092.SignedCenter
