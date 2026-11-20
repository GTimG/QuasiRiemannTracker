/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual finite ticket dictionary has two growing dyad coordinates.
Every other coordinate is fixed before the live source radius.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafWindows
import Candidate.C092.transport.StrongPairRegularTerminalFibers
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical
open Filter OAI OAI.SevenEighths HeckeFamily HeckeDetectorWitnessRows

theorem terminal_actual_key_card {Label : Type} [Fintype Label]
    (I K Je Jν : ℕ) (Z : ℝ) :
    Fintype.card (Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×Label×
      Fin (dyadicLength Z)×Fin (dyadicLength Z))=
      (I+1)*(K+1)*(Je*Jν)*Fintype.card Label*(dyadicLength Z)^2 := by
  simp only [Fintype.card_prod,Fintype.card_fin]
  ring

/-- The genuine full key costs only its two actual native dyads. Its
uniform radius threshold is valid for every later cofactor d in the bank. -/
theorem terminal_actual_key_budget {Label : Type} [Fintype Label]
    (I K Je Jν : ℕ) {dmin dmax loss : ℝ}
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hloss : 0<loss) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      (Fintype.card (Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×Label×
        Fin (dyadicLength (U^d))×Fin (dyadicLength (U^d))):ℝ) ≤ C*U^loss := by
  obtain ⟨C,hC,hbudget⟩ := StrongPair.terminal_dyad_budget hdmin hdmax hloss
  let fixed : ℝ := (I+1)*(K+1)*(Je*Jν)*Fintype.card Label
  refine ⟨fixed*C,mul_nonneg (by positivity) hC,?_⟩
  filter_upwards [hbudget] with U hU
  refine ⟨hU.1,?_⟩
  intro d hd hd'
  rw [terminal_actual_key_card]
  push_cast
  have hf : 0≤fixed := by dsimp [fixed];positivity
  have hb := mul_le_mul_of_nonneg_left (hU.2 d hd hd') hf
  convert hb using 1 <;> dsimp [fixed] <;> ring

#print axioms terminal_actual_key_card
#print axioms terminal_actual_key_budget
end
end QRH.Cycle092.RegularColoredForward
