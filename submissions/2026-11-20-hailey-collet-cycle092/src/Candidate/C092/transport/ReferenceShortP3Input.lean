/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual duplicated-slot Input for the short reference fourth. -/
import Candidate.C092.transport.ReferenceShortP3Rows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSecondHeightFamily
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentEnergyOriginalSource CenteredMomentUncenteredTerminal
open CenteredMomentDetectorPlainSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceInputTailUniform
local notation "O" => HeckeFamily.O

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (η : Character) (t : ℝ)
variable (pool : ι → Finset (Ideal O)) (ν : ι → Ideal O → ℂ)
variable (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ)
variable (hprime : ∀ i, ∀ I∈pool i, Prime I) (hP : ∀ i, 0 < P i)
variable (hM : ∀ i, 1 ≤ M i) (hν : ∀ i I, ‖ν i I‖ ≤ 1)
variable (hWslot : ∀ i, Function.support (Wslot i) ⊆ Set.Icc (1:ℝ) 2)
variable (hWbound : ∀ i x, ‖Wslot i x‖ ≤ M i)
variable (W : 𝓢(ℝ,ℂ)) (a b X : ℝ) (ha : 0 < a)
variable (hs : Function.support (W : ℝ→ℂ) ⊆ Set.Icc a b) (hX : 0 < X)

def fourthData : Data (Fin 2 × ι) where
  η := η
  m := fixedBadMask
  A := 1
  t := t
  slots := fun j => pool j.2
  prime := fun j => hprime j.2
  ν := fun j => ν j.2
  W := fun j => Wslot j.2
  lo := fun _ => 1
  hi := fun _ => 2
  P := fun j => P j.2
  lo_pos := fun _ => one_pos
  P_pos := fun j => hP j.2
  support := fun j => hWslot j.2
  W₁ := W
  W₂ := W
  X₁ := X
  X₂ := X
  Y₁ := comparisonScale b
  Y₂ := X*X/comparisonScale b
  M := fun j => M j.2
  M_ge_one := fun j => hM j.2
  coefficient_bound := by
    intro j I hI
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hν j.2 I)).trans (hWbound j.2 _)
  b₁ := b
  b₂ := b
  support₁ := fun _ hx => (hs hx).2
  support₂ := fun _ hx => (hs hx).2
  X₁_pos := hX
  X₂_pos := hX
  Y₁_pos := comparisonScale_pos b
  Y₂_pos := div_pos (mul_pos hX hX) (comparisonScale_pos b)
  same_product := comparison_product b (X*X)
  rows := ∅
  weight := fun _ => 0
  weight_nonneg := by simp

def fourthInput : Input (Fin 2 × ι) :=
  completeInput (fourthData η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X hs hX)
    (support_zero W a b ha hs) (support_zero W a b ha hs)
    (fun j => hν j.2) (fun j => hWbound j.2)
    1 2 one_pos (fun _ => le_rfl) (fun _ => le_rfl)

theorem fourthInput_volume :
    volume (fourthInput η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X ha hs hX).toData =
      X^2*(∏ i,P i)^2 := by
  simp only [volume,fourthInput,completeInput,fourthData,Fintype.prod_prod_type,
    Fin.prod_univ_two]
  ring

theorem fourthInput_plainControl :
    plainControl (fourthInput η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X ha hs hX) W W =
      (∏ i,M i)^2*(SchwartzMap.seminorm ℝ 0 0 W)^2 := by
  simp only [plainControl,fourthInput,completeInput,fourthData,Fintype.prod_prod_type,
    Fin.prod_univ_two]
  ring

#print axioms fourthInput
#print axioms fourthInput_volume
#print axioms fourthInput_plainControl
end
end QRH.Cycle092.ReferenceShortP3
