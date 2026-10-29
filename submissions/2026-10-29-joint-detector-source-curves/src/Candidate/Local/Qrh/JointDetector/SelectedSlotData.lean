/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.SelectedKernel

/-! Common ordinary-source slot data for the selected norm iteration.
The descriptor is finite after the original slot dictionary is supplied.
The analytic constants must be uniform in its bounded common masks.
-/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

structure SelectedSlotData (N : ℕ) where
  width : Fin N → ℝ
  energy : Fin N → ℝ
  sources : Fin N → Finset (Ideal O)
  coefficient : Fin N → Ideal O → ℂ

namespace SelectedSlotData
variable {N : ℕ}

def polynomial (d : SelectedSlotData N) (i : Fin N) (z : O) : ℂ :=
  ∑ I ∈ d.sources i, d.coefficient i I * idealRowHom z I

structure Bounded (d : SelectedSlotData N) (Z mesh C : ℝ) : Prop where
  width_nonneg : ∀ i, 0 ≤ d.width i
  width_le_mesh : ∀ i, d.width i ≤ mesh
  source_nonzero : ∀ i, ∀ I ∈ d.sources i, I ≠ 0
  source_norm : ∀ i, ∀ I ∈ d.sources i, (Ideal.absNorm I:ℝ) ≤ 2*Z^(d.width i)
  coefficient_mass : ∀ i, (∑ I ∈ d.sources i, ‖d.coefficient i I‖^2) ≤ C

/-- This is a fixed common individual-amplitude cell, chosen before the
ordinary source variable. It contains no operator-norm assertion. -/
def Selects (d : SelectedSlotData N) (Z : ℝ) (rows : Finset O) : Prop :=
  ∀ z ∈ rows, ∀ i, Z^(d.energy i) ≤ ‖d.polynomial i z‖^2

def HasSlope (d : SelectedSlotData N) (δ : ℝ) : Prop :=
  δ*(∑ i, d.width i) ≤ ∑ i, d.energy i

def mask (d : SelectedSlotData N) (m : Ideal O → ℂ) : SelectedSlotData N :=
  {d with coefficient := fun i I => d.coefficient i I*m I}

theorem mask_bounded {d : SelectedSlotData N} {Z mesh C : ℝ}
    (h : d.Bounded Z mesh C) (m : Ideal O → ℂ) (hm : ∀ I, ‖m I‖ ≤ 1) :
    (d.mask m).Bounded Z mesh C := by
  refine ⟨h.width_nonneg,h.width_le_mesh,h.source_nonzero,h.source_norm,?_⟩
  intro i
  apply (Finset.sum_le_sum (fun I hI => ?_)).trans (h.coefficient_mass i)
  change ‖d.coefficient i I*m I‖^2 ≤ ‖d.coefficient i I‖^2
  exact pow_le_pow_left₀ (norm_nonneg _)
    (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hm I)) 2

def quotient (d : SelectedSlotData N) (a : O) : SelectedSlotData N :=
  d.mask (fun I => idealRowHom a I)

theorem quotient_bounded {d : SelectedSlotData N} {Z mesh C : ℝ}
    (h : d.Bounded Z mesh C) (a : O) : (d.quotient a).Bounded Z mesh C :=
  mask_bounded h _ (idealRowHom_norm a)

theorem quotient_polynomial (d : SelectedSlotData N) (a z : O) (i : Fin N) :
    (d.quotient a).polynomial i z=d.polynomial i (a*z) := by
  unfold polynomial quotient mask
  apply Finset.sum_congr rfl
  intro I hI
  rw [idealRowHom_argument_mul]
  ring

theorem quotient_selects {d : SelectedSlotData N} {Z : ℝ} {rows child : Finset O}
    (h : d.Selects Z rows) (a : O) (hchild : ∀ z ∈ child, a*z ∈ rows) :
    (d.quotient a).Selects Z child := by
  intro z hz i
  rw [quotient_polynomial]
  exact h (a*z) (hchild z hz) i

theorem quotient_hasSlope {d : SelectedSlotData N} {δ : ℝ}
    (h : d.HasSlope δ) (a : O) : (d.quotient a).HasSlope δ := h

end SelectedSlotData
end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.SelectedSlotData.quotient_bounded
#print axioms Qrh.JointDetector.SelectedSlotData.quotient_selects
