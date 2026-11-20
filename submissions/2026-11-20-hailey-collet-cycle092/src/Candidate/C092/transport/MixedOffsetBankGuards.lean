/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Q.2's closed endpoints, reciprocal order and preceding-cutoff collar. -/
import Candidate.C092.transport.MixedOffsetBankLengths
import Candidate.C092.transport.MixedOffsetBankCells
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetBank
noncomputable section

/-- The physical reciprocal's lower length exceeds every auxiliary cutoff
if it exceeds the preselected top endpoint. No reciprocal is replaced. -/
theorem reciprocal_above_bank (t₀ γ reciprocalLower : ℝ) (hγ : 0≤γ)
    (hretained : t₀<reciprocalLower) (j : Offset) : cutoff t₀ γ j<reciprocalLower := by
  have h:=(offset_bounds γ hγ j).1
  dsimp [cutoff];linarith

/-- Closed bank endpoints are retained, with strict native taper-domain
margins inherited uniformly from the original coarse cell guards. -/
theorem strict_cutoff_guards (t₀ γ : ℝ) (hγ : 0≤γ)
    (hlo : 1<t₀-γ) (hhi : t₀<3/2) (j : Offset) :
    1<cutoff t₀ γ j ∧ cutoff t₀ γ j<3/2 := by
  have h:=offset_bounds γ hγ j
  dsimp [cutoff];constructor <;> linarith

/-- This is precisely Q.2's H_j argument, including the first offset.
The previous cutoff is used before subtracting the allocated collar. -/
theorem previous_collar_exact (γ εa : ℝ) (hγ : 0≤γ) (hεa : 0≤εa) (j : Offset) :
    max 0 (offset γ (previous j)-3*εa)=max 0 (offset γ j-γ/65536-3*εa) := by
  rw [previous_offset γ hγ j]
  by_cases h : 0≤offset γ j-γ/65536
  · rw [max_eq_right h]
  · have h' : offset γ j-γ/65536≤0:=le_of_not_ge h
    rw [max_eq_left h',max_eq_left (by linarith : (0:ℝ)-3*εa≤0),max_eq_left (by linarith)]

#print axioms reciprocal_above_bank
#print axioms strict_cutoff_guards
#print axioms previous_collar_exact
end
end QRH.Cycle092.MixedOffsetBank
