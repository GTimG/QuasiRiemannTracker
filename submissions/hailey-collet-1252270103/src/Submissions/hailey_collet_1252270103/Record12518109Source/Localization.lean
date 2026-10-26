/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.ValuationCore
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

theorem localR_add_left (i j : ℕ) : localR (i+6) j = localR i j := by
  simp [localR,residue_add_left]
theorem localR_add_right (i j : ℕ) : localR i (j+6) = localR i j := by
  simp [localR,residue_add_right]
theorem localL_add_left (i j : ℕ) : localL (i+6) j = localL i j := by
  simp [localL,residue_add_left]
theorem localL_add_right (i j : ℕ) : localL i (j+6) = localL i j := by
  simp [localL,residue_add_right]
theorem localO_add_left (i j : ℕ) : localO (i+6) j = localO i j := by
  simp [localO,residue_add_left]
theorem localO_add_right (i j : ℕ) : localO i (j+6) = localO i j := by
  simp [localO,residue_add_right]

theorem localB_add_left_le (i j : ℕ) : localB (i+6) j ≤ localB i j+3 := by
  unfold localB
  rw [localR_add_left]
  push_cast
  have h := le_max_left (3*(i:ℝ)-5*(j:ℝ)-localR i j) 0
  have hn := le_max_right (3*(i:ℝ)-5*(j:ℝ)-localR i j) 0
  have hm : max (3*((i:ℝ)+6)-5*(j:ℝ)-localR i j) 0 ≤
      max (3*(i:ℝ)-5*(j:ℝ)-localR i j) 0+18 := by
    apply max_le <;> linarith
  linarith

theorem localB_add_right_le (i j : ℕ) : localB i (j+6) ≤ localB i j := by
  unfold localB
  rw [localR_add_right]
  push_cast
  have hm : max (3*(i:ℝ)-5*((j:ℝ)+6)-localR i j) 0 ≤
      max (3*(i:ℝ)-5*(j:ℝ)-localR i j) 0 :=
    max_le_max (by linarith) le_rfl
  linarith

theorem localization_add_left (i j : ℕ) :
    localizationReserve i j ≤ localizationReserve (i+6) j := by
  have hb := localB_add_left_le i j
  have hc := localB_add_right_le j i
  have hm : min (i:ℝ) (j:ℝ) ≤ min ((i:ℝ)+6) (j:ℝ) :=
    min_le_min (by linarith) le_rfl
  unfold localizationReserve localSigma
  rw [localR_add_left]
  push_cast
  linarith

theorem localization_add_right (i j : ℕ) :
    localizationReserve i j ≤ localizationReserve i (j+6) := by
  have hb := localB_add_right_le i j
  have hc := localB_add_left_le j i
  have hm : min (i:ℝ) (j:ℝ) ≤ min (i:ℝ) ((j:ℝ)+6) :=
    min_le_min le_rfl (by linarith)
  unfold localizationReserve localSigma
  rw [localR_add_right]
  push_cast
  linarith

/-- The localization inequality covers every positive multiplicity pair. -/
theorem localization_all (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    0 ≤ localizationReserve i j := by
  have h := six_reduction (fun a b => -localizationReserve a b) ?_ ?_ ?_ i j hi hj
  · linarith
  · intro a b ha ha6 hb hb6
    let ai : Fin 6 := ⟨a-1,by omega⟩
    let bj : Fin 6 := ⟨b-1,by omega⟩
    have ha' : ai.val+1 = a := by dsimp [ai]; omega
    have hb' : bj.val+1 = b := by dsimp [bj]; omega
    have h := localization_six ai bj
    rw [ha',hb'] at h
    exact neg_nonpos.mpr h
  · intro a b _ _
    exact neg_le_neg (localization_add_left a b)
  · intro a b _ _
    exact neg_le_neg (localization_add_right a b)

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.localization_all
