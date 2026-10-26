/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.Localization
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

theorem localR_swap (i j : ℕ) : localR i j = localR j i := by
  have hz : ((i:ℤ)-(j:ℤ))%6 = 0 ↔ ((j:ℤ)-(i:ℤ))%6 = 0 := by
    rw [←Int.dvd_iff_emod_eq_zero,←Int.dvd_iff_emod_eq_zero]
    simpa only [neg_sub] using (Int.dvd_neg (a:=6) (b:=(j:ℤ)-(i:ℤ)))
  simp only [localR,residue,hz]
  rfl

theorem localSigma_step_left (i j : ℕ) : localSigma i j ≤ localSigma (i+6) j := by
  have hb := localB_add_left_le i j
  have hc := localB_add_right_le j i
  unfold localSigma
  rw [localR_add_left]
  push_cast
  linarith
theorem localSigma_step_right (i j : ℕ) : localSigma i j ≤ localSigma i (j+6) := by
  have hb := localB_add_right_le i j
  have hc := localB_add_left_le j i
  unfold localSigma
  rw [localR_add_right]
  push_cast
  linarith

theorem localSigma_all (i j : ℕ) (hi : 0 < i) (hj : 0 < j) : 0 ≤ localSigma i j := by
  have hbase (i j : Fin 6) : 0 ≤ localSigma (i.val+1) (j.val+1) := by
    fin_cases i <;> fin_cases j <;> norm_num [localSigma,localB,localR,residue]
  have h := six_reduction (fun a b => -localSigma a b) ?_ ?_ ?_ i j hi hj
  · linarith
  · intro a b ha ha6 hb hb6
    let ai : Fin 6 := ⟨a-1,by omega⟩
    let bj : Fin 6 := ⟨b-1,by omega⟩
    have ha' : ai.val+1 = a := by dsimp [ai]; omega
    have hb' : bj.val+1 = b := by dsimp [bj]; omega
    have h := hbase ai bj
    rw [ha',hb'] at h
    exact neg_nonpos.mpr h
  · intro a b _ _
    exact neg_le_neg (localSigma_step_left a b)
  · intro a b _ _
    exact neg_le_neg (localSigma_step_right a b)
end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.localSigma_all
