/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.FloorSteps
import Submissions.hailey_collet_1252270103.Record12518109Source.FloorBase
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

theorem raw_floorK_bounds (k : Fin 15) (p : Bool) :
    0 ≤ floorK (rawCells k) p ∧ floorK (rawCells k) p ≤ 3/4 := by
  cases p
  · norm_num [floorK]
  · fin_cases k <;> norm_num [floorK,rawCells,K,incumbent,
      cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7,
      cell8,cell9,cell10,cell11,cell12,cell13,cell14]

theorem floor_density_bound {ν : ℝ} (hν : ν ∈ Set.Icc (31/50) (3/4)) :
    0 ≤ ν ∧ 0 ≤ d ν ∧ d ν ≤ 4 ∧ 2 ≤ etaD ν+rr ν := by
  have hs := sq_nonneg (ν-31/50)
  unfold etaD rr d
  constructor
  · linarith [hν.1]
  constructor
  · linarith [hν.2]
  constructor
  · linarith [hν.1]
  · nlinarith [hν.1,hν.2]

theorem raw_naturalFloor_all (k : Fin 15) {ν : ℝ}
    (hν : ν ∈ Set.Icc (rawCells k).q (3/4)) (p : Bool)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    0 ≤ naturalFloor (rawCells k) i j p ν := by
  have hq := (raw_mixed_parameters k).2.2.2.2.1
  have hdensity := floor_density_bound (ν:=ν) ⟨hq.trans hν.1,hν.2⟩
  rcases raw_floorK_bounds k p with ⟨hk,hkhi⟩
  have hkd : floorK (rawCells k) p*d ν ≤ 3 := by
    have hh := mul_le_mul hkhi hdensity.2.2.1 hdensity.2.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hh
    exact hh
  have hleft : 0 ≤ 6*d ν*(1-floorK (rawCells k) p/3) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hdensity.2.1) (by linarith)
  have hright : 0 ≤ etaD ν+rr ν-floorK (rawCells k) p*d ν/3 := by
    linarith [hdensity.2.2.2]
  have h := six_reduction (fun a b => -naturalFloor (rawCells k) a b p ν)
    ?_ ?_ ?_ i j hi hj
  · linarith
  · intro a b ha ha6 hb hb6
    let ai : Fin 6 := ⟨a-1,by omega⟩
    let bj : Fin 6 := ⟨b-1,by omega⟩
    have ha' : ai.val+1 = a := by dsimp [ai]; omega
    have hb' : bj.val+1 = b := by dsimp [bj]; omega
    have h := raw_naturalFloor_base k hν p ai bj
    rw [ha',hb'] at h
    exact neg_nonpos.mpr h
  · intro a b _ _
    have hs := naturalFloor_step_left (rawCells k) p ν a b
      hdensity.2.1 hdensity.1 hk
    linarith only [hs,hleft]
  · intro a b _ _
    have hs := naturalFloor_step_right (rawCells k) p ν a b
      hdensity.2.1 hdensity.1 hk
    linarith only [hs,hright]

theorem raw_complementaryFloor_all (k : Fin 15) {ν : ℝ}
    (hν : ν ∈ Set.Icc (rawCells k).q (3/4))
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    0 ≤ complementaryFloor i j ν := by
  have hq := (raw_mixed_parameters k).2.2.2.2.1
  have hdensity := floor_density_bound (ν:=ν) ⟨hq.trans hν.1,hν.2⟩
  have h := six_reduction (fun a b => -complementaryFloor a b ν) ?_ ?_ ?_ i j hi hj
  · linarith
  · intro a b ha ha6 hb hb6
    let ai : Fin 6 := ⟨a-1,by omega⟩
    let bj : Fin 6 := ⟨b-1,by omega⟩
    have ha' : ai.val+1 = a := by dsimp [ai]; omega
    have hb' : bj.val+1 = b := by dsimp [bj]; omega
    have h := raw_complementaryFloor_base k hν ai bj
    rw [ha',hb'] at h
    exact neg_nonpos.mpr h
  · intro a b _ _
    have hs := complementaryFloor_step_left (rawCells k) ν a b hdensity.2.1 hdensity.1
    linarith only [hs,hdensity.2.1]
  · intro a b _ _
    have hs := complementaryFloor_step_right (rawCells k) ν a b hdensity.2.1 hdensity.1
    linarith only [hs,hdensity.2.2.2]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.raw_naturalFloor_all
#print axioms QRH.Record12518109Source.raw_complementaryFloor_all
