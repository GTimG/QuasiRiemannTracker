/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ConsumerParameters
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Cycle153.Consumer
noncomputable section

theorem top_old_outside_0 {d p : ℝ} (hd : d∈Set.Icc ((0:ℝ)) (43/100))
    (hp : p∈Set.Icc ((0:ℝ)) (1/2)) :
    0<oldCleared (h) (newCapacity h) topSaving d p := by
  have hl:=lambda_bounds
  have hb:=B_bounds
  simp only [oldCleared, J, D, P, V, common, newCapacity, oldCapacity, ell, y, kappaStar, theta, h, topSaving, rowSaving, dMinus, dPlus, countCap]
  rat_pos (depth := 30) [hd,hp,hl,hb]

theorem top_old_outside_1 {d p : ℝ} (hd : d∈Set.Icc (49/100) (3/4))
    (hp : p∈Set.Icc ((0:ℝ)) (1/2)) :
    0<oldCleared (h) (newCapacity h) topSaving d p := by
  have hl:=lambda_bounds
  have hb:=B_bounds
  simp only [oldCleared, J, D, P, V, common, newCapacity, oldCapacity, ell, y, kappaStar, theta, h, topSaving, rowSaving, dMinus, dPlus, countCap]
  rat_pos (depth := 30) [hd,hp,hl,hb]

theorem top_old_outside_2 {d p : ℝ} (hd : d∈Set.Icc (43/100) (49/100))
    (hp : p∈Set.Icc ((0:ℝ)) (495/1000)) :
    0<oldCleared (h) (newCapacity h) topSaving d p := by
  have hl:=lambda_bounds
  have hb:=B_bounds
  simp only [oldCleared, J, D, P, V, common, newCapacity, oldCapacity, ell, y, kappaStar, theta, h, topSaving, rowSaving, dMinus, dPlus, countCap]
  rat_pos (depth := 30) [hd,hp,hl,hb]

theorem top_affine {d p : ℝ} (hd : d∈Set.Icc (43/100) (49/100))
    (hp : p∈Set.Icc (495/1000) (1/2)) :
    0<affineCleared (h) (newCapacity h) topSaving d p := by
  have hl:=lambda_bounds
  have hb:=B_bounds
  simp only [affineCleared, affineD, affineN, affineSI, affineSP, affineA, common, V, newCapacity, oldCapacity, ell, y, kappaStar, theta, h, topSaving, rowSaving, dMinus, dPlus, countCap]
  rat_pos (depth := 30) [hd,hp,hl,hb]

theorem top_capped {d p : ℝ} (hd : d∈Set.Icc (43/100) (49/100))
    (hp : p∈Set.Icc (495/1000) (1/2)) :
    0<cappedCleared (h) (newCapacity h) topSaving d p := by
  have hl:=lambda_bounds
  have hb:=B_bounds
  simp only [cappedCleared, cappedD, cappedN, cappedSP, cappedA, affineSI, common, V, newCapacity, oldCapacity, OAI.SevenEighths.Cycle153Geometry.Coordinates.top, ell, y, kappaStar, theta, h, topSaving, rowSaving, dMinus, dPlus, countCap]
  rat_pos (depth := 30) [hd,hp,hl,hb]

theorem top_plain {d p : ℝ} (hd : d∈Set.Icc (43/100) (49/100))
    (hp : p∈Set.Icc (495/1000) (1/2)) :
    0<plainMargin (h) (newCapacity h) topSaving d p := by
  have hl:=lambda_bounds
  have hb:=B_bounds
  simp only [plainMargin, plain, common, newCapacity, oldCapacity, ell, y, kappaStar, theta, h, topSaving, rowSaving, dMinus, dPlus, countCap]
  rat_pos (depth := 30) [hd,hp,hl,hb]

end
end Cycle153.Consumer

#print axioms Cycle153.Consumer.top_old_outside_0

#print axioms Cycle153.Consumer.top_old_outside_1

#print axioms Cycle153.Consumer.top_old_outside_2

#print axioms Cycle153.Consumer.top_affine

#print axioms Cycle153.Consumer.top_capped

#print axioms Cycle153.Consumer.top_plain
