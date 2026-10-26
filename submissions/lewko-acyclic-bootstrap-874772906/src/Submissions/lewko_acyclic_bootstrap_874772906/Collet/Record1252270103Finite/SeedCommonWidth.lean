/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109.Bernstein
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def seedD (ν:ℝ) : ℝ := 5-2*ν
def seedPhi (ν:ℝ) : ℝ := ν*(5-6*ν)/seedD ν
def seedC (ν:ℝ) : ℝ := 16*ν*(5-6*ν)^2/(3*seedD ν*(185-138*ν))
def seedClearedRate (ν:ℝ) : ℝ := ν*(15-6*ν)*(185-138*ν)-3*ν*(5-6*ν)*(185-138*ν)-32*ν*(5-6*ν)^2
def seedRateCoefficients : Fin 4→Fin 1→ℝ := ![![(9088/1:ℝ)],![(47008/1:ℝ)],![(66464/1:ℝ)],![(25736/1:ℝ)]]
theorem seed_rate_identity (ν:ℝ) : seedClearedRate ν =
 Record12518109.Bernstein.bsum 3 0 (142/1:ℝ) seedRateCoefficients (1/2) (3/4) 0 1 ν 0 := by
 norm_num [seedClearedRate,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,seedRateCoefficients,Fin.sum_univ_succ]
 ring
theorem seed_cleared_rate_pos {ν:ℝ} (hν:ν∈Set.Icc (1/2) (3/4)) : 0<seedClearedRate ν := by
 rw [seed_rate_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hν (by norm_num)
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [seedRateCoefficients]
theorem seed_common_width_rate {ν:ℝ} (hν:ν∈Set.Icc (1/2) (3/4)) : 0<ν-seedPhi ν-2*seedC ν := by
 have hd : 0<seedD ν := by dsimp [seedD]; linarith [hν.2]
 have he : 0<185-138*ν := by linarith [hν.2]
 have hp : 0<3*seedD ν*(185-138*ν) := by positivity
 have hφ : seedPhi ν*(3*seedD ν*(185-138*ν))=3*ν*(5-6*ν)*(185-138*ν) := by
  unfold seedPhi
  calc
   (ν*(5-6*ν)/seedD ν)*(3*seedD ν*(185-138*ν)) =
    ((ν*(5-6*ν)/seedD ν)*seedD ν)*(3*(185-138*ν)) := by ring
   _ = (ν*(5-6*ν))*(3*(185-138*ν)) := by rw [div_mul_cancel₀ _ (ne_of_gt hd)]
   _ = _ := by ring
 have hC : seedC ν*(3*seedD ν*(185-138*ν))=16*ν*(5-6*ν)^2 := by
  exact div_mul_cancel₀ _ (ne_of_gt hp)
 have hmul : (ν-seedPhi ν-2*seedC ν)*(3*seedD ν*(185-138*ν))=seedClearedRate ν := by
  calc
   _ = ν*(3*seedD ν*(185-138*ν))-seedPhi ν*(3*seedD ν*(185-138*ν))-
    2*(seedC ν*(3*seedD ν*(185-138*ν))) := by ring
   _ = ν*(3*seedD ν*(185-138*ν))-3*ν*(5-6*ν)*(185-138*ν)-2*(16*ν*(5-6*ν)^2) := by rw [hφ,hC]
   _ = _ := by dsimp [seedClearedRate,seedD]; ring
 have h := seed_cleared_rate_pos hν
 rw [←hmul] at h
 exact (mul_pos_iff_of_pos_right hp).mp h
#print axioms seed_common_width_rate
end
end Record1252270103Finite
