/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def nr2_d_positive_g : Fin 1 → Fin 4 → ℝ := ![![(2010000/2197:ℝ), (5770000/2197:ℝ), (5510000/2197:ℝ), (1750000/2197:ℝ)]]
theorem nr2_d_positive {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (d ν) := by
 have heq : (d ν) = Record12518109.Bernstein.bsum 0 3 (7/4:ℝ) nr2_d_positive_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_d_positive_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_d_positive_g]
def nr2_a_positive_g : Fin 1 → Fin 4 → ℝ := ![![(44270000/2197:ℝ), (125790000/2197:ℝ), (118770000/2197:ℝ), (37250000/2197:ℝ)]]
theorem nr2_a_positive {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (aa ν) := by
 have heq : (aa ν) = Record12518109.Bernstein.bsum 0 3 (149/4:ℝ) nr2_a_positive_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_a_positive_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_a_positive_g]
def nr2_c_positive_g : Fin 1 → Fin 4 → ℝ := ![![(58690000/2197:ℝ), (158130000/2197:ℝ), (140190000/2197:ℝ), (40750000/2197:ℝ)]]
theorem nr2_c_positive {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (cc ν) := by
 have heq : (cc ν) = Record12518109.Bernstein.bsum 0 3 (163/4:ℝ) nr2_c_positive_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_c_positive_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_c_positive_g]
def nr2_w_positive_g : Fin 1 → Fin 4 → ℝ := ![![(1030000/2197:ℝ), (2310000/2197:ℝ), (1530000/2197:ℝ), (250000/2197:ℝ)]]
theorem nr2_w_positive {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (w ν) := by
 have heq : (w ν) = Record12518109.Bernstein.bsum 0 3 (1/4:ℝ) nr2_w_positive_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_w_positive_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_w_positive_g]
def nr2_xi_saturated_below_one_g : Fin 1 → Fin 4 → ℝ := ![![(7210000/2197:ℝ), (16170000/2197:ℝ), (10710000/2197:ℝ), (1750000/2197:ℝ)]]
theorem nr2_xi_saturated_below_one {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (cc ν-(150-96*ν)) := by
 have heq : (cc ν-(150-96*ν)) = Record12518109.Bernstein.bsum 0 3 (7/4:ℝ) nr2_xi_saturated_below_one_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_xi_saturated_below_one_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_xi_saturated_below_one_g]
def nr2_cutoff_below_three_halves_g : Fin 1 → Fin 4 → ℝ := ![![(515000/2197:ℝ), (1155000/2197:ℝ), (765000/2197:ℝ), (125000/2197:ℝ)]]
theorem nr2_cutoff_below_three_halves {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (3/2*d ν-5) := by
 have heq : (3/2*d ν-5) = Record12518109.Bernstein.bsum 0 3 (1/8:ℝ) nr2_cutoff_below_three_halves_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_cutoff_below_three_halves_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_cutoff_below_three_halves_g]
def nr2_A_below_phi_g : Fin 1 → Fin 4 → ℝ := ![![(16130000/2197:ℝ), (45010000/2197:ℝ), (41630000/2197:ℝ), (12750000/2197:ℝ)]]
theorem nr2_A_below_phi {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (aa ν-14*d ν) := by
 have heq : (aa ν-14*d ν) = Record12518109.Bernstein.bsum 0 3 (51/4:ℝ) nr2_A_below_phi_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_A_below_phi_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_A_below_phi_g]
def nr2_B_below_C_g : Fin 1 → Fin 4 → ℝ := ![![(295470000/2197:ℝ), (848190000/2197:ℝ), (809970000/2197:ℝ), (257250000/2197:ℝ)]]
theorem nr2_B_below_C {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (8*aa ν-cc ν) := by
 have heq : (8*aa ν-cc ν) = Record12518109.Bernstein.bsum 0 3 (1029/4:ℝ) nr2_B_below_C_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_B_below_C_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_B_below_C_g]
def nr2_C_below_one_fiftieth_g : Fin 1 → Fin 4 → ℝ := ![![(154518400/2197:ℝ), (1003648000/2197:ℝ), (1463634800/2197:ℝ), (551231600/2197:ℝ)]]
theorem nr2_C_below_one_fiftieth {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (3*d ν*cc ν-800*ν*(w ν)^2) := by
 have heq : (3*d ν*cc ν-800*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (96574/625:ℝ) nr2_C_below_one_fiftieth_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_C_below_one_fiftieth_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_C_below_one_fiftieth_g]
def nr2_rho_minus_C_above_one_sixth_g : Fin 1 → Fin 4 → ℝ := ![![(252517572/2197:ℝ), (522637100/2197:ℝ), (320822500/2197:ℝ), (49437500/2197:ℝ)]]
theorem nr2_rho_minus_C_above_one_sixth {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < ((rr ν-d ν/6)*3*cc ν-16*ν*(w ν)^2) := by
 have heq : ((rr ν-d ν/6)*3*cc ν-16*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (791/16:ℝ) nr2_rho_minus_C_above_one_sixth_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_rho_minus_C_above_one_sixth_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_rho_minus_C_above_one_sixth_g]
def nr2_s1_below_s2_g : Fin 1 → Fin 4 → ℝ := ![![(221350000/2197:ℝ), (628950000/2197:ℝ), (593850000/2197:ℝ), (186250000/2197:ℝ)]]
theorem nr2_s1_below_s2 {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (21*(45-26*ν)-2*cc ν) := by
 have heq : (21*(45-26*ν)-2*cc ν) = Record12518109.Bernstein.bsum 0 3 (745/4:ℝ) nr2_s1_below_s2_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_s1_below_s2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_s1_below_s2_g]
def nr2_xi_base_above_seven_eighths_g : Fin 1 → Fin 4 → ℝ := ![![(5000/169:ℝ), (67500/169:ℝ), (120000/169:ℝ), (57500/169:ℝ)]]
theorem nr2_xi_base_above_seven_eighths {b ν : ℝ} (hb : b ∈ Set.Icc (0:ℝ) (1:ℝ))
    (hν : ν ∈ Set.Icc (31/50:ℝ) (3/4:ℝ)) : 0 < (10-21/8*d ν) := by
 have heq : (10-21/8*d ν) = Record12518109.Bernstein.bsum 0 3 (13/200:ℝ) nr2_xi_base_above_seven_eighths_g (0:ℝ) (1:ℝ) (31/50:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, nr2_xi_base_above_seven_eighths_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [nr2_xi_base_above_seven_eighths_g]
end
end Record12518109Admission
