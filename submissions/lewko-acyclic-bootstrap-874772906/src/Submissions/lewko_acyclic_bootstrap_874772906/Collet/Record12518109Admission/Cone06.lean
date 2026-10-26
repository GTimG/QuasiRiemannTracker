/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell06
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell6_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(276327233971/914970975036:ℝ)]]
theorem cell6_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 1 1) := by
 have heq : (-orderedLow cell6 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_1_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_1_1_g]
def cell6_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(632383460170545472/3394618564964813:ℝ), (4270576374507268660/10183855694894439:ℝ), (2414161416775210000/10183855694894439:ℝ)]]
theorem cell6_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 1 1 ν := by
 have heq : mixedLowHigh cell6 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_1_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_1_1_g]
def cell6_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(28684/211:ℝ), (67840/211:ℝ), (40000/211:ℝ)]]
theorem cell6_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 1 false ν := by
 have heq : naturalFloor cell6 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_1_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_1_1_g]
def cell6_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(760302431476/5006341929:ℝ), (5293614871280/15019025787:ℝ), (3072783680000/15019025787:ℝ)]]
theorem cell6_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 1 true ν := by
 have heq : naturalFloor cell6 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_1_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_1_1_g]
def cell6_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(28684/211:ℝ), (67840/211:ℝ), (40000/211:ℝ)]]
theorem cell6_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_1_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_1_1_g]
def cell6_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(75397624000000/1982119441:ℝ), (509263854344000/5946358323:ℝ), (279105764000000/5946358323:ℝ)],
  ![(509263854344000/5946358323:ℝ), (4175189455357168000/22066935736653:ℝ), (2256718102408000000/22066935736653:ℝ)],
  ![(279105764000000/5946358323:ℝ), (2256718102408000000/22066935736653:ℝ), (1207078348000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 1 1 b ν := by
 have heq : pairedCleared cell6 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_1_1_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_1_1_g]
theorem cell6_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_1_1 hb hν
def cell6_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(31856713777170899/45748548751800000:ℝ)]]
theorem cell6_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 1 2) := by
 have heq : (-orderedLow cell6 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_1_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_1_2_g]
def cell6_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(158045086554350900589/339461856496481300:ℝ), (1038140895665773590067/1018385569489443900:ℝ), (5721527205586364395/10183855694894439:ℝ)]]
theorem cell6_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 1 2 ν := by
 have heq : mixedLowHigh cell6 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_1_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_1_2_g]
def cell6_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(57368/211:ℝ), (135680/211:ℝ), (80000/211:ℝ)]]
theorem cell6_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 2 false ν := by
 have heq : naturalFloor cell6 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_1_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_1_2_g]
def cell6_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(57368/211:ℝ), (135680/211:ℝ), (80000/211:ℝ)]]
theorem cell6_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 2 true ν := by
 have heq : naturalFloor cell6 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_1_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_1_2_g]
def cell6_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(57368/211:ℝ), (135680/211:ℝ), (80000/211:ℝ)]]
theorem cell6_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_1_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_1_2_g]
def cell6_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(205881332000000/1982119441:ℝ), (1339647960688000/5946358323:ℝ), (714073528000000/5946358323:ℝ)],
  ![(395169659448000/1982119441:ℝ), (1061608982911528000/2451881748517:ℝ), (566430072068000000/2451881748517:ℝ)],
  ![(187966588000000/1982119441:ℝ), (1518151358204000000/7355645245551:ℝ), (811355174000000000/7355645245551:ℝ)]]
theorem cell6_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 1 2 b ν := by
 have heq : pairedCleared cell6 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_1_2_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_1_2_g]
theorem cell6_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_1_2 hb hν
def cell6_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(354533701063601/11437137187950000:ℝ)]]
theorem cell6_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 1 3) := by
 have heq : (-orderedLow cell6 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_1_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_1_3_g]
def cell6_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(4654799336413612211/84865464124120325:ℝ), (70945591198912815433/254596392372360975:ℝ), (2401453995925612420/10183855694894439:ℝ)]]
theorem cell6_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 1 3 ν := by
 have heq : mixedLowHigh cell6 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_1_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_1_3_g]
def cell6_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(86052/211:ℝ), (203520/211:ℝ), (120000/211:ℝ)]]
theorem cell6_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 3 false ν := by
 have heq : naturalFloor cell6 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_1_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_1_3_g]
def cell6_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(1962008694428/5006341929:ℝ), (14021848813840/15019025787:ℝ), (8316051040000/15019025787:ℝ)]]
theorem cell6_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 3 true ν := by
 have heq : naturalFloor cell6 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_1_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_1_3_g]
def cell6_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(86052/211:ℝ), (203520/211:ℝ), (120000/211:ℝ)]]
theorem cell6_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_1_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_1_3_g]
def cell6_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (330516504000/9393931:ℝ), (311724000000/9393931:ℝ)],
  ![(1930516504000/28181793:ℝ), (21071018041376000/104582633823:ℝ), (13500333056000000/104582633823:ℝ)],
  ![(1911724000000/28181793:ℝ), (17255865056000000/104582633823:ℝ), (9964136000000000/104582633823:ℝ)]]
theorem cell6_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 1 3 b ν := by
 have heq : pairedCleared cell6 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_1_3_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_1_3_g]
theorem cell6_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_1_3 hb hν
def cell6_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(34098022483451303/45748548751800000:ℝ)]]
theorem cell6_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 1 4) := by
 have heq : (-orderedLow cell6 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_1_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_1_4_g]
def cell6_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(113425937882950802233/339461856496481300:ℝ), (894865623010697985799/1018385569489443900:ℝ), (5708819784736766815/10183855694894439:ℝ)]]
theorem cell6_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 1 4 ν := by
 have heq : mixedLowHigh cell6 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_1_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_1_4_g]
def cell6_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(114736/211:ℝ), (271360/211:ℝ), (160000/211:ℝ)]]
theorem cell6_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 4 false ν := by
 have heq : naturalFloor cell6 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_1_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_1_4_g]
def cell6_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(2562861825904/5006341929:ℝ), (18385965785120/15019025787:ℝ), (10937684720000/15019025787:ℝ)]]
theorem cell6_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 4 true ν := by
 have heq : naturalFloor cell6 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_1_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_1_4_g]
def cell6_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(114736/211:ℝ), (271360/211:ℝ), (160000/211:ℝ)]]
theorem cell6_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_1_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_1_4_g]
def cell6_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(130483708000000/1982119441:ℝ), (1039601053376000/5946358323:ℝ), (632289056000000/5946358323:ℝ)],
  ![(1083584106344000/5946358323:ℝ), (9825276197576920000/22066935736653:ℝ), (5689722821020000000/22066935736653:ℝ)],
  ![(688167764000000/5946358323:ℝ), (5938723499020000000/22066935736653:ℝ), (3329419870000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 1 4 b ν := by
 have heq : pairedCleared cell6 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_1_4_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_1_4_g]
theorem cell6_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_1_4 hb hν
def cell6_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(33388955081324101/22874274375900000:ℝ)]]
theorem cell6_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 1 5) := by
 have heq : (-orderedLow cell6 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_1_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_1_5_g]
def cell6_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(104116339210123577811/169730928248240650:ℝ), (752974440612872354933/509192784744721950:ℝ), (9016185573547921210/10183855694894439:ℝ)]]
theorem cell6_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 1 5 ν := by
 have heq : mixedLowHigh cell6 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_1_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_1_5_g]
def cell6_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(143420/211:ℝ), (339200/211:ℝ), (200000/211:ℝ)]]
theorem cell6_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 5 false ν := by
 have heq : naturalFloor cell6 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_1_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_1_5_g]
def cell6_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(1054571652460/1668780643:ℝ), (7583360918800/5006341929:ℝ), (4519772800000/5006341929:ℝ)]]
theorem cell6_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 5 true ν := by
 have heq : naturalFloor cell6 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_1_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_1_5_g]
def cell6_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(143420/211:ℝ), (339200/211:ℝ), (200000/211:ℝ)]]
theorem cell6_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_1_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_1_5_g]
def cell6_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(260967416000000/1982119441:ℝ), (1869985159720000/5946358323:ℝ), (1067256820000000/5946358323:ℝ)],
  ![(586609743448000/1982119441:ℝ), (5068189196141168000/7355645245551:ℝ), (2843625122408000000/7355645245551:ℝ)],
  ![(324320588000000/1982119441:ℝ), (2745486490408000000/7355645245551:ℝ), (1518802348000000000/7355645245551:ℝ)]]
theorem cell6_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 1 5 b ν := by
 have heq : pairedCleared cell6 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_1_5_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_1_5_g]
theorem cell6_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_1_5 hb hν
def cell6_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(225694731146071889/45748548751800000:ℝ)]]
theorem cell6_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 1 6) := by
 have heq : (-orderedLow cell6 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_1_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_1_6_g]
def cell6_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(475816438076841509011/339461856496481300:ℝ), (2864105940557685433933/1018385569489443900:ℝ), (14610978799949075605/10183855694894439:ℝ)]]
theorem cell6_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 1 6 ν := by
 have heq : mixedLowHigh cell6 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_1_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_1_6_g]
def cell6_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(58973944/44521:ℝ), (118545440/44521:ℝ), (60640000/44521:ℝ)]]
theorem cell6_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 6 false ν := by
 have heq : naturalFloor cell6 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_1_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_1_6_g]
def cell6_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(6312662428856/5006341929:ℝ), (38131952747680/15019025787:ℝ), (19554422080000/15019025787:ℝ)]]
theorem cell6_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 1 6 true ν := by
 have heq : naturalFloor cell6 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_1_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_1_6_g]
def cell6_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(58973944/44521:ℝ), (118545440/44521:ℝ), (60640000/44521:ℝ)]]
theorem cell6_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_1_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_1_6_g]
def cell6_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(727816164000000/1982119441:ℝ), (1384928128688000/1982119441:ℝ), (649181528000000/1982119441:ℝ)],
  ![(4396889474344000/5946358323:ℝ), (31071646409590088000/22066935736653:ℝ), (14583230433428000000/22066935736653:ℝ)],
  ![(2209475764000000/5946358323:ℝ), (15624648363428000000/22066935736653:ℝ), (7342014218000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 1 6 b ν := by
 have heq : pairedCleared cell6 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_1_6_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_1_6_g]
theorem cell6_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_1_6 hb hν
def cell6_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(56255891045315101/45748548751800000:ℝ)]]
theorem cell6_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 2 1) := by
 have heq : (-orderedLow cell6 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_2_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_2_1_g]
def cell6_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(3601272713504102416/10183855694894439:ℝ), (7148399650920734660/10183855694894439:ℝ), (3587862360196210000/10183855694894439:ℝ)]]
theorem cell6_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 2 1 ν := by
 have heq : mixedLowHigh cell6 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_2_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_2_1_g]
def cell6_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(36908972/133563:ℝ), (73694720/133563:ℝ), (12440000/44521:ℝ)]]
theorem cell6_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 1 false ν := by
 have heq : naturalFloor cell6 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_2_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_2_1_g]
def cell6_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(36908972/133563:ℝ), (73694720/133563:ℝ), (12440000/44521:ℝ)]]
theorem cell6_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 1 true ν := by
 have heq : naturalFloor cell6 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_2_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_2_1_g]
def cell6_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(36908972/133563:ℝ), (73694720/133563:ℝ), (12440000/44521:ℝ)]]
theorem cell6_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_2_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_2_1_g]
def cell6_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(205881332000000/1982119441:ℝ), (395169659448000/1982119441:ℝ), (187966588000000/1982119441:ℝ)],
  ![(1339647960688000/5946358323:ℝ), (1061608982911528000/2451881748517:ℝ), (1518151358204000000/7355645245551:ℝ)],
  ![(714073528000000/5946358323:ℝ), (566430072068000000/2451881748517:ℝ), (811355174000000000/7355645245551:ℝ)]]
theorem cell6_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 2 1 b ν := by
 have heq : pairedCleared cell6 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_2_1_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_2_1_g]
theorem cell6_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_2_1 hb hν
def cell6_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(1191298209007/457485487518:ℝ)]]
theorem cell6_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 2 2) := by
 have heq : (-orderedLow cell6 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_2_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_2_2_g]
def cell6_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(3528405112580154944/3394618564964813:ℝ), (21736864150983729320/10183855694894439:ℝ), (11233119658802420000/10183855694894439:ℝ)]]
theorem cell6_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 2 2 ν := by
 have heq : mixedLowHigh cell6 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_2_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_2_2_g]
def cell6_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(41792648/44521:ℝ), (86316480/44521:ℝ), (44880000/44521:ℝ)]]
theorem cell6_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 2 false ν := by
 have heq : naturalFloor cell6 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_2_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_2_2_g]
def cell6_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(4858990774952/5006341929:ℝ), (30048103478560/15019025787:ℝ), (15591283360000/15019025787:ℝ)]]
theorem cell6_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 2 true ν := by
 have heq : naturalFloor cell6 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_2_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_2_2_g]
def cell6_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(41792648/44521:ℝ), (86316480/44521:ℝ), (44880000/44521:ℝ)]]
theorem cell6_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_2_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_2_2_g]
def cell6_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(591483920000000/1982119441:ℝ), (3587489724688000/5946358323:ℝ), (1805107528000000/5946358323:ℝ)],
  ![(3587489724688000/5946358323:ℝ), (26875164008090336000/22066935736653:ℝ), (13504803260816000000/22066935736653:ℝ)],
  ![(1805107528000000/5946358323:ℝ), (13504803260816000000/22066935736653:ℝ), (6778292696000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 2 2 b ν := by
 have heq : pairedCleared cell6 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_2_2_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_2_2_g]
theorem cell6_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_2_2 hb hν
def cell6_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(137170172979320899/45748548751800000:ℝ)]]
theorem cell6_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 2 3) := by
 have heq : (-orderedLow cell6 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_2_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_2_3_g]
def cell6_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(447647251795311847789/339461856496481300:ℝ), (2784769673313419656067/1018385569489443900:ℝ), (14540485447613574395/10183855694894439:ℝ)]]
theorem cell6_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 2 3 ν := by
 have heq : mixedLowHigh cell6 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_2_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_2_3_g]
def cell6_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(47844972/44521:ℝ), (100630720/44521:ℝ), (53320000/44521:ℝ)]]
theorem cell6_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 3 false ν := by
 have heq : naturalFloor cell6 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_2_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_2_3_g]
def cell6_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(5459843906428/5006341929:ℝ), (34412220449840/15019025787:ℝ), (18212917040000/15019025787:ℝ)]]
theorem cell6_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 3 true ν := by
 have heq : naturalFloor cell6 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_2_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_2_3_g]
def cell6_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(47844972/44521:ℝ), (100630720/44521:ℝ), (53320000/44521:ℝ)]]
theorem cell6_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_2_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_2_3_g]
def cell6_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(721967628000000/1982119441:ℝ), (1472624610344000/1982119441:ℝ), (746691764000000/1982119441:ℝ)],
  ![(4263734848688000/5946358323:ℝ), (32254455398936920000/22066935736653:ℝ), (16345955807020000000/22066935736653:ℝ)],
  ![(2089901528000000/5946358323:ℝ), (15802539233020000000/22066935736653:ℝ), (8005279870000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 2 3 b ν := by
 have heq : pairedCleared cell6 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_2_3_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_2_3_g]
theorem cell6_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_2_3 hb hν
def cell6_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(26682898501601101/11437137187950000:ℝ)]]
theorem cell6_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 2 4) := by
 have heq : (-orderedLow cell6 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_2_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_2_4_g]
def cell6_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(77055340646653849011/84865464124120325:ℝ), (507602785610824331933/254596392372360975:ℝ), (11220412237952822420/10183855694894439:ℝ)]]
theorem cell6_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 2 4 ν := by
 have heq : mixedLowHigh cell6 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_2_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_2_4_g]
def cell6_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(53897296/44521:ℝ), (114944960/44521:ℝ), (61760000/44521:ℝ)]]
theorem cell6_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 4 false ν := by
 have heq : naturalFloor cell6 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_2_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_2_4_g]
def cell6_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(53897296/44521:ℝ), (114944960/44521:ℝ), (61760000/44521:ℝ)]]
theorem cell6_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 4 true ν := by
 have heq : naturalFloor cell6 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_2_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_2_4_g]
def cell6_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(53897296/44521:ℝ), (114944960/44521:ℝ), (61760000/44521:ℝ)]]
theorem cell6_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_2_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_2_4_g]
def cell6_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(516086296000000/1982119441:ℝ), (3287442817376000/5946358323:ℝ), (1723323056000000/5946358323:ℝ)],
  ![(1161854950896000/1982119441:ℝ), (3016217706607056000/2451881748517:ℝ), (1566295048136000000/2451881748517:ℝ)],
  ![(643125176000000/1982119441:ℝ), (4963024228408000000/7355645245551:ℝ), (2557882348000000000/7355645245551:ℝ)]]
theorem cell6_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 2 4 b ν := by
 have heq : pairedCleared cell6 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_2_4_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_2_4_g]
theorem cell6_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_2_4 hb hν
def cell6_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(139411481685601303/45748548751800000:ℝ)]]
theorem cell6_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 2 5) := by
 have heq : (-orderedLow cell6 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_2_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_2_5_g]
def cell6_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(403028103123911749433/339461856496481300:ℝ), (2641494400658344051799/1018385569489443900:ℝ), (14527778026763976815/10183855694894439:ℝ)]]
theorem cell6_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 2 5 ν := by
 have heq : mixedLowHigh cell6 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_2_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_2_5_g]
def cell6_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(59949620/44521:ℝ), (129259200/44521:ℝ), (70200000/44521:ℝ)]]
theorem cell6_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 5 false ν := by
 have heq : naturalFloor cell6 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_2_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_2_5_g]
def cell6_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(6661550169380/5006341929:ℝ), (43140454392400/15019025787:ℝ), (23456184400000/15019025787:ℝ)]]
theorem cell6_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 5 true ν := by
 have heq : naturalFloor cell6 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_2_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_2_5_g]
def cell6_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(59949620/44521:ℝ), (129259200/44521:ℝ), (70200000/44521:ℝ)]]
theorem cell6_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_2_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_2_5_g]
def cell6_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(646570004000000/1982119441:ℝ), (4117826923720000/5946358323:ℝ), (2158290820000000/5946358323:ℝ)],
  ![(4161809976688000/5946358323:ℝ), (32525250750310088000/22066935736653:ℝ), (16937807979428000000/22066935736653:ℝ)],
  ![(2214169528000000/5946358323:ℝ), (17186808657428000000/22066935736653:ℝ), (8900634218000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 2 5 b ν := by
 have heq : pairedCleared cell6 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_2_5_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_2_5_g]
theorem cell6_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_2_5 hb hν
def cell6_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(86045684682399101/22874274375900000:ℝ)]]
theorem cell6_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 2 6) := by
 have heq : (-orderedLow cell6 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_2_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_2_6_g]
def cell6_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(248917421830604051411/169730928248240650:ℝ), (1626288829436695387933/509192784744721950:ℝ), (17835143815575131210/10183855694894439:ℝ)]]
theorem cell6_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 2 6 ν := by
 have heq : mixedLowHigh cell6 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_2_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_2_6_g]
def cell6_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(66001944/44521:ℝ), (143573440/44521:ℝ), (78640000/44521:ℝ)]]
theorem cell6_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 6 false ν := by
 have heq : naturalFloor cell6 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_2_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_2_6_g]
def cell6_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(7262403300856/5006341929:ℝ), (47504571363680/15019025787:ℝ), (26077818080000/15019025787:ℝ)]]
theorem cell6_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 2 6 true ν := by
 have heq : naturalFloor cell6 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_2_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_2_6_g]
def cell6_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(66001944/44521:ℝ), (143573440/44521:ℝ), (78640000/44521:ℝ)]]
theorem cell6_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_2_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_2_6_g]
def cell6_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(777053712000000/1982119441:ℝ), (1649403676688000/1982119441:ℝ), (864419528000000/1982119441:ℝ)],
  ![(4838055100688000/5946358323:ℝ), (37904542141156672000/22066935736653:ℝ), (19778960525632000000/22066935736653:ℝ)],
  ![(2498963528000000/5946358323:ℝ), (19484544629632000000/22066935736653:ℝ), (10127621392000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 2 6 b ν := by
 have heq : pairedCleared cell6 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_2_6_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_2_6_g]
theorem cell6_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_2_6 hb hν
def cell6_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(442088210673569/7624758125300000:ℝ)]]
theorem cell6_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 3 1) := by
 have heq : (-orderedLow cell6 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_3_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_3_1_g]
def cell6_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(1785858544213340456/10183855694894439:ℝ), (1929478069882570900/3394618564964813:ℝ), (4043311088213950000/10183855694894439:ℝ)]]
theorem cell6_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 3 1 ν := by
 have heq : mixedLowHigh cell6 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_3_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_3_1_g]
def cell6_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(32212972/133563:ℝ), (92998720/133563:ℝ), (20440000/44521:ℝ)]]
theorem cell6_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 1 false ν := by
 have heq : naturalFloor cell6 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_3_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_3_1_g]
def cell6_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(375904726492/1668780643:ℝ), (9992864115280/15019025787:ℝ), (6669797680000/15019025787:ℝ)]]
theorem cell6_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 1 true ν := by
 have heq : naturalFloor cell6 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_3_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_3_1_g]
def cell6_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(9946972/133563:ℝ), (49732720/133563:ℝ), (13440000/44521:ℝ)]]
theorem cell6_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_3_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_3_1_g]
def cell6_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (1930516504000/28181793:ℝ), (1911724000000/28181793:ℝ)],
  ![(330516504000/9393931:ℝ), (21071018041376000/104582633823:ℝ), (17255865056000000/104582633823:ℝ)],
  ![(311724000000/9393931:ℝ), (13500333056000000/104582633823:ℝ), (9964136000000000/104582633823:ℝ)]]
theorem cell6_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 3 1 b ν := by
 have heq : pairedCleared cell6 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_3_1_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_3_1_g]
theorem cell6_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_3_1 hb hν
def cell6_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(53856450082488367/15249516250600000:ℝ)]]
theorem cell6_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 3 2) := by
 have heq : (-orderedLow cell6 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_3_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_3_2_g]
def cell6_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(12289337670732930832/10183855694894439:ℝ), (8204895809132398440/3394618564964813:ℝ), (12406820602223420000/10183855694894439:ℝ)]]
theorem cell6_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 3 2 ν := by
 have heq : mixedLowHigh cell6 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_3_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_3_2_g]
def cell6_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(144129944/133563:ℝ), (289701440/133563:ℝ), (48880000/44521:ℝ)]]
theorem cell6_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 2 false ν := by
 have heq : naturalFloor cell6 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_3_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_3_2_g]
def cell6_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(1827382446984/1668780643:ℝ), (33041386176560/15019025787:ℝ), (16715096360000/15019025787:ℝ)]]
theorem cell6_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 2 true ν := by
 have heq : naturalFloor cell6 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_3_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_3_2_g]
def cell6_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(144129944/133563:ℝ), (289701440/133563:ℝ), (48880000/44521:ℝ)]]
theorem cell6_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_3_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_3_2_g]
def cell6_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(721967628000000/1982119441:ℝ), (4263734848688000/5946358323:ℝ), (2089901528000000/5946358323:ℝ)],
  ![(1472624610344000/1982119441:ℝ), (32254455398936920000/22066935736653:ℝ), (15802539233020000000/22066935736653:ℝ)],
  ![(746691764000000/1982119441:ℝ), (16345955807020000000/22066935736653:ℝ), (8005279870000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 3 2 b ν := by
 have heq : pairedCleared cell6 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_3_2_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_3_2_g]
theorem cell6_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_3_2 hb hν
def cell6_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(1496288534019/304990325012:ℝ)]]
theorem cell6_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 3 3) := by
 have heq : (-orderedLow cell6 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_3_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_3_3_g]
def cell6_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(6424426764989764416/3394618564964813:ℝ), (13067717309153396660/3394618564964813:ℝ), (6684025966943210000/3394618564964813:ℝ)]]
theorem cell6_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 3 3 ν := by
 have heq : mixedLowHigh cell6 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_3_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_3_3_g]
def cell6_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(77532972/44521:ℝ), (158318720/44521:ℝ), (81320000/44521:ℝ)]]
theorem cell6_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 3 false ν := by
 have heq : naturalFloor cell6 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_3_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_3_3_g]
def cell6_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(2985893039476/1668780643:ℝ), (18267530695280/5006341929:ℝ), (9369927680000/5006341929:ℝ)]]
theorem cell6_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 3 true ν := by
 have heq : naturalFloor cell6 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_3_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_3_3_g]
def cell6_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(77532972/44521:ℝ), (158318720/44521:ℝ), (81320000/44521:ℝ)]]
theorem cell6_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_3_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_3_3_g]
def cell6_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(1107570216000000/1982119441:ℝ), (2221905198344000/1982119441:ℝ), (1110369764000000/1982119441:ℝ)],
  ![(2221905198344000/1982119441:ℝ), (16525046186941168000/7355645245551:ℝ), (8250962806408000000/7355645245551:ℝ)],
  ![(1110369764000000/1982119441:ℝ), (8250962806408000000/7355645245551:ℝ), (4116502348000000000/7355645245551:ℝ)]]
theorem cell6_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 3 3 b ν := by
 have heq : pairedCleared cell6 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_3_3_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_3_3_g]
theorem cell6_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_3_3 hb hν
def cell6_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(80827877393823633/15249516250600000:ℝ)]]
theorem cell6_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 3 4) := by
 have heq : (-orderedLow cell6 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_3_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_3_4_g]
def cell6_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(737249417036272794989/339461856496481300:ℝ), (1510466150320355240689/339461856496481300:ℝ), (7786481229880261465/3394618564964813:ℝ)]]
theorem cell6_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 3 4 ν := by
 have heq : mixedLowHigh cell6 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_3_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_3_4_g]
def cell6_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(83585296/44521:ℝ), (172632960/44521:ℝ), (89760000/44521:ℝ)]]
theorem cell6_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 4 false ν := by
 have heq : naturalFloor cell6 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_3_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_3_4_g]
def cell6_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(9558532249904/5006341929:ℝ), (59166709057120/15019025787:ℝ), (30731416720000/15019025787:ℝ)]]
theorem cell6_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 4 true ν := by
 have heq : naturalFloor cell6 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_3_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_3_4_g]
def cell6_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(83585296/44521:ℝ), (172632960/44521:ℝ), (89760000/44521:ℝ)]]
theorem cell6_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_3_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_3_4_g]
def cell6_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(1238053924000000/1982119441:ℝ), (7496099701376000/5946358323:ℝ), (3766077056000000/5946358323:ℝ)],
  ![(7341960719032000/5946358323:ℝ), (54954429951670088000/22066935736653:ℝ), (27594040965428000000/22066935736653:ℝ)],
  ![(3615903292000000/5946358323:ℝ), (27050624391428000000/22066935736653:ℝ), (13576494218000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 3 4 b ν := by
 have heq : pairedCleared cell6 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_3_4_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_3_4_g]
theorem cell6_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_3_4 hb hν
def cell6_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(17670421100712867/3812379062650000:ℝ)]]
theorem cell6_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 3 5) := by
 have heq : (-orderedLow cell6 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_3_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_3_5_g]
def cell6_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(149455881956894085811/84865464124120325:ℝ), (314753326674245282811/84865464124120325:ℝ), (6679790159993344140/3394618564964813:ℝ)]]
theorem cell6_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 3 5 ν := by
 have heq : mixedLowHigh cell6 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_3_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_3_5_g]
def cell6_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(89637620/44521:ℝ), (186947200/44521:ℝ), (98200000/44521:ℝ)]]
theorem cell6_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 5 false ν := by
 have heq : naturalFloor cell6 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_3_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_3_5_g]
def cell6_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(10159385381380/5006341929:ℝ), (63530826028400/15019025787:ℝ), (33353050400000/15019025787:ℝ)]]
theorem cell6_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 5 true ν := by
 have heq : naturalFloor cell6 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_3_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_3_5_g]
def cell6_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(89637620/44521:ℝ), (186947200/44521:ℝ), (98200000/44521:ℝ)]]
theorem cell6_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_3_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_3_5_g]
def cell6_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(1032172592000000/1982119441:ℝ), (6365668687720000/5946358323:ℝ), (3249324820000000/5946358323:ℝ)],
  ![(6563790723032000/5946358323:ℝ), (49845933912196672000/22066935736653:ℝ), (25344740591632000000/22066935736653:ℝ)],
  ![(3455377292000000/5946358323:ℝ), (26137157843632000000/22066935736653:ℝ), (13244861392000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 3 5 b ν := by
 have heq : pairedCleared cell6 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_3_5_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_3_5_g]
theorem cell6_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_3_5 hb hν
def cell6_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(81574980295917101/15249516250600000:ℝ)]]
theorem cell6_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 3 6) := by
 have heq : (-orderedLow cell6 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_3_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_3_6_g]
def cell6_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(692630268364872696633/339461856496481300:ℝ), (1462707726101996705933/339461856496481300:ℝ), (7782245422930395605/3394618564964813:ℝ)]]
theorem cell6_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 3 6 ν := by
 have heq : mixedLowHigh cell6 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_3_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_3_6_g]
def cell6_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(95689944/44521:ℝ), (201261440/44521:ℝ), (106640000/44521:ℝ)]]
theorem cell6_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 6 false ν := by
 have heq : naturalFloor cell6 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_3_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_3_6_g]
def cell6_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(95689944/44521:ℝ), (201261440/44521:ℝ), (106640000/44521:ℝ)]]
theorem cell6_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 3 6 true ν := by
 have heq : naturalFloor cell6 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_3_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_3_6_g]
def cell6_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(95689944/44521:ℝ), (201261440/44521:ℝ), (106640000/44521:ℝ)]]
theorem cell6_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_3_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_3_6_g]
def cell6_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(1162656300000000/1982119441:ℝ), (2398684264688000/1982119441:ℝ), (1228097528000000/1982119441:ℝ)],
  ![(2413345282344000/1982119441:ℝ), (6136136144782584000/2451881748517:ℝ), (3131765904204000000/2451881748517:ℝ)],
  ![(1246723764000000/1982119441:ℝ), (3159432646204000000/2451881748517:ℝ), (1607983174000000000/2451881748517:ℝ)]]
theorem cell6_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 3 6 b ν := by
 have heq : pairedCleared cell6 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_3_6_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_3_6_g]
theorem cell6_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_3_6 hb hν
def cell6_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(15057220157398903/9149709750360000:ℝ)]]
theorem cell6_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 4 1) := by
 have heq : (-orderedLow cell6 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_4_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_4_1_g]
def cell6_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(1717918316167172832/3394618564964813:ℝ), (11899206779543630740/10183855694894439:ℝ), (6786187253821690000/10183855694894439:ℝ)]]
theorem cell6_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 4 1 ν := by
 have heq : mixedLowHigh cell6 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_4_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_4_1_g]
def cell6_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(31832324/44521:ℝ), (70094240/44521:ℝ), (38440000/44521:ℝ)]]
theorem cell6_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 1 false ν := by
 have heq : naturalFloor cell6 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_4_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_4_1_g]
def cell6_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(3420063701476/5006341929:ℝ), (22716583681280/15019025787:ℝ), (12516468680000/15019025787:ℝ)]]
theorem cell6_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 1 true ν := by
 have heq : naturalFloor cell6 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_4_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_4_1_g]
def cell6_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(16988324/44521:ℝ), (41250240/44521:ℝ), (24440000/44521:ℝ)]]
theorem cell6_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_4_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_4_1_g]
def cell6_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(130483708000000/1982119441:ℝ), (1083584106344000/5946358323:ℝ), (688167764000000/5946358323:ℝ)],
  ![(1039601053376000/5946358323:ℝ), (9825276197576920000/22066935736653:ℝ), (5938723499020000000/22066935736653:ℝ)],
  ![(632289056000000/5946358323:ℝ), (5689722821020000000/22066935736653:ℝ), (3329419870000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 4 1 b ν := by
 have heq : pairedCleared cell6 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_4_1_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_4_1_g]
theorem cell6_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_4_1 hb hν
def cell6_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(53982994233095707/22874274375900000:ℝ)]]
theorem cell6_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 4 2) := by
 have heq : (-orderedLow cell6 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_4_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_4_2_g]
def cell6_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(10473923501442168872/10183855694894439:ℝ), (23254721986124173360/10183855694894439:ℝ), (12862269330241160000/10183855694894439:ℝ)]]
theorem cell6_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 4 2 ν := by
 have heq : mixedLowHigh cell6 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_4_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_4_2_g]
def cell6_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(139433944/133563:ℝ), (309005440/133563:ℝ), (56880000/44521:ℝ)]]
theorem cell6_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 2 false ν := by
 have heq : naturalFloor cell6 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_4_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_4_2_g]
def cell6_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(139433944/133563:ℝ), (309005440/133563:ℝ), (56880000/44521:ℝ)]]
theorem cell6_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 2 true ν := by
 have heq : naturalFloor cell6 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_4_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_4_2_g]
def cell6_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(132011944/133563:ℝ), (98194480/44521:ℝ), (163640000/133563:ℝ)]]
theorem cell6_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_4_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_4_2_g]
def cell6_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(516086296000000/1982119441:ℝ), (1161854950896000/1982119441:ℝ), (643125176000000/1982119441:ℝ)],
  ![(3287442817376000/5946358323:ℝ), (3016217706607056000/2451881748517:ℝ), (4963024228408000000/7355645245551:ℝ)],
  ![(1723323056000000/5946358323:ℝ), (1566295048136000000/2451881748517:ℝ), (2557882348000000000/7355645245551:ℝ)]]
theorem cell6_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 4 2 b ν := by
 have heq : pairedCleared cell6 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_4_2_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_4_2_g]
theorem cell6_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_4_2 hb hν
def cell6_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(266882809449615101/45748548751800000:ℝ)]]
theorem cell6_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 4 3) := by
 have heq : (-orderedLow cell6 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_4_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_4_3_g]
def cell6_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(20977402627961759248/10183855694894439:ℝ), (42080975203873655980/10183855694894439:ℝ), (7075259614750210000/3394618564964813:ℝ)]]
theorem cell6_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 4 3 ν := by
 have heq : mixedLowHigh cell6 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_4_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_4_3_g]
def cell6_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(251350916/133563:ℝ), (505708160/133563:ℝ), (85320000/44521:ℝ)]]
theorem cell6_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 3 false ν := by
 have heq : naturalFloor cell6 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_4_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_4_3_g]
def cell6_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(9580835684428/5006341929:ℝ), (57795874783840/15019025787:ℝ), (29233596040000/15019025787:ℝ)]]
theorem cell6_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 3 true ν := by
 have heq : naturalFloor cell6 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_4_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_4_3_g]
def cell6_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(251350916/133563:ℝ), (505708160/133563:ℝ), (85320000/44521:ℝ)]]
theorem cell6_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_4_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_4_3_g]
def cell6_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(1238053924000000/1982119441:ℝ), (7341960719032000/5946358323:ℝ), (3615903292000000/5946358323:ℝ)],
  ![(7496099701376000/5946358323:ℝ), (54954429951670088000/22066935736653:ℝ), (27050624391428000000/22066935736653:ℝ)],
  ![(3766077056000000/5946358323:ℝ), (27594040965428000000/22066935736653:ℝ), (13576494218000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 4 3 b ν := by
 have heq : pairedCleared cell6 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_4_3_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_4_3_g]
theorem cell6_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_4_3 hb hν
def cell6_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(1648783696525/228742743759:ℝ)]]
theorem cell6_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 4 4) := by
 have heq : (-orderedLow cell6 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_4_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_4_4_g]
def cell6_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(9320448417399373888/3394618564964813:ℝ), (56669439703936650640/10183855694894439:ℝ), (28871036142856840000/10183855694894439:ℝ)]]
theorem cell6_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 4 4 ν := by
 have heq : mixedLowHigh cell6 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_4_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_4_4_g]
def cell6_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(113273296/44521:ℝ), (230320960/44521:ℝ), (117760000/44521:ℝ)]]
theorem cell6_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 4 false ν := by
 have heq : naturalFloor cell6 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_4_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_4_4_g]
def cell6_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(13056367461904/5006341929:ℝ), (79557080693120/15019025787:ℝ), (40628282720000/15019025787:ℝ)]]
theorem cell6_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 4 true ν := by
 have heq : naturalFloor cell6 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_4_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_4_4_g]
def cell6_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(113273296/44521:ℝ), (230320960/44521:ℝ), (117760000/44521:ℝ)]]
theorem cell6_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_4_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_4_4_g]
def cell6_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(1623656512000000/1982119441:ℝ), (9743941465376000/5946358323:ℝ), (4857111056000000/5946358323:ℝ)],
  ![(9743941465376000/5946358323:ℝ), (72275113113556672000/22066935736653:ℝ), (36000973577632000000/22066935736653:ℝ)],
  ![(4857111056000000/5946358323:ℝ), (36000973577632000000/22066935736653:ℝ), (17920721392000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 4 4 b ν := by
 have heq : pairedCleared cell6 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_4_4_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_4_4_g]
theorem cell6_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_4_4 hb hν
def cell6_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(347797091383620899/45748548751800000:ℝ)]]
theorem cell6_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 4 5) := by
 have heq : (-orderedLow cell6 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_4_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_4_5_g]
def cell6_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(1026851582277233742189/339461856496481300:ℝ), (6278027228608711788067/1018385569489443900:ℝ), (32178401931667994395/10183855694894439:ℝ)]]
theorem cell6_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 4 5 ν := by
 have heq : mixedLowHigh cell6 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_4_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_4_5_g]
def cell6_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(119325620/44521:ℝ), (244635200/44521:ℝ), (126200000/44521:ℝ)]]
theorem cell6_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 5 false ν := by
 have heq : naturalFloor cell6 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_4_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_4_5_g]
def cell6_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(4552406864460/1668780643:ℝ), (27973732554800/5006341929:ℝ), (14416638800000/5006341929:ℝ)]]
theorem cell6_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 5 true ν := by
 have heq : naturalFloor cell6 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_4_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_4_5_g]
def cell6_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(119325620/44521:ℝ), (244635200/44521:ℝ), (126200000/44521:ℝ)]]
theorem cell6_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_4_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_4_5_g]
def cell6_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(1754140220000000/1982119441:ℝ), (10574325571720000/5946358323:ℝ), (5292078820000000/5946358323:ℝ)],
  ![(3473395529792000/1982119441:ℝ), (25884801501467752000/7355645245551:ℝ), (12947375374612000000/7355645245551:ℝ)],
  ![(1713968352000000/1982119441:ℝ), (4255412172204000000/2451881748517:ℝ), (2127523174000000000/2451881748517:ℝ)]]
theorem cell6_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 4 5 b ν := by
 have heq : pairedCleared cell6 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_4_5_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_4_5_g]
theorem cell6_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_4_5 hb hν
def cell6_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(79339628102676101/11437137187950000:ℝ)]]
theorem cell6_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 4 6) := by
 have heq : (-orderedLow cell6 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_4_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_4_6_g]
def cell6_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(221856423267134322611/84865464124120325:ℝ), (1380917174434647364933/254596392372360975:ℝ), (28858328722007242420/10183855694894439:ℝ)]]
theorem cell6_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 4 6 ν := by
 have heq : mixedLowHigh cell6 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_4_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_4_6_g]
def cell6_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(125377944/44521:ℝ), (258949440/44521:ℝ), (134640000/44521:ℝ)]]
theorem cell6_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 6 false ν := by
 have heq : naturalFloor cell6 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_4_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_4_6_g]
def cell6_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(14258073724856/5006341929:ℝ), (88285314635680/15019025787:ℝ), (45871550080000/15019025787:ℝ)]]
theorem cell6_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 4 6 true ν := by
 have heq : naturalFloor cell6 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_4_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_4_6_g]
def cell6_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(125377944/44521:ℝ), (258949440/44521:ℝ), (134640000/44521:ℝ)]]
theorem cell6_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_4_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_4_6_g]
def cell6_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(1548258888000000/1982119441:ℝ), (3147964852688000/1982119441:ℝ), (1591775528000000/1982119441:ℝ)],
  ![(9642016593376000/5946358323:ℝ), (72545908464929840000/22066935736653:ℝ), (36592825750040000000/22066935736653:ℝ)],
  ![(4981379056000000/5946358323:ℝ), (37385243002040000000/22066935736653:ℝ), (18816075740000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 4 6 b ν := by
 have heq : pairedCleared cell6 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_4_6_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_4_6_g]
theorem cell6_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_4_6 hb hν
def cell6_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(4622489759685863/1429642148493750:ℝ)]]
theorem cell6_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 5 1) := by
 have heq : (-orderedLow cell6 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_5_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_5_1_g]
def cell6_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(8521651352789696536/10183855694894439:ℝ), (18009979349439548780/10183855694894439:ℝ), (9529063419429430000/10183855694894439:ℝ)]]
theorem cell6_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 5 1 ν := by
 have heq : mixedLowHigh cell6 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_5_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_5_1_g]
def cell6_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(158780972/133563:ℝ), (327566720/133563:ℝ), (56440000/44521:ℝ)]]
theorem cell6_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 1 false ν := by
 have heq : naturalFloor cell6 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_5_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_5_1_g]
def cell6_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(5712413223476/5006341929:ℝ), (3937811471920/1668780643:ℝ), (6121046560000/5006341929:ℝ)]]
theorem cell6_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 1 true ν := by
 have heq : naturalFloor cell6 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_5_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_5_1_g]
def cell6_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(91982972/133563:ℝ), (197768720/133563:ℝ), (35440000/44521:ℝ)]]
theorem cell6_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_5_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_5_1_g]
def cell6_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(260967416000000/1982119441:ℝ), (586609743448000/1982119441:ℝ), (324320588000000/1982119441:ℝ)],
  ![(1869985159720000/5946358323:ℝ), (5068189196141168000/7355645245551:ℝ), (2745486490408000000/7355645245551:ℝ)],
  ![(1067256820000000/5946358323:ℝ), (2843625122408000000/7355645245551:ℝ), (1518802348000000000/7355645245551:ℝ)]]
theorem cell6_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 5 1 b ν := by
 have heq : pairedCleared cell6 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_5_1_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_5_1_g]
theorem cell6_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_5_1 hb hν
def cell6_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(36119911997828903/9149709750360000:ℝ)]]
theorem cell6_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 5 2) := by
 have heq : (-orderedLow cell6 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_5_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_5_2_g]
def cell6_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(4613939968576782304/3394618564964813:ℝ), (29365494556020091400/10183855694894439:ℝ), (15605145495848900000/10183855694894439:ℝ)]]
theorem cell6_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 5 2 ν := by
 have heq : mixedLowHigh cell6 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_5_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_5_2_g]
def cell6_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(67572648/44521:ℝ), (142096480/44521:ℝ), (74880000/44521:ℝ)]]
theorem cell6_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 2 false ν := by
 have heq : naturalFloor cell6 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_5_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_5_2_g]
def cell6_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(7518752044952/5006341929:ℝ), (47471072288560/15019025787:ℝ), (25034968360000/15019025787:ℝ)]]
theorem cell6_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 2 true ν := by
 have heq : naturalFloor cell6 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_5_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_5_2_g]
def cell6_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(57676648/44521:ℝ), (368601440/133563:ℝ), (196640000/133563:ℝ)]]
theorem cell6_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_5_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_5_2_g]
def cell6_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(646570004000000/1982119441:ℝ), (4161809976688000/5946358323:ℝ), (2214169528000000/5946358323:ℝ)],
  ![(4117826923720000/5946358323:ℝ), (32525250750310088000/22066935736653:ℝ), (17186808657428000000/22066935736653:ℝ)],
  ![(2158290820000000/5946358323:ℝ), (16937807979428000000/22066935736653:ℝ), (8900634218000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 5 2 b ν := by
 have heq : pairedCleared cell6 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_5_2_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_5_2_g]
theorem cell6_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_5_2 hb hν
def cell6_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(106639723834170707/22874274375900000:ℝ)]]
theorem cell6_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 5 3) := by
 have heq : (-orderedLow cell6 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_5_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_5_3_g]
def cell6_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(19161988458670997288/10183855694894439:ℝ), (40721009762600634020/10183855694894439:ℝ), (7227075857422790000/3394618564964813:ℝ)]]
theorem cell6_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 5 3 ν := by
 have heq : mixedLowHigh cell6 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_5_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_5_3_g]
def cell6_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(246654916/133563:ℝ), (525012160/133563:ℝ), (93320000/44521:ℝ)]]
theorem cell6_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 3 false ν := by
 have heq : naturalFloor cell6 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_5_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_5_3_g]
def cell6_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(9325090866428/5006341929:ℝ), (59501841329840/15019025787:ℝ), (31706797040000/15019025787:ℝ)]]
theorem cell6_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 3 true ν := by
 have heq : naturalFloor cell6 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_5_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_5_3_g]
def cell6_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(246654916/133563:ℝ), (525012160/133563:ℝ), (93320000/44521:ℝ)]]
theorem cell6_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_5_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_5_3_g]
def cell6_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(1032172592000000/1982119441:ℝ), (6563790723032000/5946358323:ℝ), (3455377292000000/5946358323:ℝ)],
  ![(6365668687720000/5946358323:ℝ), (49845933912196672000/22066935736653:ℝ), (26137157843632000000/22066935736653:ℝ)],
  ![(3249324820000000/5946358323:ℝ), (25344740591632000000/22066935736653:ℝ), (13244861392000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 5 3 b ν := by
 have heq : pairedCleared cell6 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_5_3_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_5_3_g]
theorem cell6_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_5_3 hb hν
def cell6_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(372196268651765101/45748548751800000:ℝ)]]
theorem cell6_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 5 4) := by
 have heq : (-orderedLow cell6 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_5_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_5_4_g]
def cell6_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(29665467585190587664/10183855694894439:ℝ), (59547262980350116640/10183855694894439:ℝ), (30044737086277840000/10183855694894439:ℝ)]]
theorem cell6_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 5 4 ν := by
 have heq : mixedLowHigh cell6 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_5_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_5_4_g]
def cell6_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(358571888/133563:ℝ), (721714880/133563:ℝ), (121760000/44521:ℝ)]]
theorem cell6_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 4 false ν := by
 have heq : naturalFloor cell6 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_5_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_5_4_g]
def cell6_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(13679524027904/5006341929:ℝ), (27516787797040/5006341929:ℝ), (13917365240000/5006341929:ℝ)]]
theorem cell6_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 4 true ν := by
 have heq : naturalFloor cell6 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_5_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_5_4_g]
def cell6_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(358571888/133563:ℝ), (721714880/133563:ℝ), (121760000/44521:ℝ)]]
theorem cell6_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_5_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_5_4_g]
def cell6_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(1754140220000000/1982119441:ℝ), (3473395529792000/1982119441:ℝ), (1713968352000000/1982119441:ℝ)],
  ![(10574325571720000/5946358323:ℝ), (25884801501467752000/7355645245551:ℝ), (4255412172204000000/2451881748517:ℝ)],
  ![(5292078820000000/5946358323:ℝ), (12947375374612000000/7355645245551:ℝ), (2127523174000000000/2451881748517:ℝ)]]
theorem cell6_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 5 4 b ν := by
 have heq : pairedCleared cell6 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_5_4_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_5_4_g]
theorem cell6_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_5_4 hb hν
def cell6_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(8701403970143/914970975036:ℝ)]]
theorem cell6_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 5 5) := by
 have heq : (-orderedLow cell6 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_5_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_5_5_g]
def cell6_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(12216470069808983360/3394618564964813:ℝ), (74135727480413111300/10183855694894439:ℝ), (37689994384884050000/10183855694894439:ℝ)]]
theorem cell6_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 5 5 ν := by
 have heq : mixedLowHigh cell6 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_5_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_5_5_g]
def cell6_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(149013620/44521:ℝ), (302323200/44521:ℝ), (154200000/44521:ℝ)]]
theorem cell6_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 5 false ν := by
 have heq : naturalFloor cell6 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_5_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_5_5_g]
def cell6_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(17155055805380/5006341929:ℝ), (104311569300400/15019025787:ℝ), (53146782400000/15019025787:ℝ)]]
theorem cell6_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 5 true ν := by
 have heq : naturalFloor cell6 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_5_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_5_5_g]
def cell6_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(149013620/44521:ℝ), (302323200/44521:ℝ), (154200000/44521:ℝ)]]
theorem cell6_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_5_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_5_5_g]
def cell6_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(2139742808000000/1982119441:ℝ), (12822167335720000/5946358323:ℝ), (6383112820000000/5946358323:ℝ)],
  ![(12822167335720000/5946358323:ℝ), (94975087666289840000/22066935736653:ℝ), (47249058736040000000/22066935736653:ℝ)],
  ![(6383112820000000/5946358323:ℝ), (47249058736040000000/22066935736653:ℝ), (23491935740000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 5 5 b ν := by
 have heq : pairedCleared cell6 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_5_5_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_5_5_g]
theorem cell6_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_5_5 hb hν
def cell6_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(453110550585770899/45748548751800000:ℝ)]]
theorem cell6_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 5 6) := by
 have heq : (-orderedLow cell6 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_5_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_5_6_g]
def cell6_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(1316453747518194689389/339461856496481300:ℝ), (8024656006256357854067/1018385569489443900:ℝ), (40997360173695204395/10183855694894439:ℝ)]]
theorem cell6_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 5 6 ν := by
 have heq : mixedLowHigh cell6 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_5_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_5_6_g]
def cell6_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(155065944/44521:ℝ), (316637440/44521:ℝ), (162640000/44521:ℝ)]]
theorem cell6_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 6 false ν := by
 have heq : naturalFloor cell6 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_5_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_5_6_g]
def cell6_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(17755908936856/5006341929:ℝ), (108675686271680/15019025787:ℝ), (55768416080000/15019025787:ℝ)]]
theorem cell6_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 5 6 true ν := by
 have heq : naturalFloor cell6 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_5_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_5_6_g]
def cell6_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(155065944/44521:ℝ), (316637440/44521:ℝ), (162640000/44521:ℝ)]]
theorem cell6_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_5_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_5_6_g]
def cell6_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(2270226516000000/1982119441:ℝ), (4550850480688000/1982119441:ℝ), (2272693528000000/1982119441:ℝ)],
  ![(13498412459720000/5946358323:ℝ), (100354379057136424000/22066935736653:ℝ), (50090211282244000000/22066935736653:ℝ)],
  ![(6667906820000000/5946358323:ℝ), (49546794708244000000/22066935736653:ℝ), (24718922914000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 5 6 b ν := by
 have heq : pairedCleared cell6 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_5_6_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_5_6_g]
theorem cell6_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_5_6 hb hν
def cell6_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(94557236828338037/15249516250600000:ℝ)]]
theorem cell6_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 6 1) := by
 have heq : (-orderedLow cell6 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_6_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_6_1_g]
def cell6_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(945826332472882936501/509192784744721950:ℝ), (629586163503119289067/169730928248240650:ℝ), (18899378583509076370/10183855694894439:ℝ)]]
theorem cell6_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 6 1 ν := by
 have heq : mixedLowHigh cell6 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_6_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_6_1_g]
def cell6_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(222064972/133563:ℝ), (444850720/133563:ℝ), (74440000/44521:ℝ)]]
theorem cell6_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 1 false ν := by
 have heq : naturalFloor cell6 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_6_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_6_1_g]
def cell6_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(2668254248492/1668780643:ℝ), (48164022813280/15019025787:ℝ), (24209810680000/15019025787:ℝ)]]
theorem cell6_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 1 true ν := by
 have heq : naturalFloor cell6 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_6_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_6_1_g]
def cell6_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(133000972/133563:ℝ), (271786720/133563:ℝ), (46440000/44521:ℝ)]]
theorem cell6_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_6_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_6_1_g]
def cell6_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(727816164000000/1982119441:ℝ), (4396889474344000/5946358323:ℝ), (2209475764000000/5946358323:ℝ)],
  ![(1384928128688000/1982119441:ℝ), (31071646409590088000/22066935736653:ℝ), (15624648363428000000/22066935736653:ℝ)],
  ![(649181528000000/1982119441:ℝ), (14583230433428000000/22066935736653:ℝ), (7342014218000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 6 1 b ν := by
 have heq : pairedCleared cell6 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_6_1_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_6_1_g]
theorem cell6_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_6_1 hb hν
def cell6_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(5275690239835367/953094765662500:ℝ)]]
theorem cell6_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 6 2) := by
 have heq : (-orderedLow cell6 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_6_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_6_2_g]
def cell6_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(17209716310018524952/10183855694894439:ℝ), (11825422375305336480/3394618564964813:ℝ), (18348021661456640000/10183855694894439:ℝ)]]
theorem cell6_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 6 2 ν := by
 have heq : mixedLowHigh cell6 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_6_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_6_2_g]
def cell6_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(266001944/133563:ℝ), (543573440/133563:ℝ), (92880000/44521:ℝ)]]
theorem cell6_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 2 false ν := by
 have heq : naturalFloor cell6 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_6_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_6_2_g]
def cell6_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(3270367188984/1668780643:ℝ), (60194791854560/15019025787:ℝ), (30881639360000/15019025787:ℝ)]]
theorem cell6_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 2 true ν := by
 have heq : naturalFloor cell6 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_6_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_6_2_g]
def cell6_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(214047944/133563:ℝ), (442619440/133563:ℝ), (229640000/133563:ℝ)]]
theorem cell6_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_6_2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_6_2_g]
def cell6_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(777053712000000/1982119441:ℝ), (4838055100688000/5946358323:ℝ), (2498963528000000/5946358323:ℝ)],
  ![(1649403676688000/1982119441:ℝ), (37904542141156672000/22066935736653:ℝ), (19484544629632000000/22066935736653:ℝ)],
  ![(864419528000000/1982119441:ℝ), (19778960525632000000/22066935736653:ℝ), (10127621392000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 6 2 b ν := by
 have heq : pairedCleared cell6 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_6_2_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_6_2_g]
theorem cell6_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_6_2 hb hν
def cell6_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(19060867946086301/3049903250120000:ℝ)]]
theorem cell6_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 6 3) := by
 have heq : (-orderedLow cell6 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_6_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_6_3_g]
def cell6_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(7509961620986391776/3394618564964813:ℝ), (15610594110832184020/3394618564964813:ℝ), (8141367912625370000/3394618564964813:ℝ)]]
theorem cell6_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 6 3 ν := by
 have heq : mixedLowHigh cell6 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_6_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_6_3_g]
def cell6_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(103312972/44521:ℝ), (214098720/44521:ℝ), (111320000/44521:ℝ)]]
theorem cell6_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 3 false ν := by
 have heq : naturalFloor cell6 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_6_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_6_3_g]
def cell6_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(103312972/44521:ℝ), (214098720/44521:ℝ), (111320000/44521:ℝ)]]
theorem cell6_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 3 true ν := by
 have heq : naturalFloor cell6 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_6_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_6_3_g]
def cell6_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(98364972/44521:ℝ), (613452160/133563:ℝ), (319960000/133563:ℝ)]]
theorem cell6_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_6_3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_6_3_g]
def cell6_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(1162656300000000/1982119441:ℝ), (2413345282344000/1982119441:ℝ), (1246723764000000/1982119441:ℝ)],
  ![(2398684264688000/1982119441:ℝ), (6136136144782584000/2451881748517:ℝ), (3159432646204000000/2451881748517:ℝ)],
  ![(1228097528000000/1982119441:ℝ), (3131765904204000000/2451881748517:ℝ), (1607983174000000000/2451881748517:ℝ)]]
theorem cell6_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 6 3 b ν := by
 have heq : pairedCleared cell6 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_6_3_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_6_3_g]
theorem cell6_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_6_3 hb hν
def cell6_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(53098817811748569/7624758125300000:ℝ)]]
theorem cell6_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 6 4) := by
 have heq : (-orderedLow cell6 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_6_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_6_4_g]
def cell6_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(27850053415899825704/10183855694894439:ℝ), (19395765846359031560/3394618564964813:ℝ), (30500185814295580000/10183855694894439:ℝ)]]
theorem cell6_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 6 4 ν := by
 have heq : mixedLowHigh cell6 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_6_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_6_4_g]
def cell6_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(353875888/133563:ℝ), (741018880/133563:ℝ), (129760000/44521:ℝ)]]
theorem cell6_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 4 false ν := by
 have heq : naturalFloor cell6 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_6_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_6_4_g]
def cell6_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(4474593069968/1668780643:ℝ), (84256329937120/15019025787:ℝ), (44225296720000/15019025787:ℝ)]]
theorem cell6_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 4 true ν := by
 have heq : naturalFloor cell6 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_6_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_6_4_g]
def cell6_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(353875888/133563:ℝ), (741018880/133563:ℝ), (129760000/44521:ℝ)]]
theorem cell6_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_6_4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_6_4_g]
def cell6_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(1548258888000000/1982119441:ℝ), (9642016593376000/5946358323:ℝ), (4981379056000000/5946358323:ℝ)],
  ![(3147964852688000/1982119441:ℝ), (72545908464929840000/22066935736653:ℝ), (37385243002040000000/22066935736653:ℝ)],
  ![(1591775528000000/1982119441:ℝ), (36592825750040000000/22066935736653:ℝ), (18816075740000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 6 4 b ν := by
 have heq : pairedCleared cell6 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_6_4_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_6_4_g]
theorem cell6_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_6_4 hb hν
def cell6_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(159169909284638367/15249516250600000:ℝ)]]
theorem cell6_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 6 5) := by
 have heq : (-orderedLow cell6 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_6_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_6_5_g]
def cell6_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(38353532542419416080/10183855694894439:ℝ), (25671183585608859100/3394618564964813:ℝ), (38863695328305050000/10183855694894439:ℝ)]]
theorem cell6_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 6 5 ν := by
 have heq : mixedLowHigh cell6 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_6_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_6_5_g]
def cell6_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(465792860/133563:ℝ), (937721600/133563:ℝ), (158200000/44521:ℝ)]]
theorem cell6_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 5 false ν := by
 have heq : naturalFloor cell6 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_6_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_6_5_g]
def cell6_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(5926070790460/1668780643:ℝ), (107304851998400/15019025787:ℝ), (54270595400000/15019025787:ℝ)]]
theorem cell6_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 5 true ν := by
 have heq : naturalFloor cell6 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_6_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_6_5_g]
def cell6_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(465792860/133563:ℝ), (937721600/133563:ℝ), (158200000/44521:ℝ)]]
theorem cell6_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_6_5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_6_5_g]
def cell6_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(2270226516000000/1982119441:ℝ), (13498412459720000/5946358323:ℝ), (6667906820000000/5946358323:ℝ)],
  ![(4550850480688000/1982119441:ℝ), (100354379057136424000/22066935736653:ℝ), (49546794708244000000/22066935736653:ℝ)],
  ![(2272693528000000/1982119441:ℝ), (50090211282244000000/22066935736653:ℝ), (24718922914000000000/22066935736653:ℝ)]]
theorem cell6_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 6 5 b ν := by
 have heq : pairedCleared cell6 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_6_5_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_6_5_g]
theorem cell6_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_6_5 hb hν
def cell6_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(1801278859031/152495162506:ℝ)]]
theorem cell6_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell6 6 6) := by
 have heq : (-orderedLow cell6 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell6_ordered_6_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordered_6_6_g]
def cell6_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(15112491722218592832/3394618564964813:ℝ), (30534005085629857320/3394618564964813:ℝ), (15502984208970420000/3394618564964813:ℝ)]]
theorem cell6_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell6 6 6 ν := by
 have heq : mixedLowHigh cell6 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_mixed_6_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_mixed_6_6_g]
def cell6_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(184753944/44521:ℝ), (374325440/44521:ℝ), (190640000/44521:ℝ)]]
theorem cell6_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 6 false ν := by
 have heq : naturalFloor cell6 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor0_6_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor0_6_6_g]
def cell6_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(7084581382952/1668780643:ℝ), (43022019302560/5006341929:ℝ), (21888427360000/5006341929:ℝ)]]
theorem cell6_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell6 6 6 true ν := by
 have heq : naturalFloor cell6 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_floor1_6_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_floor1_6_6_g]
def cell6_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(184753944/44521:ℝ), (374325440/44521:ℝ), (190640000/44521:ℝ)]]
theorem cell6_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell6_complement_floor_6_6_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement_floor_6_6_g]
def cell6_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(2655829104000000/1982119441:ℝ), (5300131068688000/1982119441:ℝ), (2636371528000000/1982119441:ℝ)],
  ![(5300131068688000/1982119441:ℝ), (39225020739674336000/7355645245551:ℝ), (19499047964816000000/7355645245551:ℝ)],
  ![(2636371528000000/1982119441:ℝ), (19499047964816000000/7355645245551:ℝ), (9687716696000000000/7355645245551:ℝ)]]
theorem cell6_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell6 6 6 b ν := by
 have heq : pairedCleared cell6 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell6_paired_cleared_6_6_g (1289/2000:ℝ) (3/4:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_cleared_6_6_g]
theorem cell6_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell6 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell6_paired_cleared_6_6 hb hν
def cell6_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(29760704659166101/45748548751800000:ℝ)]]
theorem cell6_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell6.q/K)+1+17/50*(cell6.q/cell6.priorL)+17/25*(cell6.q/cell6.priorL)*cell6.priorB) := by
 have heq : ((2-17/50-17/25)*(cell6.q/K)+1+17/50*(cell6.q/cell6.priorL)+17/25*(cell6.q/cell6.priorL)*cell6.priorB) = Record12518109.Bernstein.bsum 0 0 (29760704659166101/45748548751800000:ℝ) cell6_increment0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_increment0_g]
def cell6_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(203612526051/406838200000:ℝ)]]
theorem cell6_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell6.q/cell6.priorL)*(1-cell6.priorB)) := by
 have heq : (1+17/25*(cell6.q/cell6.priorL)*(1-cell6.priorB)) = Record12518109.Bernstein.bsum 0 0 (203612526051/406838200000:ℝ) cell6_increment1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_increment1_g]
def cell6_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(814256678153/1627352800000:ℝ)]]
theorem cell6_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell6.q/cell6.priorL)*(1-cell6.priorB)) := by
 have heq : (1+omega*(cell6.q/cell6.priorL)*(1-cell6.priorB)) = Record12518109.Bernstein.bsum 0 0 (814256678153/1627352800000:ℝ) cell6_increment2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_increment2_g]
def cell6_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(6161764/44521:ℝ), (36847360/133563:ℝ), (18896320/133563:ℝ)]]
theorem cell6_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (28787/18750:ℝ) cell6_high_increment_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_high_increment_g]
def cell6_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(164573926438/9393931:ℝ), (1152217460446/9393931:ℝ), (1855685940686/9393931:ℝ), (833886073562/9393931:ℝ)]]
theorem cell6_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (82286963219/4000000000:ℝ) cell6_three_gate0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_three_gate0_g]
def cell6_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(14342/211:ℝ), (39156/211:ℝ), (25658/211:ℝ)]]
theorem cell6_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (1513081/2000000:ℝ) cell6_three_gate1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_three_gate1_g]
def cell6_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(1955665887608/15019025787:ℝ), (3911074309640/15019025787:ℝ), (223942725020/1668780643:ℝ)]]
theorem cell6_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell6.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell6.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (97776857741/67469400000:ℝ) cell6_three_gate2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_three_gate2_g]
def cell6_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(642469/1349388:ℝ)]]
theorem cell6_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (1-cell6.q/K/3) := by
 have heq : (1-cell6.q/K/3) = Record12518109.Bernstein.bsum 0 0 (642469/1349388:ℝ) cell6_paired_margin0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_margin0_g]
def cell6_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(4751777/44532000:ℝ)]]
theorem cell6_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (gamma cell6-13/50) := by
 have heq : (gamma cell6-13/50) = Record12518109.Bernstein.bsum 0 0 (4751777/44532000:ℝ) cell6_paired_margin1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_margin1_g]
def cell6_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(7619/89064:ℝ)]]
theorem cell6_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (cell6.q-gamma cell6) := by
 have heq : (cell6.q-gamma cell6) = Record12518109.Bernstein.bsum 0 0 (7619/89064:ℝ) cell6_paired_margin2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_margin2_g]
def cell6_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(87641941/311724000:ℝ)]]
theorem cell6_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < (min (cell6.q+rho cell6.q) (3/4+rho (3/4))-gamma cell6) := by
 have heq : (min (cell6.q+rho cell6.q) (3/4+rho (3/4))-gamma cell6) = Record12518109.Bernstein.bsum 0 0 (87641941/311724000:ℝ) cell6_paired_margin3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_paired_margin3_g]
theorem cell6_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (1289/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell6 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell6_paired_1_1 hb hν
 · exact cell6_paired_1_2 hb hν
 · exact cell6_paired_1_3 hb hν
 · exact cell6_paired_1_4 hb hν
 · exact cell6_paired_1_5 hb hν
 · exact cell6_paired_1_6 hb hν
 · exact cell6_paired_2_1 hb hν
 · exact cell6_paired_2_2 hb hν
 · exact cell6_paired_2_3 hb hν
 · exact cell6_paired_2_4 hb hν
 · exact cell6_paired_2_5 hb hν
 · exact cell6_paired_2_6 hb hν
 · exact cell6_paired_3_1 hb hν
 · exact cell6_paired_3_2 hb hν
 · exact cell6_paired_3_3 hb hν
 · exact cell6_paired_3_4 hb hν
 · exact cell6_paired_3_5 hb hν
 · exact cell6_paired_3_6 hb hν
 · exact cell6_paired_4_1 hb hν
 · exact cell6_paired_4_2 hb hν
 · exact cell6_paired_4_3 hb hν
 · exact cell6_paired_4_4 hb hν
 · exact cell6_paired_4_5 hb hν
 · exact cell6_paired_4_6 hb hν
 · exact cell6_paired_5_1 hb hν
 · exact cell6_paired_5_2 hb hν
 · exact cell6_paired_5_3 hb hν
 · exact cell6_paired_5_4 hb hν
 · exact cell6_paired_5_5 hb hν
 · exact cell6_paired_5_6 hb hν
 · exact cell6_paired_6_1 hb hν
 · exact cell6_paired_6_2 hb hν
 · exact cell6_paired_6_3 hb hν
 · exact cell6_paired_6_4 hb hν
 · exact cell6_paired_6_5 hb hν
 · exact cell6_paired_6_6 hb hν
end
end Record12518109Admission
