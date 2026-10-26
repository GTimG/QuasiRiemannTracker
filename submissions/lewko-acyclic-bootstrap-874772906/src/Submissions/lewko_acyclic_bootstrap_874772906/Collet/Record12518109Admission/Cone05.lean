/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell05
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell5_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(44804027851/152495162506:ℝ)]]
theorem cell5_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 1 1) := by
 have heq : (-orderedLow cell5 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_1_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_1_1_g]
def cell5_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(150434575989154528/1153549656776637:ℝ), (345906298175502980/1153549656776637:ℝ), (200085920813455000/1153549656776637:ℝ)]]
theorem cell5_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 1 1 ν := by
 have heq : mixedLowHigh cell5 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_1_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_1_1_g]
def cell5_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(1422676/15129:ℝ), (3472160/15129:ℝ), (2110000/15129:ℝ)]]
theorem cell5_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 1 false ν := by
 have heq : naturalFloor cell5 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_1_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_1_1_g]
def cell5_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(179551343524/1701240921:ℝ), (428301269840/1701240921:ℝ), (255554890000/1701240921:ℝ)]]
theorem cell5_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 1 true ν := by
 have heq : naturalFloor cell5 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_1_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_1_1_g]
def cell5_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(1422676/15129:ℝ), (3472160/15129:ℝ), (2110000/15129:ℝ)]]
theorem cell5_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_1_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_1_1_g]
def cell5_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(5390494000000/228886641:ℝ), (12152993468000/228886641:ℝ), (6649153000000/228886641:ℝ)],
  ![(12152993468000/228886641:ℝ), (50283591407128000/428704678593:ℝ), (27110380388000000/428704678593:ℝ)],
  ![(6649153000000/228886641:ℝ), (27110380388000000/428704678593:ℝ), (14458160500000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 1 1 b ν := by
 have heq : pairedCleared cell5 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_1_1_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_1_1_g]
theorem cell5_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_1_1 hb hν
def cell5_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(5235677114910619/7624758125300000:ℝ)]]
theorem cell5_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 1 2) := by
 have heq : (-orderedLow cell5 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_1_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_1_2_g]
def cell5_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(12744221119281024587/38451655225887900:ℝ), (28312608094014504637/38451655225887900:ℝ), (317520004330811665/769033104517758:ℝ)]]
theorem cell5_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 1 2 ν := by
 have heq : mixedLowHigh cell5 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_1_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_1_2_g]
def cell5_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(2845352/15129:ℝ), (6944320/15129:ℝ), (4220000/15129:ℝ)]]
theorem cell5_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 2 false ν := by
 have heq : naturalFloor cell5 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_1_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_1_2_g]
def cell5_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(2845352/15129:ℝ), (6944320/15129:ℝ), (4220000/15129:ℝ)]]
theorem cell5_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 2 true ν := by
 have heq : naturalFloor cell5 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_1_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_1_2_g]
def cell5_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(2845352/15129:ℝ), (6944320/15129:ℝ), (4220000/15129:ℝ)]]
theorem cell5_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_1_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_1_2_g]
def cell5_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(4763039000000/76295547:ℝ), (10363955312000/76295547:ℝ), (613928000000/8477283:ℝ)],
  ![(27315866468000/228886641:ℝ), (111471976358692000/428704678593:ℝ), (59488049957000000/428704678593:ℝ)],
  ![(12913403000000/228886641:ℝ), (52826257207000000/428704678593:ℝ), (28242740750000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 1 2 b ν := by
 have heq : pairedCleared cell5 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_1_2_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_1_2_g]
theorem cell5_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_1_2 hb hν
def cell5_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(21253607451381/1906189531325000:ℝ)]]
theorem cell5_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 1 3) := by
 have heq : (-orderedLow cell5 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_1_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_1_3_g]
def cell5_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(484698078820355939/28838741419415925:ℝ), (5056280413837115089/28838741419415925:ℝ), (196705889281990010/1153549656776637:ℝ)]]
theorem cell5_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 1 3 ν := by
 have heq : mixedLowHigh cell5 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_1_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_1_3_g]
def cell5_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(1422676/5043:ℝ), (3472160/5043:ℝ), (2110000/5043:ℝ)]]
theorem cell5_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 3 false ν := by
 have heq : naturalFloor cell5 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_1_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_1_3_g]
def cell5_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(460362630572/1701240921:ℝ), (1133462409520/1701240921:ℝ), (693514670000/1701240921:ℝ)]]
theorem cell5_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 3 true ν := by
 have heq : naturalFloor cell5 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_1_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_1_3_g]
def cell5_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(1422676/5043:ℝ), (3472160/5043:ℝ), (2110000/5043:ℝ)]]
theorem cell5_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_1_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_1_3_g]
def cell5_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (14032516000/620289:ℝ), (13111000000/620289:ℝ)],
  ![(242097548000/5582601:ℝ), (1334677665616000/10456211673:ℝ), (851181086000000/10456211673:ℝ)],
  ![(239333000000/5582601:ℝ), (1088115586000000/10456211673:ℝ), (625331000000000/10456211673:ℝ)]]
theorem cell5_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 1 3 b ν := by
 have heq : pairedCleared cell5 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_1_3_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_1_3_g]
theorem cell5_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_1_3 hb hν
def cell5_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(5520412752262143/7624758125300000:ℝ)]]
theorem cell5_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 1 4) := by
 have heq : (-orderedLow cell5 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_1_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_1_4_g]
def cell5_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(25127998074209044717/115354965677663700:ℝ), (70572316119841676267/115354965677663700:ℝ), (945799949929505015/2307099313553274:ℝ)]]
theorem cell5_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 1 4 ν := by
 have heq : mixedLowHigh cell5 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_1_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_1_4_g]
def cell5_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(5690704/15129:ℝ), (13888640/15129:ℝ), (8440000/15129:ℝ)]]
theorem cell5_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 4 false ν := by
 have heq : naturalFloor cell5 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_1_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_1_4_g]
def cell5_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(600768274096/1701240921:ℝ), (1486042979360/1701240921:ℝ), (912494560000/1701240921:ℝ)]]
theorem cell5_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 4 true ν := by
 have heq : naturalFloor cell5 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_1_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_1_4_g]
def cell5_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(5690704/15129:ℝ), (13888640/15129:ℝ), (8440000/15129:ℝ)]]
theorem cell5_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_1_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_1_4_g]
def cell5_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(8898623000000/228886641:ℝ), (24116870872000/228886641:ℝ), (14764862000000/228886641:ℝ)],
  ![(25088872468000/228886641:ℝ), (115910169241820000/428704678593:ℝ), (67276094095000000/428704678593:ℝ)],
  ![(16076903000000/228886641:ℝ), (70328615845000000/428704678593:ℝ), (39423151250000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 1 4 b ν := by
 have heq : pairedCleared cell5 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_1_4_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_1_4_g]
theorem cell5_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_1_4 hb hν
def cell5_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(5477905537359381/3812379062650000:ℝ)]]
theorem cell5_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 1 5) := by
 have heq : (-orderedLow cell5 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_1_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_1_5_g]
def cell5_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(2684289101840925871/6408609204314650:ℝ), (6717750588018605121/6408609204314650:ℝ), (83232673405279445/128172184086293:ℝ)]]
theorem cell5_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 1 5 ν := by
 have heq : mixedLowHigh cell5 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_1_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_1_5_g]
def cell5_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(7113380/15129:ℝ), (17360800/15129:ℝ), (10550000/15129:ℝ)]]
theorem cell5_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 5 false ν := by
 have heq : naturalFloor cell5 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_1_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_1_5_g]
def cell5_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(247057972540/567080307:ℝ), (612874516400/567080307:ℝ), (377158150000/567080307:ℝ)]]
theorem cell5_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 5 true ν := by
 have heq : naturalFloor cell5 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_1_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_1_5_g]
def cell5_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(7113380/15129:ℝ), (17360800/15129:ℝ), (10550000/15129:ℝ)]]
theorem cell5_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_1_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_1_5_g]
def cell5_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(17797246000000/228886641:ℝ), (43055743340000/228886641:ℝ), (24691765000000/228886641:ℝ)],
  ![(40251745468000/228886641:ℝ), (177098554193384000/428704678593:ℝ), (99653763664000000/428704678593:ℝ)],
  ![(7447051000000/76295547:ℝ), (3557203432000000/15877951059:ℝ), (17735910500000000/142901559531:ℝ)]]
theorem cell5_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 1 5 b ν := by
 have heq : pairedCleared cell5 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_1_5_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_1_5_g]
theorem cell5_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_1_5 hb hν
def cell5_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(37563331412298809/7624758125300000:ℝ)]]
theorem cell5_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 1 6) := by
 have heq : (-orderedLow cell5 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_1_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_1_6_g]
def cell5_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(118703662387671286639/115354965677663700:ℝ), (237525853157685108089/115354965677663700:ℝ), (2431814198925555005/2307099313553274:ℝ)]]
theorem cell5_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 1 6 ν := by
 have heq : mixedLowHigh cell5 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_1_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_1_6_g]
def cell5_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(14726056/15129:ℝ), (29522960/15129:ℝ), (15160000/15129:ℝ)]]
theorem cell5_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 6 false ν := by
 have heq : naturalFloor cell5 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_1_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_1_6_g]
def cell5_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(1577638871144/1701240921:ℝ), (3168385929040/1701240921:ℝ), (1631576840000/1701240921:ℝ)]]
theorem cell5_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 1 6 true ν := by
 have heq : naturalFloor cell5 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_1_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_1_6_g]
def cell5_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(14726056/15129:ℝ), (29522960/15129:ℝ), (15160000/15129:ℝ)]]
theorem cell5_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_1_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_1_6_g]
def cell5_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(49883609000000/228886641:ℝ), (94547355808000/228886641:ℝ), (43983668000000/228886641:ℝ)],
  ![(100267358468000/228886641:ℝ), (356225516164948000/428704678593:ℝ), (165960828233000000/428704678593:ℝ)],
  ![(16756801000000/76295547:ℝ), (6619543129000000/15877951059:ℝ), (27793687250000000/142901559531:ℝ)]]
theorem cell5_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 1 6 b ν := by
 have heq : pairedCleared cell5 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_1_6_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_1_6_g]
theorem cell5_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_1_6 hb hν
def cell5_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(9262180350545381/7624758125300000:ℝ)]]
theorem cell5_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 2 1) := by
 have heq : (-orderedLow cell5 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_2_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_2_1_g]
def cell5_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(299150234122552528/1153549656776637:ℝ), (591844930654400980/1153549656776637:ℝ), (99102965052985000/384516552258879:ℝ)]]
theorem cell5_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 2 1 ν := by
 have heq : mixedLowHigh cell5 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_2_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_2_1_g]
def cell5_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(3078676/15129:ℝ), (2042720/5043:ℝ), (3110000/15129:ℝ)]]
theorem cell5_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 1 false ν := by
 have heq : naturalFloor cell5 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_2_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_2_1_g]
def cell5_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(3078676/15129:ℝ), (2042720/5043:ℝ), (3110000/15129:ℝ)]]
theorem cell5_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 1 true ν := by
 have heq : naturalFloor cell5 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_2_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_2_1_g]
def cell5_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(3078676/15129:ℝ), (2042720/5043:ℝ), (3110000/15129:ℝ)]]
theorem cell5_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_2_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_2_1_g]
def cell5_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(4763039000000/76295547:ℝ), (27315866468000/228886641:ℝ), (12913403000000/228886641:ℝ)],
  ![(10363955312000/76295547:ℝ), (111471976358692000/428704678593:ℝ), (52826257207000000/428704678593:ℝ)],
  ![(613928000000/8477283:ℝ), (59488049957000000/428704678593:ℝ), (28242740750000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 2 1 b ν := by
 have heq : pairedCleared cell5 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_2_1_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_2_1_g]
theorem cell5_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_2_1 hb hν
def cell5_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(197299190357/76247581253:ℝ)]]
theorem cell5_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 2 2) := by
 have heq : (-orderedLow cell5 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_2_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_2_2_g]
def cell5_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(872116030725785056/1153549656776637:ℝ), (1796792543869481960/1153549656776637:ℝ), (933904910397910000/1153549656776637:ℝ)]]
theorem cell5_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 2 2 ν := by
 have heq : mixedLowHigh cell5 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_2_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_2_2_g]
def cell5_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(3445784/5043:ℝ), (7145440/5043:ℝ), (3740000/5043:ℝ)]]
theorem cell5_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 2 false ν := by
 have heq : naturalFloor cell5 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_2_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_2_2_g]
def cell5_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1201570595048/1701240921:ℝ), (2486213447680/1701240921:ℝ), (1298252780000/1701240921:ℝ)]]
theorem cell5_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 2 true ν := by
 have heq : naturalFloor cell5 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_2_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_2_2_g]
def cell5_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(3445784/5043:ℝ), (7145440/5043:ℝ), (3740000/5043:ℝ)]]
theorem cell5_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_2_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_2_2_g]
def cell5_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(38846020000000/228886641:ℝ), (78593018936000/228886641:ℝ), (39520306000000/228886641:ℝ)],
  ![(78593018936000/228886641:ℝ), (297249099750256000/428704678593:ℝ), (149223066776000000/428704678593:ℝ)],
  ![(39520306000000/228886641:ℝ), (149223066776000000/428704678593:ℝ), (74804821000000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 2 2 b ν := by
 have heq : pairedCleared cell5 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_2_2_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_2_2_g]
theorem cell5_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_2_2 hb hν
def cell5_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(22725394758060619/7624758125300000:ℝ)]]
theorem cell5_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 2 3) := by
 have heq : (-orderedLow cell5 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_2_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_2_3_g]
def cell5_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(36800269610502042187/38451655225887900:ℝ), (76675482950480470637/38451655225887900:ℝ), (806732664053781665/769033104517758:ℝ)]]
theorem cell5_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 2 3 ν := by
 have heq : mixedLowHigh cell5 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_2_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_2_3_g]
def cell5_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(11760028/15129:ℝ), (24908480/15129:ℝ), (13330000/15129:ℝ)]]
theorem cell5_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 3 false ν := by
 have heq : naturalFloor cell5 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_2_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_2_3_g]
def cell5_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(1341976238572/1701240921:ℝ), (2838794017520/1701240921:ℝ), (1517232670000/1701240921:ℝ)]]
theorem cell5_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 3 true ν := by
 have heq : naturalFloor cell5 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_2_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_2_3_g]
def cell5_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(11760028/15129:ℝ), (24908480/15129:ℝ), (13330000/15129:ℝ)]]
theorem cell5_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_2_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_2_3_g]
def cell5_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(15914881000000/76295547:ℝ), (32510630468000/76295547:ℝ), (16482403000000/76295547:ℝ)],
  ![(93755891936000/228886641:ℝ), (358437484701820000/428704678593:ℝ), (181600736345000000/428704678593:ℝ)],
  ![(45784556000000/228886641:ℝ), (174938943595000000/428704678593:ℝ), (88589401250000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 2 3 b ν := by
 have heq : pairedCleared cell5 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_2_3_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_2_3_g]
theorem cell5_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_2_3 hb hν
def cell5_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(4393683018238881/1906189531325000:ℝ)]]
theorem cell5_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 2 4) := by
 have heq : (-orderedLow cell5 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_2_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_2_4_g]
def cell5_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(18526734447236119139/28838741419415925:ℝ), (41328436556186589589/28838741419415925:ℝ), (930524878866445010/1153549656776637:ℝ)]]
theorem cell5_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 2 4 ν := by
 have heq : mixedLowHigh cell5 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_2_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_2_4_g]
def cell5_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(13182704/15129:ℝ), (28380640/15129:ℝ), (15440000/15129:ℝ)]]
theorem cell5_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 4 false ν := by
 have heq : naturalFloor cell5 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_2_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_2_4_g]
def cell5_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(13182704/15129:ℝ), (28380640/15129:ℝ), (15440000/15129:ℝ)]]
theorem cell5_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 4 true ν := by
 have heq : naturalFloor cell5 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_2_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_2_4_g]
def cell5_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(13182704/15129:ℝ), (28380640/15129:ℝ), (15440000/15129:ℝ)]]
theorem cell5_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_2_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_2_4_g]
def cell5_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(11151842000000/76295547:ℝ), (7957558208000/25431849:ℝ), (12569704000000/76295547:ℝ)],
  ![(76366024936000/228886641:ℝ), (301687292633384000/428704678593:ℝ), (157011110914000000/428704678593:ℝ)],
  ![(42683806000000/228886641:ℝ), (166725425414000000/428704678593:ℝ), (85985231500000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 2 4 b ν := by
 have heq : pairedCleared cell5 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_2_4_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_2_4_g]
theorem cell5_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_2_4 hb hν
def cell5_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(23010130395412143/7624758125300000:ℝ)]]
theorem cell5_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 2 5) := by
 have heq : (-orderedLow cell5 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_2_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_2_5_g]
def cell5_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(97296143547872097517/115354965677663700:ℝ), (215660940689239574267/115354965677663700:ℝ), (2413437929098415015/2307099313553274:ℝ)]]
theorem cell5_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 2 5 ν := by
 have heq : mixedLowHigh cell5 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_2_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_2_5_g]
def cell5_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1622820/1681:ℝ), (3539200/1681:ℝ), (1950000/1681:ℝ)]]
theorem cell5_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 5 false ν := by
 have heq : naturalFloor cell5 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_2_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_2_5_g]
def cell5_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1622787525620/1701240921:ℝ), (3543955157200/1701240921:ℝ), (1955192450000/1701240921:ℝ)]]
theorem cell5_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 5 true ν := by
 have heq : naturalFloor cell5 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_2_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_2_5_g]
def cell5_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1622820/1681:ℝ), (3539200/1681:ℝ), (1950000/1681:ℝ)]]
theorem cell5_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_2_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_2_5_g]
def cell5_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(42354149000000/228886641:ℝ), (90556896340000/228886641:ℝ), (47636015000000/228886641:ℝ)],
  ![(91528897936000/228886641:ℝ), (362875677584948000/428704678593:ℝ), (189388780483000000/428704678593:ℝ)],
  ![(48948056000000/228886641:ℝ), (192441302233000000/428704678593:ℝ), (99769811750000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 2 5 b ν := by
 have heq : pairedCleared cell5 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_2_5_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_2_5_g]
theorem cell5_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_2_5 hb hν
def cell5_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(14222764358934381/3812379062650000:ℝ)]]
theorem cell5_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 2 6) := by
 have heq : (-orderedLow cell5 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_2_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_2_6_g]
def cell5_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(20080891551133286413/19225827612943950:ℝ), (44334689192288798363/19225827612943950:ℝ), (494304350077323335/384516552258879:ℝ)]]
theorem cell5_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 2 6 ν := by
 have heq : mixedLowHigh cell5 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_2_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_2_6_g]
def cell5_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(16028056/15129:ℝ), (35324960/15129:ℝ), (19660000/15129:ℝ)]]
theorem cell5_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 6 false ν := by
 have heq : naturalFloor cell5 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_2_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_2_6_g]
def cell5_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1763193169144/1701240921:ℝ), (3896535727040/1701240921:ℝ), (2174172340000/1701240921:ℝ)]]
theorem cell5_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 2 6 true ν := by
 have heq : naturalFloor cell5 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_2_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_2_6_g]
def cell5_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(16028056/15129:ℝ), (35324960/15129:ℝ), (19660000/15129:ℝ)]]
theorem cell5_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_2_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_2_6_g]
def cell5_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(51252772000000/228886641:ℝ), (109495768808000/228886641:ℝ), (57562918000000/228886641:ℝ)],
  ![(106691770936000/228886641:ℝ), (424064062536512000/428704678593:ℝ), (221766450052000000/428704678593:ℝ)],
  ![(18404102000000/76295547:ℝ), (72719059684000000/142901559531:ℝ), (37851464000000000/142901559531:ℝ)]]
theorem cell5_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 2 6 b ν := by
 have heq : pairedCleared cell5 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_2_6_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_2_6_g]
theorem cell5_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_2_6 hb hν
def cell5_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(72188828057667/3812379062650000:ℝ)]]
theorem cell5_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 3 1) := by
 have heq : (-orderedLow cell5 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_3_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_3_1_g]
def cell5_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(12872094399223572/128172184086293:ℝ), (445912169186755600/1153549656776637:ℝ), (334677518220850000/1153549656776637:ℝ)]]
theorem cell5_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 3 1 ν := by
 have heq : mixedLowHigh cell5 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_3_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_3_1_g]
def cell5_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(2290676/15129:ℝ), (2446720/5043:ℝ), (5110000/15129:ℝ)]]
theorem cell5_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 1 false ν := by
 have heq : naturalFloor cell5 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_3_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_3_1_g]
def cell5_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(238011375524/1701240921:ℝ), (787533301840/1701240921:ℝ), (556326890000/1701240921:ℝ)]]
theorem cell5_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 1 true ν := by
 have heq : naturalFloor cell5 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_3_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_3_1_g]
def cell5_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(417676/15129:ℝ), (3717160/15129:ℝ), (1120000/5043:ℝ)]]
theorem cell5_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_3_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_3_1_g]
def cell5_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (242097548000/5582601:ℝ), (239333000000/5582601:ℝ)],
  ![(14032516000/620289:ℝ), (1334677665616000/10456211673:ℝ), (1088115586000000/10456211673:ℝ)],
  ![(13111000000/620289:ℝ), (851181086000000/10456211673:ℝ), (625331000000000/10456211673:ℝ)]]
theorem cell5_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 3 1 b ν := by
 have heq : pairedCleared cell5 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_3_1_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_3_1_g]
theorem cell5_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_3_1 hb hν
def cell5_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(26751897993695381/7624758125300000:ℝ)]]
theorem cell5_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 3 2) := by
 have heq : (-orderedLow cell5 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_3_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_3_2_g]
def cell5_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(1020831688859183056/1153549656776637:ℝ), (2042731176348379960/1153549656776637:ℝ), (114569764971490000/128172184086293:ℝ)]]
theorem cell5_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 3 2 ν := by
 have heq : mixedLowHigh cell5 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_3_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_3_2_g]
def cell5_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(3997784/5043:ℝ), (24092320/15129:ℝ), (12220000/15129:ℝ)]]
theorem cell5_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 2 false ν := by
 have heq : naturalFloor cell5 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_3_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_3_2_g]
def cell5_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(1368213289048/1701240921:ℝ), (2747017641680/1701240921:ℝ), (1392414280000/1701240921:ℝ)]]
theorem cell5_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 2 true ν := by
 have heq : naturalFloor cell5 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_3_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_3_2_g]
def cell5_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(3997784/5043:ℝ), (24092320/15129:ℝ), (12220000/15129:ℝ)]]
theorem cell5_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_3_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_3_2_g]
def cell5_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(15914881000000/76295547:ℝ), (93755891936000/228886641:ℝ), (45784556000000/228886641:ℝ)],
  ![(32510630468000/76295547:ℝ), (358437484701820000/428704678593:ℝ), (174938943595000000/428704678593:ℝ)],
  ![(16482403000000/76295547:ℝ), (181600736345000000/428704678593:ℝ), (88589401250000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 3 2 b ν := by
 have heq : pairedCleared cell5 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_3_2_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_3_2_g]
theorem cell5_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_3_2 hb hν
def cell5_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(744392733577/152495162506:ℝ)]]
theorem cell5_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 3 3) := by
 have heq : (-orderedLow cell5 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_3_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_3_3_g]
def cell5_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1593797485462415584/1153549656776637:ℝ), (3247678789563460940/1153549656776637:ℝ), (1667723899982365000/1153549656776637:ℝ)]]
theorem cell5_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 3 3 ν := by
 have heq : mixedLowHigh cell5 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_3_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_3_3_g]
def cell5_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(19252028/15129:ℝ), (39400480/15129:ℝ), (20330000/15129:ℝ)]]
theorem cell5_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 3 false ν := by
 have heq : naturalFloor cell5 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_3_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_3_3_g]
def cell5_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(247065538508/189026769:ℝ), (504902847280/189026769:ℝ), (260105630000/189026769:ℝ)]]
theorem cell5_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 3 true ν := by
 have heq : naturalFloor cell5 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_3_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_3_3_g]
def cell5_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(19252028/15129:ℝ), (39400480/15129:ℝ), (20330000/15129:ℝ)]]
theorem cell5_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_3_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_3_3_g]
def cell5_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(72301546000000/228886641:ℝ), (145033044404000/228886641:ℝ), (72391459000000/228886641:ℝ)],
  ![(145033044404000/228886641:ℝ), (544214608093384000/428704678593:ℝ), (271335753164000000/428704678593:ℝ)],
  ![(72391459000000/228886641:ℝ), (271335753164000000/428704678593:ℝ), (135151481500000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 3 3 b ν := by
 have heq : pairedCleared cell5 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_3_3_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_3_3_g]
theorem cell5_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_3_3 hb hν
def cell5_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(40215112401210619/7624758125300000:ℝ)]]
theorem cell5_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 3 4) := by
 have heq : (-orderedLow cell5 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_3_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_3_4_g]
def cell5_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(20285439367241019929/12817218408629300:ℝ), (41679452602315478879/12817218408629300:ℝ), (431981774592250555/256344368172586:ℝ)]]
theorem cell5_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 3 4 ν := by
 have heq : mixedLowHigh cell5 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_3_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_3_4_g]
def cell5_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(6891568/5043:ℝ), (14290880/5043:ℝ), (7480000/5043:ℝ)]]
theorem cell5_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 4 false ν := by
 have heq : naturalFloor cell5 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_3_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_3_4_g]
def cell5_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2363995490096/1701240921:ℝ), (4896706195360/1701240921:ℝ), (2559930560000/1701240921:ℝ)]]
theorem cell5_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 4 true ν := by
 have heq : naturalFloor cell5 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_3_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_3_4_g]
def cell5_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(6891568/5043:ℝ), (14290880/5043:ℝ), (7480000/5043:ℝ)]]
theorem cell5_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_3_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_3_4_g]
def cell5_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(9022241000000/25431849:ℝ), (54657305624000/76295547:ℝ), (27439454000000/76295547:ℝ)],
  ![(160195917404000/228886641:ℝ), (605402993044948000/428704678593:ℝ), (303713422733000000/428704678593:ℝ)],
  ![(78655709000000/228886641:ℝ), (297051629983000000/428704678593:ℝ), (148936061750000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 3 4 b ν := by
 have heq : pairedCleared cell5 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_3_4_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_3_4_g]
theorem cell5_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_3_4 hb hν
def cell5_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(8766112429026381/1906189531325000:ℝ)]]
theorem cell5_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 3 5) := by
 have heq : (-orderedLow cell5 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_3_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_3_5_g]
def cell5_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(36568770815651882339/28838741419415925:ℝ), (77600592698536064089/28838741419415925:ℝ), (1664343868450900010/1153549656776637:ℝ)]]
theorem cell5_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 3 5 ν := by
 have heq : mixedLowHigh cell5 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_3_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_3_5_g]
def cell5_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(22097380/15129:ℝ), (46344800/15129:ℝ), (24550000/15129:ℝ)]]
theorem cell5_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 5 false ν := by
 have heq : naturalFloor cell5 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_3_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_3_5_g]
def cell5_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(2504401133620/1701240921:ℝ), (5249286765200/1701240921:ℝ), (2778910450000/1701240921:ℝ)]]
theorem cell5_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 5 true ν := by
 have heq : naturalFloor cell5 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_3_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_3_5_g]
def cell5_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(22097380/15129:ℝ), (46344800/15129:ℝ), (24550000/15129:ℝ)]]
theorem cell5_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_3_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_3_5_g]
def cell5_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(22303684000000/76295547:ℝ), (15339783260000/25431849:ℝ), (23526755000000/76295547:ℝ)],
  ![(142806050404000/228886641:ℝ), (548652800976512000/428704678593:ℝ), (279123797302000000/428704678593:ℝ)],
  ![(75554959000000/228886641:ℝ), (288838111802000000/428704678593:ℝ), (146331892000000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 3 5 b ν := by
 have heq : pairedCleared cell5 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_3_5_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_3_5_g]
theorem cell5_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_3_5 hb hν
def cell5_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(40499848038562143/7624758125300000:ℝ)]]
theorem cell5_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 3 6) := by
 have heq : (-orderedLow cell5 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_3_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_3_6_g]
def cell5_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(169464289021535150317/115354965677663700:ℝ), (360749565258637472267/115354965677663700:ℝ), (3881075908267325015/2307099313553274:ℝ)]]
theorem cell5_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 3 6 ν := by
 have heq : mixedLowHigh cell5 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_3_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_3_6_g]
def cell5_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(23520056/15129:ℝ), (49816960/15129:ℝ), (26660000/15129:ℝ)]]
theorem cell5_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 6 false ν := by
 have heq : naturalFloor cell5 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_3_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_3_6_g]
def cell5_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(23520056/15129:ℝ), (49816960/15129:ℝ), (26660000/15129:ℝ)]]
theorem cell5_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 3 6 true ν := by
 have heq : naturalFloor cell5 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_3_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_3_6_g]
def cell5_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(23520056/15129:ℝ), (49816960/15129:ℝ), (26660000/15129:ℝ)]]
theorem cell5_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_3_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_3_6_g]
def cell5_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(75809675000000/228886641:ℝ), (156996921808000/228886641:ℝ), (80507168000000/228886641:ℝ)],
  ![(157968923404000/228886641:ℝ), (609841185928076000/428704678593:ℝ), (311501466871000000/428704678593:ℝ)],
  ![(81819209000000/228886641:ℝ), (314553988621000000/428704678593:ℝ), (160116472250000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 3 6 b ν := by
 have heq : pairedCleared cell5 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_3_6_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_3_6_g]
theorem cell5_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_3_6 hb hν
def cell5_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(2439739395361743/1524951625060000:ℝ)]]
theorem cell5_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 4 1) := by
 have heq : (-orderedLow cell5 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_4_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_4_1_g]
def cell5_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(404519993019541768/1153549656776637:ℝ), (962570888807680220/1153549656776637:ℝ), (562665094415245000/1153549656776637:ℝ)]]
theorem cell5_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 4 1 ν := by
 have heq : mixedLowHigh cell5 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_4_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_4_1_g]
def cell5_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(7692676/15129:ℝ), (17242160/15129:ℝ), (9610000/15129:ℝ)]]
theorem cell5_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 1 false ν := by
 have heq : naturalFloor cell5 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_4_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_4_1_g]
def cell5_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(825888023524/1701240921:ℝ), (1863142949840/1701240921:ℝ), (1044059890000/1701240921:ℝ)]]
theorem cell5_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 1 true ν := by
 have heq : naturalFloor cell5 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_4_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_4_1_g]
def cell5_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(3946676/15129:ℝ), (9996160/15129:ℝ), (6110000/15129:ℝ)]]
theorem cell5_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_4_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_4_1_g]
def cell5_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(8898623000000/228886641:ℝ), (25088872468000/228886641:ℝ), (16076903000000/228886641:ℝ)],
  ![(24116870872000/228886641:ℝ), (115910169241820000/428704678593:ℝ), (70328615845000000/428704678593:ℝ)],
  ![(14764862000000/228886641:ℝ), (67276094095000000/428704678593:ℝ), (39423151250000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 4 1 b ν := by
 have heq : pairedCleared cell5 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_4_1_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_4_1_g]
theorem cell5_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_4_1 hb hν
def cell5_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(8817047649632667/3812379062650000:ℝ)]]
theorem cell5_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 4 2) := by
 have heq : (-orderedLow cell5 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_4_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_4_2_g]
def cell5_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(279176768109880892/384516552258879:ℝ), (1896798414880734580/1153549656776637:ℝ), (1068496507805305000/1153549656776637:ℝ)]]
theorem cell5_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 4 2 ν := by
 have heq : mixedLowHigh cell5 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_4_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_4_2_g]
def cell5_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(11205352/15129:ℝ), (25304320/15129:ℝ), (1580000/1681:ℝ)]]
theorem cell5_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 2 false ν := by
 have heq : naturalFloor cell5 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_4_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_4_2_g]
def cell5_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(11205352/15129:ℝ), (25304320/15129:ℝ), (1580000/1681:ℝ)]]
theorem cell5_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 2 true ν := by
 have heq : naturalFloor cell5 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_4_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_4_2_g]
def cell5_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(31743056/45387:ℝ), (72289960/45387:ℝ), (40910000/45387:ℝ)]]
theorem cell5_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_4_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_4_2_g]
def cell5_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(11151842000000/76295547:ℝ), (76366024936000/228886641:ℝ), (42683806000000/228886641:ℝ)],
  ![(7957558208000/25431849:ℝ), (301687292633384000/428704678593:ℝ), (166725425414000000/428704678593:ℝ)],
  ![(12569704000000/76295547:ℝ), (157011110914000000/428704678593:ℝ), (85985231500000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 4 2 b ν := by
 have heq : pairedCleared cell5 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_4_2_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_4_2_g]
theorem cell5_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_4_2 hb hν
def cell5_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(44241615636845381/7624758125300000:ℝ)]]
theorem cell5_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 4 3) := by
 have heq : (-orderedLow cell5 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_4_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_4_3_g]
def cell5_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(1742513143595813584/1153549656776637:ℝ), (3493617422042358940/1153549656776637:ℝ), (588315624775955000/384516552258879:ℝ)]]
theorem cell5_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 4 3 ν := by
 have heq : mixedLowHigh cell5 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_4_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_4_3_g]
def cell5_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(20908028/15129:ℝ), (42056480/15129:ℝ), (2370000/1681:ℝ)]]
theorem cell5_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 3 false ν := by
 have heq : naturalFloor cell5 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_4_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_4_3_g]
def cell5_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(2390232540572/1701240921:ℝ), (4804929819520/1701240921:ℝ), (2435112170000/1701240921:ℝ)]]
theorem cell5_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 3 true ν := by
 have heq : naturalFloor cell5 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_4_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_4_3_g]
def cell5_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(20908028/15129:ℝ), (42056480/15129:ℝ), (2370000/1681:ℝ)]]
theorem cell5_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_4_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_4_3_g]
def cell5_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(9022241000000/25431849:ℝ), (160195917404000/228886641:ℝ), (78655709000000/228886641:ℝ)],
  ![(54657305624000/76295547:ℝ), (605402993044948000/428704678593:ℝ), (297051629983000000/428704678593:ℝ)],
  ![(27439454000000/76295547:ℝ), (303713422733000000/428704678593:ℝ), (148936061750000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 4 3 b ν := by
 have heq : pairedCleared cell5 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_4_3_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_4_3_g]
theorem cell5_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_4_3 hb hν
def cell5_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(547093543220/76247581253:ℝ)]]
theorem cell5_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 4 4) := by
 have heq : (-orderedLow cell5 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_4_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_4_4_g]
def cell5_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(2315478940199046112/1153549656776637:ℝ), (4698565035257439920/1153549656776637:ℝ), (2401542889566820000/1153549656776637:ℝ)]]
theorem cell5_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 4 4 ν := by
 have heq : mixedLowHigh cell5 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_4_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_4_4_g]
def cell5_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(28166704/15129:ℝ), (57364640/15129:ℝ), (29440000/15129:ℝ)]]
theorem cell5_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 4 false ν := by
 have heq : naturalFloor cell5 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_4_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_4_4_g]
def cell5_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(3245609098096/1701240921:ℝ), (6602037803360/1701240921:ℝ), (3383648560000/1701240921:ℝ)]]
theorem cell5_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 4 true ν := by
 have heq : naturalFloor cell5 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_4_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_4_4_g]
def cell5_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(28166704/15129:ℝ), (57364640/15129:ℝ), (29440000/15129:ℝ)]]
theorem cell5_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_4_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_4_4_g]
def cell5_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(105757072000000/228886641:ℝ), (211473069872000/228886641:ℝ), (105262612000000/228886641:ℝ)],
  ![(211473069872000/228886641:ℝ), (791180116436512000/428704678593:ℝ), (393448439552000000/428704678593:ℝ)],
  ![(105262612000000/228886641:ℝ), (393448439552000000/428704678593:ℝ), (195498142000000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 4 4 b ν := by
 have heq : pairedCleared cell5 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_4_4_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_4_4_g]
theorem cell5_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_4_4 hb hν
def cell5_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(57704830044360619/7624758125300000:ℝ)]]
theorem cell5_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 4 5) := by
 have heq : (-orderedLow cell5 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_4_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_4_5_g]
def cell5_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(84912366592944077387/38451655225887900:ℝ), (173401232663412402637/38451655225887900:ℝ), (1785157983499721665/769033104517758:ℝ)]]
theorem cell5_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 4 5 ν := by
 have heq : mixedLowHigh cell5 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_4_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_4_5_g]
def cell5_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(29589380/15129:ℝ), (60836800/15129:ℝ), (31550000/15129:ℝ)]]
theorem cell5_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 5 false ν := by
 have heq : naturalFloor cell5 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_4_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_4_5_g]
def cell5_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(376223860180/189026769:ℝ), (772735374800/189026769:ℝ), (400292050000/189026769:ℝ)]]
theorem cell5_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 5 true ν := by
 have heq : naturalFloor cell5 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_4_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_4_5_g]
def cell5_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(29589380/15129:ℝ), (60836800/15129:ℝ), (31550000/15129:ℝ)]]
theorem cell5_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_4_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_4_5_g]
def cell5_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(38218565000000/76295547:ℝ), (76803980780000/76295547:ℝ), (12798835000000/25431849:ℝ)],
  ![(226635942872000/228886641:ℝ), (852368501388076000/428704678593:ℝ), (425826109121000000/428704678593:ℝ)],
  ![(111526862000000/228886641:ℝ), (419164316371000000/428704678593:ℝ), (209282722250000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 4 5 b ν := by
 have heq : pairedCleared cell5 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_4_5_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_4_5_g]
theorem cell5_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_4_5 hb hν
def cell5_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(13138541839813881/1906189531325000:ℝ)]]
theorem cell5_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 4 6) := by
 have heq : (-orderedLow cell5 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_4_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_4_6_g]
def cell5_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(54610807184067645539/28838741419415925:ℝ), (113872748840885538589/28838741419415925:ℝ), (2398162858035355010/1153549656776637:ℝ)]]
theorem cell5_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 4 6 ν := by
 have heq : mixedLowHigh cell5 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_4_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_4_6_g]
def cell5_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3445784/1681:ℝ), (7145440/1681:ℝ), (3740000/1681:ℝ)]]
theorem cell5_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 6 false ν := by
 have heq : naturalFloor cell5 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_4_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_4_6_g]
def cell5_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3526420385144/1701240921:ℝ), (7307198943040/1701240921:ℝ), (3821608340000/1701240921:ℝ)]]
theorem cell5_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 4 6 true ν := by
 have heq : naturalFloor cell5 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_4_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_4_6_g]
def cell5_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3445784/1681:ℝ), (7145440/1681:ℝ), (3740000/1681:ℝ)]]
theorem cell5_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_4_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_4_6_g]
def cell5_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(11151842000000/25431849:ℝ), (22722008312000/25431849:ℝ), (1277178000000/2825761:ℝ)],
  ![(209246075872000/228886641:ℝ), (795618309319640000/428704678593:ℝ), (401236483690000000/428704678593:ℝ)],
  ![(108426112000000/228886641:ℝ), (410950798190000000/428704678593:ℝ), (206678552500000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 4 6 b ν := by
 have heq : pairedCleared cell5 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_4_6_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_4_6_g]
theorem cell5_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_4_6 hb hν
def cell5_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(1515813518593881/476547382831250:ℝ)]]
theorem cell5_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 5 1) := by
 have heq : (-orderedLow cell5 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_5_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_5_1_g]
def cell5_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(693191136446071388/1153549656776637:ℝ), (493076536142868280/384516552258879:ℝ), (790652670609640000/1153549656776637:ℝ)]]
theorem cell5_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 5 1 ν := by
 have heq : mixedLowHigh cell5 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_5_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_5_1_g]
def cell5_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(1454964/1681:ℝ), (27144160/15129:ℝ), (14110000/15129:ℝ)]]
theorem cell5_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 1 false ν := by
 have heq : naturalFloor cell5 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_5_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_5_1_g]
def cell5_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(471254890508/567080307:ℝ), (979584199280/567080307:ℝ), (56733070000/63008923:ℝ)]]
theorem cell5_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 1 true ν := by
 have heq : naturalFloor cell5 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_5_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_5_1_g]
def cell5_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(2491892/5043:ℝ), (16275160/15129:ℝ), (8860000/15129:ℝ)]]
theorem cell5_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_5_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_5_1_g]
def cell5_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(17797246000000/228886641:ℝ), (40251745468000/228886641:ℝ), (7447051000000/76295547:ℝ)],
  ![(43055743340000/228886641:ℝ), (177098554193384000/428704678593:ℝ), (3557203432000000/15877951059:ℝ)],
  ![(24691765000000/228886641:ℝ), (99653763664000000/428704678593:ℝ), (17735910500000000/142901559531:ℝ)]]
theorem cell5_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 5 1 b ν := by
 have heq : pairedCleared cell5 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_5_1_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_5_1_g]
theorem cell5_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_5_1 hb hν
def cell5_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(5937682923991743/1524951625060000:ℝ)]]
theorem cell5_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 5 2) := by
 have heq : (-orderedLow cell5 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_5_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_5_2_g]
def cell5_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1126201447756172296/1153549656776637:ℝ), (2413457134501659200/1153549656776637:ℝ), (1296484083999700000/1153549656776637:ℝ)]]
theorem cell5_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 5 2 ν := by
 have heq : mixedLowHigh cell5 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_5_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_5_2_g]
def cell5_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(5535784/5043:ℝ), (11735440/5043:ℝ), (2080000/1681:ℝ)]]
theorem cell5_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 2 false ν := by
 have heq : naturalFloor cell5 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_5_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_5_2_g]
def cell5_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1847907275048/1701240921:ℝ), (3921055127680/1701240921:ℝ), (2086757780000/1701240921:ℝ)]]
theorem cell5_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 2 true ν := by
 have heq : naturalFloor cell5 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_5_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_5_2_g]
def cell5_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(42330056/45387:ℝ), (91126960/45387:ℝ), (49160000/45387:ℝ)]]
theorem cell5_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_5_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_5_2_g]
def cell5_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(42354149000000/228886641:ℝ), (91528897936000/228886641:ℝ), (48948056000000/228886641:ℝ)],
  ![(90556896340000/228886641:ℝ), (362875677584948000/428704678593:ℝ), (192441302233000000/428704678593:ℝ)],
  ![(47636015000000/228886641:ℝ), (189388780483000000/428704678593:ℝ), (99769811750000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 5 2 b ν := by
 have heq : pairedCleared cell5 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_5_2_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_5_2_g]
theorem cell5_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_5_2 hb hν
def cell5_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(17561906471207667/3812379062650000:ℝ)]]
theorem cell5_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 5 3) := by
 have heq : (-orderedLow cell5 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_5_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_5_3_g]
def cell5_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(519737253022091068/384516552258879:ℝ), (3347684660574713560/1153549656776637:ℝ), (1802315497389760000/1153549656776637:ℝ)]]
theorem cell5_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 5 3 ν := by
 have heq : mixedLowHigh cell5 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_5_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_5_3_g]
def cell5_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(6706676/5043:ℝ), (43268480/15129:ℝ), (23330000/15129:ℝ)]]
theorem cell5_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 3 false ν := by
 have heq : naturalFloor cell5 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_5_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_5_3_g]
def cell5_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(2282049878572/1701240921:ℝ), (4903357657520/1701240921:ℝ), (2641722670000/1701240921:ℝ)]]
theorem cell5_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 3 true ν := by
 have heq : naturalFloor cell5 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_5_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_5_3_g]
def cell5_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(6706676/5043:ℝ), (43268480/15129:ℝ), (23330000/15129:ℝ)]]
theorem cell5_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_5_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_5_3_g]
def cell5_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(22303684000000/76295547:ℝ), (142806050404000/228886641:ℝ), (75554959000000/228886641:ℝ)],
  ![(15339783260000/25431849:ℝ), (548652800976512000/428704678593:ℝ), (288838111802000000/428704678593:ℝ)],
  ![(23526755000000/76295547:ℝ), (279123797302000000/428704678593:ℝ), (146331892000000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 5 3 b ν := by
 have heq : pairedCleared cell5 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_5_3_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_5_3_g]
theorem cell5_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_5_3 hb hν
def cell5_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(61731333279995381/7624758125300000:ℝ)]]
theorem cell5_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 5 4) := by
 have heq : (-orderedLow cell5 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_5_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_5_4_g]
def cell5_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(2464194598332444112/1153549656776637:ℝ), (4944503667736337920/1153549656776637:ℝ), (832921954637440000/384516552258879:ℝ)]]
theorem cell5_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 5 4 ν := by
 have heq : mixedLowHigh cell5 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_5_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_5_4_g]
def cell5_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(29822704/15129:ℝ), (6668960/1681:ℝ), (30440000/15129:ℝ)]]
theorem cell5_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 4 false ν := by
 have heq : naturalFloor cell5 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_5_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_5_4_g]
def cell5_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(1137417264032/567080307:ℝ), (2287613999120/567080307:ℝ), (128807780000/63008923:ℝ)]]
theorem cell5_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 4 true ν := by
 have heq : naturalFloor cell5 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_5_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_5_4_g]
def cell5_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(29822704/15129:ℝ), (6668960/1681:ℝ), (30440000/15129:ℝ)]]
theorem cell5_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_5_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_5_4_g]
def cell5_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(38218565000000/76295547:ℝ), (226635942872000/228886641:ℝ), (111526862000000/228886641:ℝ)],
  ![(76803980780000/76295547:ℝ), (852368501388076000/428704678593:ℝ), (419164316371000000/428704678593:ℝ)],
  ![(12798835000000/25431849:ℝ), (425826109121000000/428704678593:ℝ), (209282722250000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 5 4 b ν := by
 have heq : pairedCleared cell5 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_5_4_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_5_4_g]
theorem cell5_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_5_4 hb hν
def cell5_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(1443981439303/152495162506:ℝ)]]
theorem cell5_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 5 5) := by
 have heq : (-orderedLow cell5 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_5_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_5_5_g]
def cell5_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(3037160394935676640/1153549656776637:ℝ), (6149451280951418900/1153549656776637:ℝ), (3135361879151275000/1153549656776637:ℝ)]]
theorem cell5_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 5 5 ν := by
 have heq : mixedLowHigh cell5 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_5_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_5_5_g]
def cell5_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(12360460/5043:ℝ), (25109600/5043:ℝ), (12850000/5043:ℝ)]]
theorem cell5_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 5 false ν := by
 have heq : naturalFloor cell5 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_5_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_5_5_g]
def cell5_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(4267628349620/1701240921:ℝ), (8659949981200/1701240921:ℝ), (4426346450000/1701240921:ℝ)]]
theorem cell5_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 5 true ν := by
 have heq : naturalFloor cell5 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_5_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_5_5_g]
def cell5_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(12360460/5043:ℝ), (25109600/5043:ℝ), (12850000/5043:ℝ)]]
theorem cell5_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_5_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_5_5_g]
def cell5_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(139212598000000/228886641:ℝ), (277913095340000/228886641:ℝ), (138133765000000/228886641:ℝ)],
  ![(277913095340000/228886641:ℝ), (1038145624779640000/428704678593:ℝ), (515561125940000000/428704678593:ℝ)],
  ![(138133765000000/228886641:ℝ), (515561125940000000/428704678593:ℝ), (255844802500000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 5 5 b ν := by
 have heq : pairedCleared cell5 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_5_5_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_5_5_g]
theorem cell5_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_5_5 hb hν
def cell5_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(75194547687510619/7624758125300000:ℝ)]]
theorem cell5_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 5 6) := by
 have heq : (-orderedLow cell5 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_5_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_5_6_g]
def cell5_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(108968415084165094987/38451655225887900:ℝ), (221764107519878368637/38451655225887900:ℝ), (2274370643222691665/769033104517758:ℝ)]]
theorem cell5_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 5 6 ν := by
 have heq : mixedLowHigh cell5 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_5_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_5_6_g]
def cell5_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(38504056/15129:ℝ), (78800960/15129:ℝ), (40660000/15129:ℝ)]]
theorem cell5_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 6 false ν := by
 have heq : naturalFloor cell5 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_5_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_5_6_g]
def cell5_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(4408033993144/1701240921:ℝ), (9012530551040/1701240921:ℝ), (4645326340000/1701240921:ℝ)]]
theorem cell5_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 5 6 true ν := by
 have heq : naturalFloor cell5 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_5_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_5_6_g]
def cell5_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(38504056/15129:ℝ), (78800960/15129:ℝ), (40660000/15129:ℝ)]]
theorem cell5_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_5_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_5_6_g]
def cell5_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(49370407000000/76295547:ℝ), (98950655936000/76295547:ℝ), (49353556000000/76295547:ℝ)],
  ![(293075968340000/228886641:ℝ), (1099334009731204000/428704678593:ℝ), (547938795509000000/428704678593:ℝ)],
  ![(144398015000000/228886641:ℝ), (541277002759000000/428704678593:ℝ), (269629382750000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 5 6 b ν := by
 have heq : pairedCleared cell5 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_5_6_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_5_6_g]
theorem cell5_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_5_6 hb hν
def cell5_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(46893396625757191/7624758125300000:ℝ)]]
theorem cell5_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 6 1) := by
 have heq : (-orderedLow cell5 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_6_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_6_1_g]
def cell5_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(26278217464791561961/19225827612943950:ℝ), (157324364948070607733/57677482838831850:ℝ), (1574408449701024985/1153549656776637:ℝ)]]
theorem cell5_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 6 1 ν := by
 have heq : mixedLowHigh cell5 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_6_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_6_1_g]
def cell5_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(18496676/15129:ℝ), (4116240/1681:ℝ), (18610000/15129:ℝ)]]
theorem cell5_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 1 false ν := by
 have heq : naturalFloor cell5 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_6_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_6_1_g]
def cell5_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(2001641319524/1701240921:ℝ), (4014362245840/1701240921:ℝ), (2019525890000/1701240921:ℝ)]]
theorem cell5_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 1 true ν := by
 have heq : naturalFloor cell5 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_6_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_6_1_g]
def cell5_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(11004676/15129:ℝ), (22554160/15129:ℝ), (1290000/1681:ℝ)]]
theorem cell5_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_6_1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_6_1_g]
def cell5_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(49883609000000/228886641:ℝ), (100267358468000/228886641:ℝ), (16756801000000/76295547:ℝ)],
  ![(94547355808000/228886641:ℝ), (356225516164948000/428704678593:ℝ), (6619543129000000/15877951059:ℝ)],
  ![(43983668000000/228886641:ℝ), (165960828233000000/428704678593:ℝ), (27793687250000000/142901559531:ℝ)]]
theorem cell5_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 6 1 b ν := by
 have heq : pairedCleared cell5 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_6_1_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_6_1_g]
theorem cell5_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_6_1 hb hν
def cell5_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(1304460435645378/238273691415625:ℝ)]]
theorem cell5_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 6 2) := by
 have heq : (-orderedLow cell5 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_6_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_6_2_g]
def cell5_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(1414872591182701916/1153549656776637:ℝ), (976705284707527940/384516552258879:ℝ), (1524471660194095000/1153549656776637:ℝ)]]
theorem cell5_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 6 2 ν := by
 have heq : mixedLowHigh cell5 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_6_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_6_2_g]
def cell5_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(22009352/15129:ℝ), (45108320/15129:ℝ), (2580000/1681:ℝ)]]
theorem cell5_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 2 false ν := by
 have heq : naturalFloor cell5 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_6_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_6_2_g]
def cell5_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(2435783923048/1701240921:ℝ), (4996664775680/1701240921:ℝ), (2574490780000/1701240921:ℝ)]]
theorem cell5_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 2 true ν := by
 have heq : naturalFloor cell5 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_6_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_6_2_g]
def cell5_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(52917056/45387:ℝ), (109963960/45387:ℝ), (57410000/45387:ℝ)]]
theorem cell5_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_6_2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_6_2_g]
def cell5_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(51252772000000/228886641:ℝ), (106691770936000/228886641:ℝ), (18404102000000/76295547:ℝ)],
  ![(109495768808000/228886641:ℝ), (424064062536512000/428704678593:ℝ), (72719059684000000/142901559531:ℝ)],
  ![(57562918000000/228886641:ℝ), (221766450052000000/428704678593:ℝ), (37851464000000000/142901559531:ℝ)]]
theorem cell5_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 6 2 b ν := by
 have heq : pairedCleared cell5 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_6_2_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_6_2_g]
theorem cell5_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_6_2 hb hν
def cell5_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(9435626452621743/1524951625060000:ℝ)]]
theorem cell5_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 6 3) := by
 have heq : (-orderedLow cell5 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_6_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_6_3_g]
def cell5_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(1847882902492802824/1153549656776637:ℝ), (3864343380195638180/1153549656776637:ℝ), (2030303073584155000/1153549656776637:ℝ)]]
theorem cell5_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 6 3 ν := by
 have heq : mixedLowHigh cell5 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_6_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_6_3_g]
def cell5_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(25522028/15129:ℝ), (53170480/15129:ℝ), (27830000/15129:ℝ)]]
theorem cell5_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 3 false ν := by
 have heq : naturalFloor cell5 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_6_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_6_3_g]
def cell5_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(25522028/15129:ℝ), (53170480/15129:ℝ), (27830000/15129:ℝ)]]
theorem cell5_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 3 true ν := by
 have heq : naturalFloor cell5 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_6_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_6_3_g]
def cell5_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(72820084/45387:ℝ), (152265440/45387:ℝ), (79990000/45387:ℝ)]]
theorem cell5_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_6_3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_6_3_g]
def cell5_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(75809675000000/228886641:ℝ), (157968923404000/228886641:ℝ), (81819209000000/228886641:ℝ)],
  ![(156996921808000/228886641:ℝ), (609841185928076000/428704678593:ℝ), (314553988621000000/428704678593:ℝ)],
  ![(80507168000000/228886641:ℝ), (311501466871000000/428704678593:ℝ), (160116472250000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 6 3 b ν := by
 have heq : pairedCleared cell5 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_6_3_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_6_3_g]
theorem cell5_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_6_3 hb hν
def cell5_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(26306765292782667/3812379062650000:ℝ)]]
theorem cell5_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 6 4) := by
 have heq : (-orderedLow cell5 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_6_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_6_4_g]
def cell5_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(253432579311433748/128172184086293:ℝ), (4798570906268692540/1153549656776637:ℝ), (2536134486974215000/1153549656776637:ℝ)]]
theorem cell5_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 6 4 ν := by
 have heq : mixedLowHigh cell5 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_6_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_6_4_g]
def cell5_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(29034704/15129:ℝ), (20410880/5043:ℝ), (32440000/15129:ℝ)]]
theorem cell5_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 4 false ν := by
 have heq : naturalFloor cell5 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_6_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_6_4_g]
def cell5_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(3304069130096/1701240921:ℝ), (6961269835360/1701240921:ℝ), (3684420560000/1701240921:ℝ)]]
theorem cell5_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 4 true ν := by
 have heq : naturalFloor cell5 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_6_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_6_4_g]
def cell5_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(29034704/15129:ℝ), (20410880/5043:ℝ), (32440000/15129:ℝ)]]
theorem cell5_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_6_4_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_6_4_g]
def cell5_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(11151842000000/25431849:ℝ), (209246075872000/228886641:ℝ), (108426112000000/228886641:ℝ)],
  ![(22722008312000/25431849:ℝ), (795618309319640000/428704678593:ℝ), (410950798190000000/428704678593:ℝ)],
  ![(1277178000000/2825761:ℝ), (401236483690000000/428704678593:ℝ), (206678552500000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 6 4 b ν := by
 have heq : pairedCleared cell5 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_6_4_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_6_4_g]
theorem cell5_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_6_4 hb hν
def cell5_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(79221050923145381/7624758125300000:ℝ)]]
theorem cell5_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 6 5) := by
 have heq : (-orderedLow cell5 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_6_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_6_5_g]
def cell5_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(3185876053069074640/1153549656776637:ℝ), (6395389913430316900/1153549656776637:ℝ), (359176094832975000/128172184086293:ℝ)]]
theorem cell5_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 6 5 ν := by
 have heq : mixedLowHigh cell5 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_6_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_6_5_g]
def cell5_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(12912460/5043:ℝ), (77984800/15129:ℝ), (39550000/15129:ℝ)]]
theorem cell5_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 5 false ν := by
 have heq : naturalFloor cell5 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_6_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_6_5_g]
def cell5_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(4434271043620/1701240921:ℝ), (8920754175200/1701240921:ℝ), (4520507950000/1701240921:ℝ)]]
theorem cell5_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 5 true ν := by
 have heq : naturalFloor cell5 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_6_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_6_5_g]
def cell5_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(12912460/5043:ℝ), (77984800/15129:ℝ), (39550000/15129:ℝ)]]
theorem cell5_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_6_5_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_6_5_g]
def cell5_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(49370407000000/76295547:ℝ), (293075968340000/228886641:ℝ), (144398015000000/228886641:ℝ)],
  ![(98950655936000/76295547:ℝ), (1099334009731204000/428704678593:ℝ), (541277002759000000/428704678593:ℝ)],
  ![(49353556000000/76295547:ℝ), (547938795509000000/428704678593:ℝ), (269629382750000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 6 5 b ν := by
 have heq : pairedCleared cell5 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_6_5_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_6_5_g]
theorem cell5_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_6_5 hb hν
def cell5_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(896887896083/76247581253:ℝ)]]
theorem cell5_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell5 6 6) := by
 have heq : (-orderedLow cell5 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell5_ordered_6_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_ordered_6_6_g]
def cell5_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(3758841849672307168/1153549656776637:ℝ), (7600337526645397880/1153549656776637:ℝ), (3869180868735730000/1153549656776637:ℝ)]]
theorem cell5_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell5 6 6 ν := by
 have heq : mixedLowHigh cell5 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_mixed_6_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_mixed_6_6_g]
def cell5_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(45996056/15129:ℝ), (93292960/15129:ℝ), (47660000/15129:ℝ)]]
theorem cell5_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 6 false ν := by
 have heq : naturalFloor cell5 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor0_6_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor0_6_6_g]
def cell5_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(1763215867048/567080307:ℝ), (3572620719680/567080307:ℝ), (1823014780000/567080307:ℝ)]]
theorem cell5_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell5 6 6 true ν := by
 have heq : naturalFloor cell5 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_floor1_6_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_floor1_6_6_g]
def cell5_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(45996056/15129:ℝ), (93292960/15129:ℝ), (47660000/15129:ℝ)]]
theorem cell5_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell5_complement_floor_6_6_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_complement_floor_6_6_g]
def cell5_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(172668124000000/228886641:ℝ), (344353120808000/228886641:ℝ), (171004918000000/228886641:ℝ)],
  ![(344353120808000/228886641:ℝ), (1285111133122768000/428704678593:ℝ), (637673812328000000/428704678593:ℝ)],
  ![(171004918000000/228886641:ℝ), (637673812328000000/428704678593:ℝ), (316191463000000000/428704678593:ℝ)]]
theorem cell5_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell5 6 6 b ν := by
 have heq : pairedCleared cell5 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell5_paired_cleared_6_6_g (627/1000:ℝ) (3/4:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_cleared_6_6_g]
theorem cell5_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) : 0 ≤ pairedGap cell5 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell5_paired_cleared_6_6 hb hν
def cell5_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(4928953096166381/7624758125300000:ℝ)]]
theorem cell5_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell5.q/K)+1+17/50*(cell5.q/cell5.priorL)+17/25*(cell5.q/cell5.priorL)*cell5.priorB) := by
 have heq : ((2-17/50-17/25)*(cell5.q/K)+1+17/50*(cell5.q/cell5.priorL)+17/25*(cell5.q/cell5.priorL)*cell5.priorB) = Record12518109.Bernstein.bsum 0 0 (4928953096166381/7624758125300000:ℝ) cell5_increment0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_increment0_g]
def cell5_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(101803636993/203419100000:ℝ)]]
theorem cell5_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell5.q/cell5.priorL)*(1-cell5.priorB)) := by
 have heq : (1+17/25*(cell5.q/cell5.priorL)*(1-cell5.priorB)) = Record12518109.Bernstein.bsum 0 0 (101803636993/203419100000:ℝ) cell5_increment1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_increment1_g]
def cell5_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(407120460979/813676400000:ℝ)]]
theorem cell5_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell5.q/cell5.priorL)*(1-cell5.priorB)) := by
 have heq : (1+omega*(cell5.q/cell5.priorL)*(1-cell5.priorB)) = Record12518109.Bernstein.bsum 0 0 (407120460979/813676400000:ℝ) cell5_increment2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_increment2_g]
def cell5_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(1546636/15129:ℝ), (1021360/5043:ℝ), (1577960/15129:ℝ)]]
theorem cell5_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (38301/25000:ℝ) cell5_high_increment_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_high_increment_g]
def cell5_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(4610667422/620289:ℝ), (44958791774/620289:ℝ), (79595327734/620289:ℝ), (36991832578/620289:ℝ)]]
theorem cell5_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (6916001133/500000000:ℝ) cell5_three_gate0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_three_gate0_g]
def cell5_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(711338/15129:ℝ), (2049484/15129:ℝ), (1398662/15129:ℝ)]]
theorem cell5_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (355669/500000:ℝ) cell5_three_gate1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_three_gate1_g]
def cell5_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(163809909064/1701240921:ℝ), (325622556920/1701240921:ℝ), (168617611540/1701240921:ℝ)]]
theorem cell5_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell5.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell5.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (8140563923/5622450000:ℝ) cell5_three_gate2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_three_gate2_g]
def cell5_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(53612/112449:ℝ)]]
theorem cell5_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (1-cell5.q/K/3) := by
 have heq : (1-cell5.q/K/3) = Record12518109.Bernstein.bsum 0 0 (53612/112449:ℝ) cell5_paired_margin0_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_margin0_g]
def cell5_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(327641/3746000:ℝ)]]
theorem cell5_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (gamma cell5-13/50) := by
 have heq : (gamma cell5-13/50) = Record12518109.Bernstein.bsum 0 0 (327641/3746000:ℝ) cell5_paired_margin1_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_margin1_g]
def cell5_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(1439/14984:ℝ)]]
theorem cell5_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (cell5.q-gamma cell5) := by
 have heq : (cell5.q-gamma cell5) = Record12518109.Bernstein.bsum 0 0 (1439/14984:ℝ) cell5_paired_margin2_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_margin2_g]
def cell5_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(7876903/26222000:ℝ)]]
theorem cell5_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4:ℝ)) : 0 < (min (cell5.q+rho cell5.q) (3/4+rho (3/4))-gamma cell5) := by
 have heq : (min (cell5.q+rho cell5.q) (3/4+rho (3/4))-gamma cell5) = Record12518109.Bernstein.bsum 0 0 (7876903/26222000:ℝ) cell5_paired_margin3_g (39/1000:ℝ) (1/25:ℝ) (627/1000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell5, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell5_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell5_paired_margin3_g]
theorem cell5_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (627/1000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (627/1000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell5 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell5_paired_1_1 hb hν
 · exact cell5_paired_1_2 hb hν
 · exact cell5_paired_1_3 hb hν
 · exact cell5_paired_1_4 hb hν
 · exact cell5_paired_1_5 hb hν
 · exact cell5_paired_1_6 hb hν
 · exact cell5_paired_2_1 hb hν
 · exact cell5_paired_2_2 hb hν
 · exact cell5_paired_2_3 hb hν
 · exact cell5_paired_2_4 hb hν
 · exact cell5_paired_2_5 hb hν
 · exact cell5_paired_2_6 hb hν
 · exact cell5_paired_3_1 hb hν
 · exact cell5_paired_3_2 hb hν
 · exact cell5_paired_3_3 hb hν
 · exact cell5_paired_3_4 hb hν
 · exact cell5_paired_3_5 hb hν
 · exact cell5_paired_3_6 hb hν
 · exact cell5_paired_4_1 hb hν
 · exact cell5_paired_4_2 hb hν
 · exact cell5_paired_4_3 hb hν
 · exact cell5_paired_4_4 hb hν
 · exact cell5_paired_4_5 hb hν
 · exact cell5_paired_4_6 hb hν
 · exact cell5_paired_5_1 hb hν
 · exact cell5_paired_5_2 hb hν
 · exact cell5_paired_5_3 hb hν
 · exact cell5_paired_5_4 hb hν
 · exact cell5_paired_5_5 hb hν
 · exact cell5_paired_5_6 hb hν
 · exact cell5_paired_6_1 hb hν
 · exact cell5_paired_6_2 hb hν
 · exact cell5_paired_6_3 hb hν
 · exact cell5_paired_6_4 hb hν
 · exact cell5_paired_6_5 hb hν
 · exact cell5_paired_6_6 hb hν
end
end Record12518109Admission
