/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell08
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell8_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(1347765182293/4574854875180:ℝ)]]
theorem cell8_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 1 1) := by
 have heq : (-orderedLow cell8 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_1_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_1_1_g]
def cell8_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(45351474940517445184/336564982141936071:ℝ), (34687626430054150300/112188327380645357:ℝ), (60057664278212750000/336564982141936071:ℝ)]]
theorem cell8_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 1 1 ν := by
 have heq : mixedLowHigh cell8 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_1_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_1_1_g]
def cell8_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(143135076/1471369:ℝ), (348249600/1471369:ℝ), (211000000/1471369:ℝ)]]
theorem cell8_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 1 false ν := by
 have heq : naturalFloor cell8 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_1_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_1_1_g]
def cell8_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(54168620033372/496361918043:ℝ), (42954838120400/165453972681:ℝ), (76681342000000/496361918043:ℝ)]]
theorem cell8_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 1 true ν := by
 have heq : naturalFloor cell8 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_1_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_1_1_g]
def cell8_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(143135076/1471369:ℝ), (348249600/1471369:ℝ), (211000000/1471369:ℝ)]]
theorem cell8_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_1_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_1_1_g]
def cell8_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(159722940200000000/6494780202483:ℝ), (120021370823880000/2164926734161:ℝ), (197037124900000000/6494780202483:ℝ)],
  ![(120021370823880000/2164926734161:ℝ), (4961612957636132880000/40512273976354793:ℝ), (2675769889585800000000/40512273976354793:ℝ)],
  ![(197037124900000000/6494780202483:ℝ), (2675769889585800000000/40512273976354793:ℝ), (4282333121500000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 1 1 b ν := by
 have heq : pairedCleared cell8 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_1_1_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_1_1_g]
theorem cell8_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_1_1 hb hν
def cell8_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(157285315404204917/228742743759000000:ℝ)]]
theorem cell8_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 1 2) := by
 have heq : (-orderedLow cell8 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_1_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_1_2_g]
def cell8_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(11506583305783829072263/33656498214193607100:ℝ), (8509076415317696119321/11218832738064535700:ℝ), (142898979258828081425/336564982141936071:ℝ)]]
theorem cell8_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 1 2 ν := by
 have heq : mixedLowHigh cell8 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_1_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_1_2_g]
def cell8_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(286270152/1471369:ℝ), (696499200/1471369:ℝ), (422000000/1471369:ℝ)]]
theorem cell8_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 2 false ν := by
 have heq : naturalFloor cell8 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_1_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_1_2_g]
def cell8_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(286270152/1471369:ℝ), (696499200/1471369:ℝ), (422000000/1471369:ℝ)]]
theorem cell8_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 2 true ν := by
 have heq : naturalFloor cell8 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_1_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_1_2_g]
def cell8_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(286270152/1471369:ℝ), (696499200/1471369:ℝ), (422000000/1471369:ℝ)]]
theorem cell8_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_1_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_1_2_g]
def cell8_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(424498791100000000/6494780202483:ℝ), (307808128547760000/2164926734161:ℝ), (492317499800000000/6494780202483:ℝ)],
  ![(811802713371640000/6494780202483:ℝ), (11029828665090999320000/40512273976354793:ℝ), (17658922885011100000000/121536821929064379:ℝ)],
  ![(127999958300000000/2164926734161:ℝ), (5229931999753700000000/40512273976354793:ℝ), (2796121560750000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 1 2 b ν := by
 have heq : pairedCleared cell8 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_1_2_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_1_2_g]
theorem cell8_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_1_2 hb hν
def cell8_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(747871222342583/57185685939750000:ℝ)]]
theorem cell8_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 1 3) := by
 have heq : (-orderedLow cell8 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_1_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_1_3_g]
def cell8_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(165035619450152763337/8414124553548401775:ℝ), (513949522566081683179/2804708184516133925:ℝ), (59111297715626924300/336564982141936071:ℝ)]]
theorem cell8_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 1 3 ν := by
 have heq : mixedLowHigh cell8 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_1_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_1_3_g]
def cell8_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(429405228/1471369:ℝ), (1044748800/1471369:ℝ), (633000000/1471369:ℝ)]]
theorem cell8_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 3 false ν := by
 have heq : naturalFloor cell8 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_1_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_1_3_g]
def cell8_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(138976133900116/496361918043:ℝ), (113686438961200/165453972681:ℝ), (208039526000000/496361918043:ℝ)]]
theorem cell8_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 3 true ν := by
 have heq : naturalFloor cell8 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_1_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_1_3_g]
def cell8_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(429405228/1471369:ℝ), (1044748800/1471369:ℝ), (633000000/1471369:ℝ)]]
theorem cell8_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_1_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_1_3_g]
def cell8_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (42021164280000/1784770597:ℝ), (39297300000000/1784770597:ℝ)],
  ![(242021164280000/5354311791:ℝ), (4443149896095520000/33398412181661:ℝ), (8504589749600000000/100195236544983:ℝ)],
  ![(239297300000000/5354311791:ℝ), (3623928083200000000/33398412181661:ℝ), (6250811000000000000/100195236544983:ℝ)]]
theorem cell8_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 1 3 b ν := by
 have heq : pairedCleared cell8 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_1_3_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_1_3_g]
theorem cell8_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_1_3 hb hν
def cell8_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(166086219181805249/228742743759000000:ℝ)]]
theorem cell8_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 1 4) := by
 have heq : (-orderedLow cell8 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_1_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_1_4_g]
def cell8_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(7631578289532695607211/33656498214193607100:ℝ), (7096111862576607822037/11218832738064535700:ℝ), (141952612696242255725/336564982141936071:ℝ)]]
theorem cell8_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 1 4 ν := by
 have heq : mixedLowHigh cell8 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_1_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_1_4_g]
def cell8_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(572540304/1471369:ℝ), (1392998400/1471369:ℝ), (844000000/1471369:ℝ)]]
theorem cell8_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 4 false ν := by
 have heq : naturalFloor cell8 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_1_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_1_4_g]
def cell8_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(181379890833488/496361918043:ℝ), (149052239381600/165453972681:ℝ), (273718618000000/496361918043:ℝ)]]
theorem cell8_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 4 true ν := by
 have heq : naturalFloor cell8 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_1_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_1_4_g]
def cell8_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(572540304/1471369:ℝ), (1392998400/1471369:ℝ), (844000000/1471369:ℝ)]]
theorem cell8_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_1_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_1_4_g]
def cell8_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(264775850900000000/6494780202483:ℝ), (238758429995520000/2164926734161:ℝ), (438283249600000000/6494780202483:ℝ)],
  ![(248436757723880000/2164926734161:ℝ), (11457756531418732200000/40512273976354793:ℝ), (6649226860839500000000/40512273976354793:ℝ)],
  ![(477230374900000000/6494780202483:ℝ), (6949986875089500000000/40512273976354793:ℝ), (11688265303750000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 1 4 b ν := by
 have heq : pairedCleared cell8 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_1_4_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_1_4_g]
theorem cell8_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_1_4 hb hν
def cell8_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(164590476737120083/114371371879500000:ℝ)]]
theorem cell8_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 1 5) := by
 have heq : (-orderedLow cell8 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_1_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_1_5_g]
def cell8_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(7301507050632390080537/16828249107096803550:ℝ), (6068212817444444455679/5609416369032267850:ℝ), (224793927676857587150/336564982141936071:ℝ)]]
theorem cell8_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 1 5 ν := by
 have heq : mixedLowHigh cell8 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_1_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_1_5_g]
def cell8_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(715675380/1471369:ℝ), (1741248000/1471369:ℝ), (1055000000/1471369:ℝ)]]
theorem cell8_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 5 false ν := by
 have heq : naturalFloor cell8 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_1_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_1_5_g]
def cell8_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(74594549255620/165453972681:ℝ), (61472679934000/55151324227:ℝ), (113132570000000/165453972681:ℝ)]]
theorem cell8_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 5 true ν := by
 have heq : naturalFloor cell8 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_1_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_1_5_g]
def cell8_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(715675380/1471369:ℝ), (1741248000/1471369:ℝ), (1055000000/1471369:ℝ)]]
theorem cell8_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_1_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_1_5_g]
def cell8_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(529551701800000000/6494780202483:ℝ), (426545187719400000/2164926734161:ℝ), (733563624500000000/6494780202483:ℝ)],
  ![(1197048874071640000/6494780202483:ℝ), (17525972238873598640000/40512273976354793:ℝ), (29579293798772200000000/121536821929064379:ℝ)],
  ![(221397708300000000/2164926734161:ℝ), (9504148985257400000000/40512273976354793:ℝ), (5264765621500000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 1 5 b ν := by
 have heq : pairedCleared cell8 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_1_5_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_1_5_g]
theorem cell8_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_1_5 hb hν
def cell8_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(1127052817381214087/228742743759000000:ℝ)]]
theorem cell8_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 1 6) := by
 have heq : (-orderedLow cell8 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_1_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_1_6_g]
def cell8_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(35616966952361874714937/33656498214193607100:ℝ), (23763767951647840000679/11218832738064535700:ℝ), (364820928597222918575/336564982141936071:ℝ)]]
theorem cell8_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 1 6 ν := by
 have heq : mixedLowHigh cell8 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_1_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_1_6_g]
def cell8_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(1472710456/1471369:ℝ), (2953397600/1471369:ℝ), (1516000000/1471369:ℝ)]]
theorem cell8_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 6 false ν := by
 have heq : naturalFloor cell8 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_1_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_1_6_g]
def cell8_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(473284728000232/496361918043:ℝ), (316928531322400/165453972681:ℝ), (489413552000000/496361918043:ℝ)]]
theorem cell8_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 1 6 true ν := by
 have heq : naturalFloor cell8 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_1_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_1_6_g]
def cell8_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(1472710456/1471369:ℝ), (2953397600/1471369:ℝ), (1516000000/1471369:ℝ)]]
theorem cell8_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_1_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_1_6_g]
def cell8_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(494534064900000000/2164926734161:ℝ), (937655159443280000/2164926734161:ℝ), (436512999800000000/2164926734161:ℝ)],
  ![(2982657116971640000/6494780202483:ℝ), (35302691494910465080000/40512273976354793:ℝ), (49375715050025900000000/121536821929064379:ℝ)],
  ![(1495750874900000000/6494780202483:ℝ), (17716467340425300000000/40512273976354793:ℝ), (24812490925250000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 1 6 b ν := by
 have heq : pairedCleared cell8 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_1_6_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_1_6_g]
theorem cell8_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_1_6 hb hν
def cell8_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(278197060573925083/228742743759000000:ℝ)]]
theorem cell8_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 2 1) := by
 have heq : (-orderedLow cell8 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_2_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_2_1_g]
def cell8_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(29923636682910791728/112188327380645357:ℝ), (177666268026552380900/336564982141936071:ℝ), (89241617906387750000/336564982141936071:ℝ)]]
theorem cell8_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 2 1 ν := by
 have heq : mixedLowHigh cell8 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_2_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_2_1_g]
def cell8_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(923485228/4414107:ℝ), (1838828800/4414107:ℝ), (311000000/1471369:ℝ)]]
theorem cell8_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 1 false ν := by
 have heq : naturalFloor cell8 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_2_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_2_1_g]
def cell8_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(923485228/4414107:ℝ), (1838828800/4414107:ℝ), (311000000/1471369:ℝ)]]
theorem cell8_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 1 true ν := by
 have heq : naturalFloor cell8 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_2_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_2_1_g]
def cell8_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(923485228/4414107:ℝ), (1838828800/4414107:ℝ), (311000000/1471369:ℝ)]]
theorem cell8_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_2_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_2_1_g]
def cell8_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(424498791100000000/6494780202483:ℝ), (811802713371640000/6494780202483:ℝ), (127999958300000000/2164926734161:ℝ)],
  ![(307808128547760000/2164926734161:ℝ), (11029828665090999320000/40512273976354793:ℝ), (5229931999753700000000/40512273976354793:ℝ)],
  ![(492317499800000000/6494780202483:ℝ), (17658922885011100000000/121536821929064379:ℝ), (2796121560750000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 2 1 b ν := by
 have heq : pairedCleared cell8 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_2_1_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_2_1_g]
theorem cell8_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_2_1 hb hν
def cell8_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(5922620057473/2287427437590:ℝ)]]
theorem cell8_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 2 2) := by
 have heq : (-orderedLow cell8 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_2_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_2_2_g]
def cell8_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(261921468439521570368/336564982141936071:ℝ), (179821399256703860600/112188327380645357:ℝ), (280235249187725500000/336564982141936071:ℝ)]]
theorem cell8_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 2 2 ν := by
 have heq : mixedLowHigh cell8 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_2_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_2_2_g]
def cell8_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1034790152/1471369:ℝ), (2145019200/1471369:ℝ), (1122000000/1471369:ℝ)]]
theorem cell8_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 2 false ν := by
 have heq : naturalFloor cell8 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_2_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_2_2_g]
def cell8_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(360848216506744/496361918043:ℝ), (248794301720800/165453972681:ℝ), (389505584000000/496361918043:ℝ)]]
theorem cell8_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 2 true ν := by
 have heq : naturalFloor cell8 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_2_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_2_2_g]
def cell8_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1034790152/1471369:ℝ), (2145019200/1471369:ℝ), (1122000000/1471369:ℝ)]]
theorem cell8_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_2_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_2_2_g]
def cell8_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(1159869166000000000/6494780202483:ℝ), (782165836847760000/2164926734161:ℝ), (1180020249800000000/6494780202483:ℝ)],
  ![(782165836847760000/2164926734161:ℝ), (29555129561749865760000/40512273976354793:ℝ), (14838693945171600000000/40512273976354793:ℝ)],
  ![(1180020249800000000/6494780202483:ℝ), (14838693945171600000000/40512273976354793:ℝ), (22318721243000000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 2 2 b ν := by
 have heq : pairedCleared cell8 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_2_2_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_2_2_g]
theorem cell8_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_2_2 hb hν
def cell8_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(682159062036854917/228742743759000000:ℝ)]]
theorem cell8_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 2 3) := by
 have heq : (-orderedLow cell8 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_2_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_2_3_g]
def cell8_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(33163582655684241590663/33656498214193607100:ℝ), (23022453697982667149321/11218832738064535700:ℝ), (363076564168340831425/336564982141936071:ℝ)]]
theorem cell8_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 2 3 ν := by
 have heq : mixedLowHigh cell8 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_2_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_2_3_g]
def cell8_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(1177925228/1471369:ℝ), (2493268800/1471369:ℝ), (1333000000/1471369:ℝ)]]
theorem cell8_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 3 false ν := by
 have heq : naturalFloor cell8 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_2_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_2_3_g]
def cell8_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(403251973440116/496361918043:ℝ), (284160102141200/165453972681:ℝ), (455184676000000/496361918043:ℝ)]]
theorem cell8_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 3 true ν := by
 have heq : naturalFloor cell8 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_2_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_2_3_g]
def cell8_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(1177925228/1471369:ℝ), (2493268800/1471369:ℝ), (1333000000/1471369:ℝ)]]
theorem cell8_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_2_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_2_3_g]
def cell8_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(474881672300000000/2164926734161:ℝ), (969952594571640000/2164926734161:ℝ), (491766874900000000/2164926734161:ℝ)],
  ![(2798236111443280000/6494780202483:ℝ), (35623345269204732200000/40512273976354793:ℝ), (54147695051768500000000/121536821929064379:ℝ)],
  ![(1366982999800000000/6494780202483:ℝ), (17392856055339500000000/40512273976354793:ℝ), (26424752803750000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 2 3 b ν := by
 have heq : pairedCleared cell8 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_2_3_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_2_3_g]
theorem cell8_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_2_3 hb hν
def cell8_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(131966307880505083/57185685939750000:ℝ)]]
theorem cell8_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 2 4) := by
 have heq : (-orderedLow cell8 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_2_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_2_4_g]
def cell8_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(5579285456925255892937/8414124553548401775:ℝ), (4142293843232324440679/2804708184516133925:ℝ), (279288882625139674300/336564982141936071:ℝ)]]
theorem cell8_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 2 4 ν := by
 have heq : mixedLowHigh cell8 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_2_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_2_4_g]
def cell8_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1321060304/1471369:ℝ), (2841518400/1471369:ℝ), (1544000000/1471369:ℝ)]]
theorem cell8_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 4 false ν := by
 have heq : naturalFloor cell8 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_2_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_2_4_g]
def cell8_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1321060304/1471369:ℝ), (2841518400/1471369:ℝ), (1544000000/1471369:ℝ)]]
theorem cell8_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 4 true ν := by
 have heq : naturalFloor cell8 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_2_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_2_4_g]
def cell8_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1321060304/1471369:ℝ), (2841518400/1471369:ℝ), (1544000000/1471369:ℝ)]]
theorem cell8_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_2_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_2_4_g]
def cell8_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(1000146225800000000/6494780202483:ℝ), (713116138295520000/2164926734161:ℝ), (1125985999600000000/6494780202483:ℝ)],
  ![(2280005070343280000/6494780202483:ℝ), (29983057428077598640000/40512273976354793:ℝ), (46804839533022200000000/121536821929064379:ℝ)],
  ![(424416916600000000/2164926734161:ℝ), (16558748820507400000000/40512273976354793:ℝ), (8539540621500000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 2 4 b ν := by
 have heq : pairedCleared cell8 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_2_4_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_2_4_g]
theorem cell8_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_2_4 hb hν
def cell8_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(690959965814455249/228742743759000000:ℝ)]]
theorem cell8_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 2 5) := by
 have heq : (-orderedLow cell8 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_2_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_2_5_g]
def cell8_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(29288577639433108125611/33656498214193607100:ℝ), (21609489145241578852037/11218832738064535700:ℝ), (362130197605755005725/336564982141936071:ℝ)]]
theorem cell8_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 2 5 ν := by
 have heq : mixedLowHigh cell8 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_2_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_2_5_g]
def cell8_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1464195380/1471369:ℝ), (3189768000/1471369:ℝ), (1755000000/1471369:ℝ)]]
theorem cell8_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 5 false ν := by
 have heq : naturalFloor cell8 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_2_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_2_5_g]
def cell8_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(488059487306860/496361918043:ℝ), (354891702982000/165453972681:ℝ), (586542860000000/496361918043:ℝ)]]
theorem cell8_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 5 true ν := by
 have heq : naturalFloor cell8 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_2_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_2_5_g]
def cell8_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1464195380/1471369:ℝ), (3189768000/1471369:ℝ), (1755000000/1471369:ℝ)]]
theorem cell8_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_2_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_2_5_g]
def cell8_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(1264922076700000000/6494780202483:ℝ), (900902896019400000/2164926734161:ℝ), (1421266374500000000/6494780202483:ℝ)],
  ![(910581223747760000/2164926734161:ℝ), (36051273135532465080000/40512273976354793:ℝ), (18812150916425300000000/40512273976354793:ℝ)],
  ![(1460213499800000000/6494780202483:ℝ), (19112910930675300000000/40512273976354793:ℝ), (29724653425250000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 2 5 b ν := by
 have heq : pairedCleared cell8 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_2_5_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_2_5_g]
theorem cell8_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_2_5 hb hν
def cell8_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(427027350053445083/114371371879500000:ℝ)]]
theorem cell8_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 2 6) := by
 have heq : (-orderedLow cell8 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_2_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_2_6_g]
def cell8_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(18130006725582596339737/16828249107096803550:ℝ), (13324901458776929970679/5609416369032267850:ℝ), (444971512586370337150/336564982141936071:ℝ)]]
theorem cell8_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 2 6 ν := by
 have heq : mixedLowHigh cell8 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_2_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_2_6_g]
def cell8_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1607330456/1471369:ℝ), (3538017600/1471369:ℝ), (1966000000/1471369:ℝ)]]
theorem cell8_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 6 false ν := by
 have heq : naturalFloor cell8 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_2_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_2_6_g]
def cell8_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(530463244240232/496361918043:ℝ), (390257503402400/165453972681:ℝ), (652221952000000/496361918043:ℝ)]]
theorem cell8_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 2 6 true ν := by
 have heq : naturalFloor cell8 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_2_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_2_6_g]
def cell8_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1607330456/1471369:ℝ), (3538017600/1471369:ℝ), (1966000000/1471369:ℝ)]]
theorem cell8_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_2_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_2_6_g]
def cell8_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(509899309200000000/2164926734161:ℝ), (1088689653743280000/2164926734161:ℝ), (572182249800000000/2164926734161:ℝ)],
  ![(3183482272143280000/6494780202483:ℝ), (42119488842987331520000/40512273976354793:ℝ), (66068065965529600000000/121536821929064379:ℝ)],
  ![(1647176249800000000/6494780202483:ℝ), (21667073040843200000000/40512273976354793:ℝ), (33830684986000000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 2 6 b ν := by
 have heq : pairedCleared cell8 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_2_6_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_2_6_g]
theorem cell8_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_2_6 hb hν
def cell8_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(866490549933527/38123790626500000:ℝ)]]
theorem cell8_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 3 1) := by
 have heq : (-orderedLow cell8 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_3_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_3_1_g]
def cell8_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(35713711810126441784/336564982141936071:ℝ), (134836718031039947500/336564982141936071:ℝ), (100469266149481250000/336564982141936071:ℝ)]]
theorem cell8_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 3 1 ν := by
 have heq : mixedLowHigh cell8 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_3_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_3_1_g]
def cell8_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(698645228/4414107:ℝ), (2213988800/4414107:ℝ), (511000000/1471369:ℝ)]]
theorem cell8_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 1 false ν := by
 have heq : naturalFloor cell8 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_3_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_3_1_g]
def cell8_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(72679525693372/496361918043:ℝ), (26397474446800/55151324227:ℝ), (166883192000000/496361918043:ℝ)]]
theorem cell8_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 1 true ν := by
 have heq : naturalFloor cell8 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_3_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_3_1_g]
def cell8_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(137255228/4414107:ℝ), (1127598800/4414107:ℝ), (336000000/1471369:ℝ)]]
theorem cell8_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_3_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_3_1_g]
def cell8_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (242021164280000/5354311791:ℝ), (239297300000000/5354311791:ℝ)],
  ![(42021164280000/1784770597:ℝ), (4443149896095520000/33398412181661:ℝ), (3623928083200000000/33398412181661:ℝ)],
  ![(39297300000000/1784770597:ℝ), (8504589749600000000/100195236544983:ℝ), (6250811000000000000/100195236544983:ℝ)]]
theorem cell8_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 3 1 b ν := by
 have heq : pairedCleared cell8 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_3_1_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_3_1_g]
theorem cell8_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_3_1 hb hν
def cell8_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(267690269068858361/76247581253000000:ℝ)]]
theorem cell8_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 3 2) := by
 have heq : (-orderedLow cell8 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_3_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_3_2_g]
def cell8_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(306340903547736500368/336564982141936071:ℝ), (613067586506501511800/336564982141936071:ℝ), (309419202815900500000/336564982141936071:ℝ)]]
theorem cell8_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 3 2 ν := by
 have heq : mixedLowHigh cell8 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_3_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_3_2_g]
def cell8_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(3598450456/4414107:ℝ), (7229137600/4414107:ℝ), (1222000000/1471369:ℝ)]]
theorem cell8_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 2 false ν := by
 have heq : naturalFloor cell8 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_3_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_3_2_g]
def cell8_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(410524586876744/496361918043:ℝ), (91588094503600/55151324227:ℝ), (417739159000000/496361918043:ℝ)]]
theorem cell8_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 2 true ν := by
 have heq : naturalFloor cell8 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_3_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_3_2_g]
def cell8_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(3598450456/4414107:ℝ), (7229137600/4414107:ℝ), (1222000000/1471369:ℝ)]]
theorem cell8_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_3_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_3_2_g]
def cell8_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(474881672300000000/2164926734161:ℝ), (2798236111443280000/6494780202483:ℝ), (1366982999800000000/6494780202483:ℝ)],
  ![(969952594571640000/2164926734161:ℝ), (35623345269204732200000/40512273976354793:ℝ), (17392856055339500000000/40512273976354793:ℝ)],
  ![(491766874900000000/2164926734161:ℝ), (54147695051768500000000/121536821929064379:ℝ), (26424752803750000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 3 2 b ν := by
 have heq : pairedCleared cell8 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_3_2_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_3_2_g]
theorem cell8_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_3_2 hb hν
def cell8_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(7447571682533/1524951625060:ℝ)]]
theorem cell8_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 3 3) := by
 have heq : (-orderedLow cell8 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_3_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_3_3_g]
def cell8_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(159497153979508565184/112188327380645357:ℝ), (324955172083353570900/112188327380645357:ℝ), (166804278032412750000/112188327380645357:ℝ)]]
theorem cell8_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 3 3 ν := by
 have heq : mixedLowHigh cell8 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_3_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_3_3_g]
def cell8_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1926445228/1471369:ℝ), (3941788800/1471369:ℝ), (2033000000/1471369:ℝ)]]
theorem cell8_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 3 false ν := by
 have heq : naturalFloor cell8 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_3_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_3_3_g]
def cell8_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(222509270993372/165453972681:ℝ), (151544588440400/55151324227:ℝ), (234109942000000/165453972681:ℝ)]]
theorem cell8_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 3 true ν := by
 have heq : naturalFloor cell8 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_3_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_3_3_g]
def cell8_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1926445228/1471369:ℝ), (3941788800/1471369:ℝ), (2033000000/1471369:ℝ)]]
theorem cell8_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_3_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_3_3_g]
def cell8_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(720005130600000000/2164926734161:ℝ), (1444310302871640000/2164926734161:ℝ), (721001124900000000/2164926734161:ℝ)],
  ![(1444310302871640000/2164926734161:ℝ), (54148646165863598640000/40512273976354793:ℝ), (27001618000757400000000/40512273976354793:ℝ)],
  ![(721001124900000000/2164926734161:ℝ), (27001618000757400000000/40512273976354793:ℝ), (13451703121500000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 3 3 b ν := by
 have heq : pairedCleared cell8 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_3_3_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_3_3_g]
theorem cell8_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_3_3 hb hν
def cell8_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(402344269556501639/76247581253000000:ℝ)]]
theorem cell8_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 3 4) := by
 have heq : (-orderedLow cell8 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_3_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_3_4_g]
def cell8_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(18273527335194884703021/11218832738064535700:ℝ), (37535830980647638179321/11218832738064535700:ℝ), (194418049692617860475/112188327380645357:ℝ)]]
theorem cell8_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 3 4 ν := by
 have heq : mixedLowHigh cell8 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_3_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_3_4_g]
def cell8_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2069580304/1471369:ℝ), (4290038400/1471369:ℝ), (2244000000/1471369:ℝ)]]
theorem cell8_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 4 false ν := by
 have heq : naturalFloor cell8 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_3_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_3_4_g]
def cell8_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(709931569913488/496361918043:ℝ), (489999565741600/165453972681:ℝ), (768008918000000/496361918043:ℝ)]]
theorem cell8_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 4 true ν := by
 have heq : naturalFloor cell8 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_3_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_3_4_g]
def cell8_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2069580304/1471369:ℝ), (4290038400/1471369:ℝ), (2244000000/1471369:ℝ)]]
theorem cell8_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_3_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_3_4_g]
def cell8_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(2424791242700000000/6494780202483:ℝ), (1632097060595520000/2164926734161:ℝ), (2458283749600000000/6494780202483:ℝ)],
  ![(4784669509514920000/6494780202483:ℝ), (60216861873318465080000/40512273976354793:ℝ), (90636467218525900000000/121536821929064379:ℝ)],
  ![(2349966124700000000/6494780202483:ℝ), (29555780110925300000000/40512273976354793:ℝ), (44461140925250000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 3 4 b ν := by
 have heq : pairedCleared cell8 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_3_4_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_3_4_g]
theorem cell8_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_3_4 hb hν
def cell8_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(87728248179555861/19061895313250000:ℝ)]]
theorem cell8_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 3 5) := by
 have heq : (-orderedLow cell8 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_3_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_3_5_g]
def cell8_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(3664511764800119674179/2804708184516133925:ℝ), (7770638163898567198179/2804708184516133925:ℝ), (166488822511550808100/112188327380645357:ℝ)]]
theorem cell8_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 3 5 ν := by
 have heq : mixedLowHigh cell8 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_3_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_3_5_g]
def cell8_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(2212715380/1471369:ℝ), (4638288000/1471369:ℝ), (2455000000/1471369:ℝ)]]
theorem cell8_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 5 false ν := by
 have heq : naturalFloor cell8 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_3_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_3_5_g]
def cell8_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(752335326846860/496361918043:ℝ), (525365366162000/165453972681:ℝ), (833688010000000/496361918043:ℝ)]]
theorem cell8_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 5 true ν := by
 have heq : naturalFloor cell8 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_3_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_3_5_g]
def cell8_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(2212715380/1471369:ℝ), (4638288000/1471369:ℝ), (2455000000/1471369:ℝ)]]
theorem cell8_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_3_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_3_5_g]
def cell8_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(2000292451600000000/6494780202483:ℝ), (1375260604319400000/2164926734161:ℝ), (2108969124500000000/6494780202483:ℝ)],
  ![(4266438468414920000/6494780202483:ℝ), (54576574032191331520000/40512273976354793:ℝ), (83293611699779600000000/121536821929064379:ℝ)],
  ![(2256233874700000000/6494780202483:ℝ), (28721672876093200000000/40512273976354793:ℝ), (43655009986000000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 3 5 b ν := by
 have heq : pairedCleared cell8 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_3_5_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_3_5_g]
theorem cell8_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_3_5 hb hν
def cell8_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(405277904149035083/76247581253000000:ℝ)]]
theorem cell8_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 3 6) := by
 have heq : (-orderedLow cell8 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_3_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_3_6_g]
def cell8_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(16981858996444506881337/11218832738064535700:ℝ), (36122866427906549882037/11218832738064535700:ℝ), (194102594171755918575/112188327380645357:ℝ)]]
theorem cell8_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 3 6 ν := by
 have heq : mixedLowHigh cell8 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_3_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_3_6_g]
def cell8_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2355850456/1471369:ℝ), (4986537600/1471369:ℝ), (2666000000/1471369:ℝ)]]
theorem cell8_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 6 false ν := by
 have heq : naturalFloor cell8 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_3_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_3_6_g]
def cell8_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2355850456/1471369:ℝ), (4986537600/1471369:ℝ), (2666000000/1471369:ℝ)]]
theorem cell8_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 3 6 true ν := by
 have heq : naturalFloor cell8 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_3_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_3_6_g]
def cell8_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2355850456/1471369:ℝ), (4986537600/1471369:ℝ), (2666000000/1471369:ℝ)]]
theorem cell8_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_3_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_3_6_g]
def cell8_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(755022767500000000/2164926734161:ℝ), (1563047362043280000/2164926734161:ℝ), (801416499800000000/2164926734161:ℝ)],
  ![(1572725689771640000/2164926734161:ℝ), (60644789739646197960000/40512273976354793:ℝ), (30975074972011100000000/40512273976354793:ℝ)],
  ![(814398874900000000/2164926734161:ℝ), (31275834986261100000000/40512273976354793:ℝ), (15920347182250000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 3 6 b ν := by
 have heq : pairedCleared cell8 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_3_6_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_3_6_g]
theorem cell8_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_3_6 hb hν
def cell8_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(73395591127963249/45748548751800000:ℝ)]]
theorem cell8_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 4 1) := by
 have heq : (-orderedLow cell8 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_4_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_4_1_g]
def cell8_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(122081683965170608384/336564982141936071:ℝ), (96539341456309204700/112188327380645357:ℝ), (168882600332324750000/336564982141936071:ℝ)]]
theorem cell8_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 4 1 ν := by
 have heq : mixedLowHigh cell8 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_4_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_4_1_g]
def cell8_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(771835076/1471369:ℝ), (1726949600/1471369:ℝ), (961000000/1471369:ℝ)]]
theorem cell8_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 1 false ν := by
 have heq : naturalFloor cell8 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_4_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_4_1_g]
def cell8_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(248611384283372/496361918043:ℝ), (186604717870400/165453972681:ℝ), (313188217000000/496361918043:ℝ)]]
theorem cell8_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 1 true ν := by
 have heq : naturalFloor cell8 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_4_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_4_1_g]
def cell8_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(397575076/1471369:ℝ), (1002689600/1471369:ℝ), (611000000/1471369:ℝ)]]
theorem cell8_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_4_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_4_1_g]
def cell8_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(264775850900000000/6494780202483:ℝ), (248436757723880000/2164926734161:ℝ), (477230374900000000/6494780202483:ℝ)],
  ![(238758429995520000/2164926734161:ℝ), (11457756531418732200000/40512273976354793:ℝ), (6949986875089500000000/40512273976354793:ℝ)],
  ![(438283249600000000/6494780202483:ℝ), (6649226860839500000000/40512273976354793:ℝ), (11688265303750000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 4 1 b ν := by
 have heq : pairedCleared cell8 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_4_1_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_4_1_g]
theorem cell8_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_4_1 hb hν
def cell8_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(265036344966125581/114371371879500000:ℝ)]]
theorem cell8_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 4 2) := by
 have heq : (-orderedLow cell8 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_4_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_4_2_g]
def cell8_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(84094568436376855656/112188327380645357:ℝ), (570238036510989078400/336564982141936071:ℝ), (320646851058994000000/336564982141936071:ℝ)]]
theorem cell8_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 4 2 ν := by
 have heq : mixedLowHigh cell8 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_4_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_4_2_g]
def cell8_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(3373610456/4414107:ℝ), (7604297600/4414107:ℝ), (1422000000/1471369:ℝ)]]
theorem cell8_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 2 false ν := by
 have heq : naturalFloor cell8 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_4_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_4_2_g]
def cell8_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(3373610456/4414107:ℝ), (7604297600/4414107:ℝ), (1422000000/1471369:ℝ)]]
theorem cell8_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 2 true ν := by
 have heq : naturalFloor cell8 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_4_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_4_2_g]
def cell8_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(1062160152/1471369:ℝ), (7242167600/4414107:ℝ), (4091000000/4414107:ℝ)]]
theorem cell8_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_4_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_4_2_g]
def cell8_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(1000146225800000000/6494780202483:ℝ), (2280005070343280000/6494780202483:ℝ), (424416916600000000/2164926734161:ℝ)],
  ![(713116138295520000/2164926734161:ℝ), (29983057428077598640000/40512273976354793:ℝ), (16558748820507400000000/40512273976354793:ℝ)],
  ![(1125985999600000000/6494780202483:ℝ), (46804839533022200000000/121536821929064379:ℝ), (8539540621500000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 4 2 b ν := by
 have heq : pairedCleared cell8 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_4_2_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_4_2_g]
theorem cell8_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_4_2 hb hν
def cell8_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(1327944553839225083/228742743759000000:ℝ)]]
theorem cell8_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 4 3) := by
 have heq : (-orderedLow cell8 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_4_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_4_3_g]
def cell8_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(522910897046740625552/336564982141936071:ℝ), (1048468904986450642700/336564982141936071:ℝ), (176532262575137750000/112188327380645357:ℝ)]]
theorem cell8_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 4 3 ν := by
 have heq : mixedLowHigh cell8 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_4_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_4_3_g]
def cell8_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(6273415684/4414107:ℝ), (12619446400/4414107:ℝ), (2133000000/1471369:ℝ)]]
theorem cell8_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 3 false ν := by
 have heq : naturalFloor cell8 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_4_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_4_3_g]
def cell8_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(717204183350116/496361918043:ℝ), (480603747111200/165453972681:ℝ), (730563401000000/496361918043:ℝ)]]
theorem cell8_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 3 true ν := by
 have heq : naturalFloor cell8 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_4_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_4_3_g]
def cell8_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(6273415684/4414107:ℝ), (12619446400/4414107:ℝ), (2133000000/1471369:ℝ)]]
theorem cell8_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_4_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_4_3_g]
def cell8_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(2424791242700000000/6494780202483:ℝ), (4784669509514920000/6494780202483:ℝ), (2349966124700000000/6494780202483:ℝ)],
  ![(1632097060595520000/2164926734161:ℝ), (60216861873318465080000/40512273976354793:ℝ), (29555780110925300000000/40512273976354793:ℝ)],
  ![(2458283749600000000/6494780202483:ℝ), (90636467218525900000000/121536821929064379:ℝ), (44461140925250000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 4 3 b ν := by
 have heq : pairedCleared cell8 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_4_3_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_4_3_g]
theorem cell8_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_4_3 hb hν
def cell8_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(8210047495063/1143713718795:ℝ)]]
theorem cell8_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 4 4) := by
 have heq : (-orderedLow cell8 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_4_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_4_4_g]
def cell8_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(695061455437529820736/336564982141936071:ℝ), (470088944910003281200/112188327380645357:ℝ), (720590419006751000000/336564982141936071:ℝ)]]
theorem cell8_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 4 4 ν := by
 have heq : mixedLowHigh cell8 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_4_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_4_4_g]
def cell8_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(2818100304/1471369:ℝ), (5738558400/1471369:ℝ), (2944000000/1471369:ℝ)]]
theorem cell8_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 4 false ν := by
 have heq : naturalFloor cell8 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_4_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_4_4_g]
def cell8_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(974207409453488/496361918043:ℝ), (660473228921600/165453972681:ℝ), (1015154068000000/496361918043:ℝ)]]
theorem cell8_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 4 true ν := by
 have heq : naturalFloor cell8 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_4_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_4_4_g]
def cell8_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(2818100304/1471369:ℝ), (5738558400/1471369:ℝ), (2944000000/1471369:ℝ)]]
theorem cell8_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_4_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_4_4_g]
def cell8_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(3160161617600000000/6494780202483:ℝ), (2106454768895520000/2164926734161:ℝ), (3145986499600000000/6494780202483:ℝ)],
  ![(2106454768895520000/2164926734161:ℝ), (78742162769977331520000/40512273976354793:ℝ), (39164542056343200000000/40512273976354793:ℝ)],
  ![(3145986499600000000/6494780202483:ℝ), (39164542056343200000000/40512273976354793:ℝ), (58391497486000000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 4 4 b ν := by
 have heq : pairedCleared cell8 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_4_4_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_4_4_g]
theorem cell8_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_4_4 hb hν
def cell8_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(1731906555302154917/228742743759000000:ℝ)]]
theorem cell8_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 4 5) := by
 have heq : (-orderedLow cell8 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_4_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_4_5_g]
def cell8_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(76477581355485066627463/33656498214193607100:ℝ), (52049208263312609209321/11218832738064535700:ℝ), (803431733987366331425/336564982141936071:ℝ)]]
theorem cell8_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 4 5 ν := by
 have heq : mixedLowHigh cell8 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_4_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_4_5_g]
def cell8_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(2961235380/1471369:ℝ), (6086808000/1471369:ℝ), (3155000000/1471369:ℝ)]]
theorem cell8_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 5 false ν := by
 have heq : naturalFloor cell8 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_4_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_4_5_g]
def cell8_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(338870388795620/165453972681:ℝ), (231946343114000/55151324227:ℝ), (360277720000000/165453972681:ℝ)]]
theorem cell8_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 5 true ν := by
 have heq : naturalFloor cell8 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_4_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_4_5_g]
def cell8_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(2961235380/1471369:ℝ), (6086808000/1471369:ℝ), (3155000000/1471369:ℝ)]]
theorem cell8_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_4_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_4_5_g]
def cell8_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(3424937468500000000/6494780202483:ℝ), (2294241526619400000/2164926734161:ℝ), (3441266874500000000/6494780202483:ℝ)],
  ![(6771102907586560000/6494780202483:ℝ), (84810378477432197960000/40512273976354793:ℝ), (127125239385283300000000/121536821929064379:ℝ)],
  ![(1110983083200000000/2164926734161:ℝ), (41718704166511100000000/40512273976354793:ℝ), (20832509682250000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 4 5 b ν := by
 have heq : pairedCleared cell8 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_4_5_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_4_5_g]
theorem cell8_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_4_5 hb hν
def cell8_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(394403181196830083/57185685939750000:ℝ)]]
theorem cell8_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 4 6) := by
 have heq : (-orderedLow cell8 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_4_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_4_6_g]
def cell8_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(16407785131875462152137/8414124553548401775:ℝ), (11398982484564809955679/2804708184516133925:ℝ), (719644052444165174300/336564982141936071:ℝ)]]
theorem cell8_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 4 6 ν := by
 have heq : mixedLowHigh cell8 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_4_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_4_6_g]
def cell8_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3104370456/1471369:ℝ), (6435057600/1471369:ℝ), (3366000000/1471369:ℝ)]]
theorem cell8_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 6 false ν := by
 have heq : naturalFloor cell8 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_4_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_4_6_g]
def cell8_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(1059014923320232/496361918043:ℝ), (731204829762400/165453972681:ℝ), (1146512252000000/496361918043:ℝ)]]
theorem cell8_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 4 6 true ν := by
 have heq : naturalFloor cell8 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_4_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_4_6_g]
def cell8_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3104370456/1471369:ℝ), (6435057600/1471369:ℝ), (3366000000/1471369:ℝ)]]
theorem cell8_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_4_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_4_6_g]
def cell8_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(1000146225800000000/2164926734161:ℝ), (2037405070343280000/2164926734161:ℝ), (1030650749800000000/2164926734161:ℝ)],
  ![(6252871866486560000/6494780202483:ℝ), (79170090636305064400000/40512273976354793:ℝ), (119782383866537000000000/121536821929064379:ℝ)],
  ![(3239216999600000000/6494780202483:ℝ), (40884596931679000000000/40512273976354793:ℝ), (61691398107500000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 4 6 b ν := by
 have heq : pairedCleared cell8 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_4_6_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_4_6_g]
theorem cell8_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_4_6 hb hν
def cell8_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(22773655249375979/7148210742468750:ℝ)]]
theorem cell8_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 5 1) := by
 have heq : (-orderedLow cell8 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_5_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_5_1_g]
def cell8_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(69483218706738258328/112188327380645357:ℝ), (444399330706815280700/336564982141936071:ℝ), (237295934515168250000/336564982141936071:ℝ)]]
theorem cell8_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 5 1 ν := by
 have heq : mixedLowHigh cell8 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_5_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_5_1_g]
def cell8_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(3932365228/4414107:ℝ), (8147708800/4414107:ℝ), (1411000000/1471369:ℝ)]]
theorem cell8_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 1 false ν := by
 have heq : naturalFloor cell8 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_5_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_5_1_g]
def cell8_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(141514414291124/165453972681:ℝ), (294017012400400/165453972681:ℝ), (153164414000000/165453972681:ℝ)]]
theorem cell8_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 1 true ν := by
 have heq : naturalFloor cell8 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_5_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_5_1_g]
def cell8_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(2248195228/4414107:ℝ), (4888538800/4414107:ℝ), (886000000/1471369:ℝ)]]
theorem cell8_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_5_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_5_1_g]
def cell8_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(529551701800000000/6494780202483:ℝ), (1197048874071640000/6494780202483:ℝ), (221397708300000000/2164926734161:ℝ)],
  ![(426545187719400000/2164926734161:ℝ), (17525972238873598640000/40512273976354793:ℝ), (9504148985257400000000/40512273976354793:ℝ)],
  ![(733563624500000000/6494780202483:ℝ), (29579293798772200000000/121536821929064379:ℝ), (5264765621500000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 5 1 b ν := by
 have heq : pairedCleared cell8 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_5_1_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_5_1_g]
theorem cell8_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_5_1 hb hν
def cell8_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(178370340454493249/45748548751800000:ℝ)]]
theorem cell8_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 5 2) := by
 have heq : (-orderedLow cell8 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_5_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_5_2_g]
def cell8_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(338651677464174733568/336564982141936071:ℝ), (241673114282958915000/112188327380645357:ℝ), (389060185241837500000/336564982141936071:ℝ)]]
theorem cell8_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 5 2 ν := by
 have heq : mixedLowHigh cell8 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_5_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_5_2_g]
def cell8_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1663490152/1471369:ℝ), (3523719200/1471369:ℝ), (1872000000/1471369:ℝ)]]
theorem cell8_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 2 false ν := by
 have heq : naturalFloor cell8 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_5_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_5_2_g]
def cell8_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(555290980756744/496361918043:ℝ), (392444181470800/165453972681:ℝ), (626012459000000/496361918043:ℝ)]]
theorem cell8_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 2 true ν := by
 have heq : naturalFloor cell8 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_5_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_5_2_g]
def cell8_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(4241950456/4414107:ℝ), (3040879200/1471369:ℝ), (4916000000/4414107:ℝ)]]
theorem cell8_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_5_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_5_2_g]
def cell8_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(1264922076700000000/6494780202483:ℝ), (910581223747760000/2164926734161:ℝ), (1460213499800000000/6494780202483:ℝ)],
  ![(900902896019400000/2164926734161:ℝ), (36051273135532465080000/40512273976354793:ℝ), (19112910930675300000000/40512273976354793:ℝ)],
  ![(1421266374500000000/6494780202483:ℝ), (18812150916425300000000/40512273976354793:ℝ), (29724653425250000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 5 2 b ν := by
 have heq : pairedCleared cell8 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_5_2_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_5_2_g]
theorem cell8_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_5_2 hb hν
def cell8_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(527473218282450581/114371371879500000:ℝ)]]
theorem cell8_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 5 3) := by
 have heq : (-orderedLow cell8 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_5_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_5_3_g]
def cell8_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(468853698808134692152/336564982141936071:ℝ), (1005639354990938209300/336564982141936071:ℝ), (180274811989502250000/112188327380645357:ℝ)]]
theorem cell8_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 5 3 ν := by
 have heq : mixedLowHigh cell8 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_5_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_5_3_g]
def cell8_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(6048575684/4414107:ℝ), (12994606400/4414107:ℝ), (2333000000/1471369:ℝ)]]
theorem cell8_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 3 false ν := by
 have heq : naturalFloor cell8 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_5_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_5_3_g]
def cell8_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(686038718640116/496361918043:ℝ), (490871350541200/165453972681:ℝ), (792531676000000/496361918043:ℝ)]]
theorem cell8_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 3 true ν := by
 have heq : naturalFloor cell8 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_5_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_5_3_g]
def cell8_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(6048575684/4414107:ℝ), (12994606400/4414107:ℝ), (2333000000/1471369:ℝ)]]
theorem cell8_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_5_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_5_3_g]
def cell8_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(2000292451600000000/6494780202483:ℝ), (4266438468414920000/6494780202483:ℝ), (2256233874700000000/6494780202483:ℝ)],
  ![(1375260604319400000/2164926734161:ℝ), (54576574032191331520000/40512273976354793:ℝ), (28721672876093200000000/40512273976354793:ℝ)],
  ![(2108969124500000000/6494780202483:ℝ), (83293611699779600000000/121536821929064379:ℝ), (43655009986000000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 5 3 b ν := by
 have heq : pairedCleared cell8 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_5_3_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_5_3_g]
theorem cell8_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_5_3 hb hν
def cell8_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(1852818300471875083/228742743759000000:ℝ)]]
theorem cell8_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 5 4) := by
 have heq : (-orderedLow cell8 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_5_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_5_4_g]
def cell8_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(246493630181914916912/112188327380645357:ℝ), (1483870223466399773600/336564982141936071:ℝ), (749774372634926000000/336564982141936071:ℝ)]]
theorem cell8_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 5 4 ν := by
 have heq : mixedLowHigh cell8 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_5_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_5_4_g]
def cell8_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(8948380912/4414107:ℝ), (18009755200/4414107:ℝ), (3044000000/1471369:ℝ)]]
theorem cell8_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 4 false ν := by
 have heq : naturalFloor cell8 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_5_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_5_4_g]
def cell8_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(113764864424832/55151324227:ℝ), (686443210711600/165453972681:ℝ), (347795881000000/165453972681:ℝ)]]
theorem cell8_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 4 true ν := by
 have heq : naturalFloor cell8 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_5_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_5_4_g]
def cell8_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(8948380912/4414107:ℝ), (18009755200/4414107:ℝ), (3044000000/1471369:ℝ)]]
theorem cell8_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_5_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_5_4_g]
def cell8_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(3424937468500000000/6494780202483:ℝ), (6771102907586560000/6494780202483:ℝ), (1110983083200000000/2164926734161:ℝ)],
  ![(2294241526619400000/2164926734161:ℝ), (84810378477432197960000/40512273976354793:ℝ), (41718704166511100000000/40512273976354793:ℝ)],
  ![(3441266874500000000/6494780202483:ℝ), (127125239385283300000000/121536821929064379:ℝ), (20832509682250000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 5 4 b ν := by
 have heq : pairedCleared cell8 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_5_4_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_5_4_g]
theorem cell8_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_5_4 hb hν
def cell8_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(8667532982581/914970975036:ℝ)]]
theorem cell8_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 5 5) := by
 have heq : (-orderedLow cell8 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_5_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_5_5_g]
def cell8_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(911631448936533945920/336564982141936071:ℝ), (615222717736652991500/112188327380645357:ℝ), (940768003916263750000/336564982141936071:ℝ)]]
theorem cell8_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 5 5 ν := by
 have heq : mixedLowHigh cell8 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_5_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_5_5_g]
def cell8_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(3709755380/1471369:ℝ), (7535328000/1471369:ℝ), (3855000000/1471369:ℝ)]]
theorem cell8_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 5 false ν := by
 have heq : naturalFloor cell8 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_5_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_5_5_g]
def cell8_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(1280887005926860/496361918043:ℝ), (866312692522000/165453972681:ℝ), (1327978310000000/496361918043:ℝ)]]
theorem cell8_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 5 true ν := by
 have heq : naturalFloor cell8 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_5_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_5_5_g]
def cell8_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(3709755380/1471369:ℝ), (7535328000/1471369:ℝ), (3855000000/1471369:ℝ)]]
theorem cell8_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_5_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_5_5_g]
def cell8_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(4160307843400000000/6494780202483:ℝ), (2768599234919400000/2164926734161:ℝ), (4128969624500000000/6494780202483:ℝ)],
  ![(2768599234919400000/2164926734161:ℝ), (103335679374091064400000/40512273976354793:ℝ), (51327466111929000000000/40512273976354793:ℝ)],
  ![(4128969624500000000/6494780202483:ℝ), (51327466111929000000000/40512273976354793:ℝ), (76427885607500000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 5 5 b ν := by
 have heq : pairedCleared cell8 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_5_5_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_5_5_g]
theorem cell8_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_5_5 hb hν
def cell8_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(2256780301934804917/228742743759000000:ℝ)]]
theorem cell8_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 5 6) := by
 have heq : (-orderedLow cell8 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_5_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_5_6_g]
def cell8_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(98134580705385479145863/33656498214193607100:ℝ), (66562585545977580239321/11218832738064535700:ℝ), (1023609318896879081425/336564982141936071:ℝ)]]
theorem cell8_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 5 6 ν := by
 have heq : mixedLowHigh cell8 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_5_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_5_6_g]
def cell8_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(3852890456/1471369:ℝ), (7883577600/1471369:ℝ), (4066000000/1471369:ℝ)]]
theorem cell8_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 6 false ν := by
 have heq : naturalFloor cell8 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_5_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_5_6_g]
def cell8_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(1323290762860232/496361918043:ℝ), (901678492942400/165453972681:ℝ), (1393657402000000/496361918043:ℝ)]]
theorem cell8_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 5 6 true ν := by
 have heq : naturalFloor cell8 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_5_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_5_6_g]
def cell8_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(3852890456/1471369:ℝ), (7883577600/1471369:ℝ), (4066000000/1471369:ℝ)]]
theorem cell8_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_5_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_5_6_g]
def cell8_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(1475027898100000000/2164926734161:ℝ), (2956385992643280000/2164926734161:ℝ), (1474749999800000000/2164926734161:ℝ)],
  ![(8757536305658200000/6494780202483:ℝ), (109403895081545930840000/40512273976354793:ℝ), (163614011552040700000000/121536821929064379:ℝ)],
  ![(4315932374500000000/6494780202483:ℝ), (53881628222096900000000/40512273976354793:ℝ), (80533917168250000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 5 6 b ν := by
 have heq : pairedCleared cell8 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_5_6_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_5_6_g]
theorem cell8_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_5_6 hb hν
def cell8_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(469308181709171971/76247581253000000:ℝ)]]
theorem cell8_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 6 1) := by
 have heq : (-orderedLow cell8 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_6_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_6_1_g]
def cell8_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(23649819733620598365589/16828249107096803550:ℝ), (47199419998283623078889/16828249107096803550:ℝ), (472338265221828238550/336564982141936071:ℝ)]]
theorem cell8_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 6 1 ν := by
 have heq : mixedLowHigh cell8 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_6_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_6_1_g]
def cell8_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(5549225228/4414107:ℝ), (11114568800/4414107:ℝ), (1861000000/1471369:ℝ)]]
theorem cell8_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 1 false ν := by
 have heq : naturalFloor cell8 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_6_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_6_1_g]
def cell8_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(600475101463372/496361918043:ℝ), (133809768976800/55151324227:ℝ), (605798267000000/496361918043:ℝ)]]
theorem cell8_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 1 true ν := by
 have heq : naturalFloor cell8 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_6_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_6_1_g]
def cell8_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(3303665228/4414107:ℝ), (6769008800/4414107:ℝ), (1161000000/1471369:ℝ)]]
theorem cell8_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_6_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_6_1_g]
def cell8_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(494534064900000000/2164926734161:ℝ), (2982657116971640000/6494780202483:ℝ), (1495750874900000000/6494780202483:ℝ)],
  ![(937655159443280000/2164926734161:ℝ), (35302691494910465080000/40512273976354793:ℝ), (17716467340425300000000/40512273976354793:ℝ)],
  ![(436512999800000000/2164926734161:ℝ), (49375715050025900000000/121536821929064379:ℝ), (24812490925250000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 6 1 b ν := by
 have heq : pairedCleared cell8 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_6_1_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_6_1_g]
theorem cell8_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_6_1 hb hν
def cell8_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(26117306554430861/4765473828312500:ℝ)]]
theorem cell8_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 6 2) := by
 have heq : (-orderedLow cell8 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_6_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_6_2_g]
def cell8_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(425019649619218900168/336564982141936071:ℝ), (879800649186764411600/336564982141936071:ℝ), (457473519424681000000/336564982141936071:ℝ)]]
theorem cell8_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 6 2 ν := by
 have heq : mixedLowHigh cell8 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_6_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_6_2_g]
def cell8_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(6607330456/4414107:ℝ), (13538017600/4414107:ℝ), (2322000000/1471369:ℝ)]]
theorem cell8_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 2 false ν := by
 have heq : naturalFloor cell8 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_6_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_6_2_g]
def cell8_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(731222839346744/496361918043:ℝ), (166618825333600/55151324227:ℝ), (772317484000000/496361918043:ℝ)]]
theorem cell8_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 2 true ν := by
 have heq : naturalFloor cell8 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_6_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_6_2_g]
def cell8_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(5297420456/4414107:ℝ), (11003107600/4414107:ℝ), (5741000000/4414107:ℝ)]]
theorem cell8_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_6_2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_6_2_g]
def cell8_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(509899309200000000/2164926734161:ℝ), (3183482272143280000/6494780202483:ℝ), (1647176249800000000/6494780202483:ℝ)],
  ![(1088689653743280000/2164926734161:ℝ), (42119488842987331520000/40512273976354793:ℝ), (21667073040843200000000/40512273976354793:ℝ)],
  ![(572182249800000000/2164926734161:ℝ), (66068065965529600000000/121536821929064379:ℝ), (33830684986000000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 6 2 b ν := by
 have heq : pairedCleared cell8 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_6_2_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_6_2_g]
theorem cell8_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_6_2 hb hν
def cell8_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(94448363260341083/15249516250600000:ℝ)]]
theorem cell8_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 6 3) := by
 have heq : (-orderedLow cell8 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_6_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_6_3_g]
def cell8_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(185073890321059619584/112188327380645357:ℝ), (386806887109608625300/112188327380645357:ℝ), (203079256717116750000/112188327380645357:ℝ)]]
theorem cell8_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 6 3 ν := by
 have heq : mixedLowHigh cell8 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_6_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_6_3_g]
def cell8_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2555145228/1471369:ℝ), (5320488800/1471369:ℝ), (2783000000/1471369:ℝ)]]
theorem cell8_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 3 false ν := by
 have heq : naturalFloor cell8 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_6_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_6_3_g]
def cell8_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2555145228/1471369:ℝ), (5320488800/1471369:ℝ), (2783000000/1471369:ℝ)]]
theorem cell8_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 3 true ν := by
 have heq : naturalFloor cell8 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_6_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_6_3_g]
def cell8_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(7291175684/4414107:ℝ), (5079068800/1471369:ℝ), (7999000000/4414107:ℝ)]]
theorem cell8_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_6_3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_6_3_g]
def cell8_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(755022767500000000/2164926734161:ℝ), (1572725689771640000/2164926734161:ℝ), (814398874900000000/2164926734161:ℝ)],
  ![(1563047362043280000/2164926734161:ℝ), (60644789739646197960000/40512273976354793:ℝ), (31275834986261100000000/40512273976354793:ℝ)],
  ![(801416499800000000/2164926734161:ℝ), (30975074972011100000000/40512273976354793:ℝ), (15920347182250000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 6 3 b ν := by
 have heq : pairedCleared cell8 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_6_3_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_6_3_g]
theorem cell8_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_6_3 hb hν
def cell8_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(263303363866258527/38123790626500000:ℝ)]]
theorem cell8_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 6 4) := by
 have heq : (-orderedLow cell8 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_6_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_6_4_g]
def cell8_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(685423692307138817336/336564982141936071:ℝ), (1441040673470887340200/336564982141936071:ℝ), (761002020878019500000/336564982141936071:ℝ)]]
theorem cell8_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 6 4 ν := by
 have heq : mixedLowHigh cell8 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_6_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_6_4_g]
def cell8_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(8723540912/4414107:ℝ), (18384915200/4414107:ℝ), (3244000000/1471369:ℝ)]]
theorem cell8_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 4 false ν := by
 have heq : naturalFloor cell8 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_6_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_6_4_g]
def cell8_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(992718315113488/496361918043:ℝ), (232236938047200/55151324227:ℝ), (1105355918000000/496361918043:ℝ)]]
theorem cell8_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 4 true ν := by
 have heq : naturalFloor cell8 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_6_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_6_4_g]
def cell8_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(8723540912/4414107:ℝ), (18384915200/4414107:ℝ), (3244000000/1471369:ℝ)]]
theorem cell8_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_6_4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_6_4_g]
def cell8_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(1000146225800000000/2164926734161:ℝ), (6252871866486560000/6494780202483:ℝ), (3239216999600000000/6494780202483:ℝ)],
  ![(2037405070343280000/2164926734161:ℝ), (79170090636305064400000/40512273976354793:ℝ), (40884596931679000000000/40512273976354793:ℝ)],
  ![(1030650749800000000/2164926734161:ℝ), (119782383866537000000000/121536821929064379:ℝ), (61691398107500000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 6 4 b ν := by
 have heq : pairedCleared cell8 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_6_4_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_6_4_g]
theorem cell8_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_6_4 hb hν
def cell8_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(792564015701508361/76247581253000000:ℝ)]]
theorem cell8_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 6 5) := by
 have heq : (-orderedLow cell8 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_6_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_6_5_g]
def cell8_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(956050884044748875920/336564982141936071:ℝ), (1919271541946348904500/336564982141936071:ℝ), (969951957544438750000/336564982141936071:ℝ)]]
theorem cell8_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 6 5 ν := by
 have heq : mixedLowHigh cell8 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_6_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_6_5_g]
def cell8_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(11623346140/4414107:ℝ), (23400064000/4414107:ℝ), (3955000000/1471369:ℝ)]]
theorem cell8_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 5 false ν := by
 have heq : naturalFloor cell8 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_6_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_6_5_g]
def cell8_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(1330563376296860/496361918043:ℝ), (297427558104000/55151324227:ℝ), (1356211885000000/496361918043:ℝ)]]
theorem cell8_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 5 true ν := by
 have heq : naturalFloor cell8 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_6_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_6_5_g]
def cell8_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(11623346140/4414107:ℝ), (23400064000/4414107:ℝ), (3955000000/1471369:ℝ)]]
theorem cell8_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_6_5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_6_5_g]
def cell8_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(1475027898100000000/2164926734161:ℝ), (8757536305658200000/6494780202483:ℝ), (4315932374500000000/6494780202483:ℝ)],
  ![(2956385992643280000/2164926734161:ℝ), (109403895081545930840000/40512273976354793:ℝ), (53881628222096900000000/40512273976354793:ℝ)],
  ![(1474749999800000000/2164926734161:ℝ), (163614011552040700000000/121536821929064379:ℝ), (80533917168250000000000/121536821929064379:ℝ)]]
theorem cell8_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 6 5 b ν := by
 have heq : pairedCleared cell8 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_6_5_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_6_5_g]
theorem cell8_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_6_5 hb hν
def cell8_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(8972523307593/762475812530:ℝ)]]
theorem cell8_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell8 6 6) := by
 have heq : (-orderedLow cell8 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell8_ordered_6_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordered_6_6_g]
def cell8_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(376067147478512690368/112188327380645357:ℝ), (760356490563302701800/112188327380645357:ℝ), (386981862941925500000/112188327380645357:ℝ)]]
theorem cell8_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell8 6 6 ν := by
 have heq : mixedLowHigh cell8 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_mixed_6_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_mixed_6_6_g]
def cell8_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(4601410456/1471369:ℝ), (9332097600/1471369:ℝ), (4766000000/1471369:ℝ)]]
theorem cell8_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 6 false ν := by
 have heq : naturalFloor cell8 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor0_6_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor0_6_6_g]
def cell8_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(529188867466744/165453972681:ℝ), (357384052040800/55151324227:ℝ), (546934184000000/165453972681:ℝ)]]
theorem cell8_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell8 6 6 true ν := by
 have heq : naturalFloor cell8 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_floor1_6_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_floor1_6_6_g]
def cell8_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(4601410456/1471369:ℝ), (9332097600/1471369:ℝ), (4766000000/1471369:ℝ)]]
theorem cell8_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell8_complement_floor_6_6_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement_floor_6_6_g]
def cell8_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(1720151356400000000/2164926734161:ℝ), (3430743700943280000/2164926734161:ℝ), (1703984249800000000/2164926734161:ℝ)],
  ![(3430743700943280000/2164926734161:ℝ), (127929195978204797280000/40512273976354793:ℝ), (63490390167514800000000/40512273976354793:ℝ)],
  ![(1703984249800000000/2164926734161:ℝ), (63490390167514800000000/40512273976354793:ℝ), (31488091243000000000000/40512273976354793:ℝ)]]
theorem cell8_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell8 6 6 b ν := by
 have heq : pairedCleared cell8 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell8_paired_cleared_6_6_g (6287/10000:ℝ) (3/4:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_cleared_6_6_g]
theorem cell8_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell8 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell8_paired_cleared_6_6 hb hν
def cell8_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(147959414696330083/228742743759000000:ℝ)]]
theorem cell8_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell8.q/K)+1+17/50*(cell8.q/cell8.priorL)+17/25*(cell8.q/cell8.priorL)*cell8.priorB) := by
 have heq : ((2-17/50-17/25)*(cell8.q/K)+1+17/50*(cell8.q/cell8.priorL)+17/25*(cell8.q/cell8.priorL)*cell8.priorB) = Record12518109.Bernstein.bsum 0 0 (147959414696330083/228742743759000000:ℝ) cell8_increment0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_increment0_g]
def cell8_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(1018038920933/2034191000000:ℝ)]]
theorem cell8_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell8.q/cell8.priorL)*(1-cell8.priorB)) := by
 have heq : (1+17/25*(cell8.q/cell8.priorL)*(1-cell8.priorB)) = Record12518109.Bernstein.bsum 0 0 (1018038920933/2034191000000:ℝ) cell8_increment1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_increment1_g]
def cell8_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(4071212262799/8136764000000:ℝ)]]
theorem cell8_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell8.q/cell8.priorL)*(1-cell8.priorB)) := by
 have heq : (1+omega*(cell8.q/cell8.priorL)*(1-cell8.priorB)) = Record12518109.Bernstein.bsum 0 0 (4071212262799/8136764000000:ℝ) cell8_increment2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_increment2_g]
def cell8_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(154592676/1471369:ℝ), (919414400/4414107:ℝ), (473292800/4414107:ℝ)]]
theorem cell8_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (287317/187500:ℝ) cell8_high_increment_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_high_increment_g]
def cell8_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(14478310491946/1784770597:ℝ), (135807882617362/1784770597:ℝ), (238148187524162/1784770597:ℝ), (110329189508054/1784770597:ℝ)]]
theorem cell8_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (7239155245973/500000000000:ℝ) cell8_three_gate0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_three_gate0_g]
def cell8_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(71567538/1471369:ℝ), (205114524/1471369:ℝ), (139432462/1471369:ℝ)]]
theorem cell8_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (35783769/50000000:ℝ) cell8_three_gate1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_three_gate1_g]
def cell8_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(49114833058072/496361918043:ℝ), (32565150530200/165453972681:ℝ), (50566066204700/496361918043:ℝ)]]
theorem cell8_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell8.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell8.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (162825752651/112449000000:ℝ) cell8_three_gate2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_three_gate2_g]
def cell8_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(643259/1349388:ℝ)]]
theorem cell8_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (1-cell8.q/K/3) := by
 have heq : (1-cell8.q/K/3) = Record12518109.Bernstein.bsum 0 0 (643259/1349388:ℝ) cell8_paired_margin0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_margin0_g]
def cell8_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(100291993/1122780000:ℝ)]]
theorem cell8_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (gamma cell8-13/50) := by
 have heq : (gamma cell8-13/50) = Record12518109.Bernstein.bsum 0 0 (100291993/1122780000:ℝ) cell8_paired_margin1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_margin1_g]
def cell8_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(42677/449112:ℝ)]]
theorem cell8_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (cell8.q-gamma cell8) := by
 have heq : (cell8.q-gamma cell8) = Record12518109.Bernstein.bsum 0 0 (42677/449112:ℝ) cell8_paired_margin2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_margin2_g]
def cell8_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(2346303749/7859460000:ℝ)]]
theorem cell8_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < (min (cell8.q+rho cell8.q) (3/4+rho (3/4))-gamma cell8) := by
 have heq : (min (cell8.q+rho cell8.q) (3/4+rho (3/4))-gamma cell8) = Record12518109.Bernstein.bsum 0 0 (2346303749/7859460000:ℝ) cell8_paired_margin3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_paired_margin3_g]
theorem cell8_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (6287/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell8 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell8_paired_1_1 hb hν
 · exact cell8_paired_1_2 hb hν
 · exact cell8_paired_1_3 hb hν
 · exact cell8_paired_1_4 hb hν
 · exact cell8_paired_1_5 hb hν
 · exact cell8_paired_1_6 hb hν
 · exact cell8_paired_2_1 hb hν
 · exact cell8_paired_2_2 hb hν
 · exact cell8_paired_2_3 hb hν
 · exact cell8_paired_2_4 hb hν
 · exact cell8_paired_2_5 hb hν
 · exact cell8_paired_2_6 hb hν
 · exact cell8_paired_3_1 hb hν
 · exact cell8_paired_3_2 hb hν
 · exact cell8_paired_3_3 hb hν
 · exact cell8_paired_3_4 hb hν
 · exact cell8_paired_3_5 hb hν
 · exact cell8_paired_3_6 hb hν
 · exact cell8_paired_4_1 hb hν
 · exact cell8_paired_4_2 hb hν
 · exact cell8_paired_4_3 hb hν
 · exact cell8_paired_4_4 hb hν
 · exact cell8_paired_4_5 hb hν
 · exact cell8_paired_4_6 hb hν
 · exact cell8_paired_5_1 hb hν
 · exact cell8_paired_5_2 hb hν
 · exact cell8_paired_5_3 hb hν
 · exact cell8_paired_5_4 hb hν
 · exact cell8_paired_5_5 hb hν
 · exact cell8_paired_5_6 hb hν
 · exact cell8_paired_6_1 hb hν
 · exact cell8_paired_6_2 hb hν
 · exact cell8_paired_6_3 hb hν
 · exact cell8_paired_6_4 hb hν
 · exact cell8_paired_6_5 hb hν
 · exact cell8_paired_6_6 hb hν
end
end Record12518109Admission
