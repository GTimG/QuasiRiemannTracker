/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.All
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission
def additional1_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(10871824/25281:ℝ), (23958200/25281:ℝ), (13187500/25281:ℝ)]]
theorem additional1_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 1 false ν := by
 have heq : naturalFloor cell1 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_1_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_1_1_g]
def additional1_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(1352198136976/2842823169:ℝ), (2948873031800/2842823169:ℝ), (1608046187500/2842823169:ℝ)]]
theorem additional1_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 1 true ν := by
 have heq : naturalFloor cell1 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_1_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_1_1_g]
def additional1_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(10871824/25281:ℝ), (23958200/25281:ℝ), (13187500/25281:ℝ)]]
theorem additional1_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_1_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_1_1_g]
def additional1_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(122531350000000/639128961:ℝ), (273451603040000/639128961:ℝ), (149774012500000/639128961:ℝ)],
  ![(273451603040000/639128961:ℝ), (1363689409470860000/1448905354587:ℝ), (738668696893750000/1448905354587:ℝ)],
  ![(149774012500000/639128961:ℝ), (738668696893750000/1448905354587:ℝ), (396623609375000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 1 1 b ν := by
 have heq : pairedCleared cell1 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_1_1_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_1_1_g]
theorem additional1_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_1_1 hb hν
def additional1_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(21743648/25281:ℝ), (47916400/25281:ℝ), (26375000/25281:ℝ)]]
theorem additional1_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 2 false ν := by
 have heq : naturalFloor cell1 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_1_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_1_2_g]
def additional1_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(21743648/25281:ℝ), (47916400/25281:ℝ), (26375000/25281:ℝ)]]
theorem additional1_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 2 true ν := by
 have heq : naturalFloor cell1 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_1_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_1_2_g]
def additional1_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(21743648/25281:ℝ), (47916400/25281:ℝ), (26375000/25281:ℝ)]]
theorem additional1_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_1_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_1_2_g]
def additional1_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(124514975000000/213042987:ℝ), (266453997860000/213042987:ℝ), (47058287500000/71014329:ℝ)],
  ![(725269865540000/639128961:ℝ), (3521913103506290000/1448905354587:ℝ), (1867514461356250000/1448905354587:ℝ)],
  ![(350578700000000/639128961:ℝ), (1704653535575000000/1448905354587:ℝ), (904876820312500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 1 2 b ν := by
 have heq : pairedCleared cell1 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_1_2_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_1_2_g]
theorem additional1_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_1_2 hb hν
def additional1_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(10871824/8427:ℝ), (23958200/8427:ℝ), (13187500/8427:ℝ)]]
theorem additional1_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 3 false ν := by
 have heq : naturalFloor cell1 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_1_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_1_3_g]
def additional1_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(3537904810928/2842823169:ℝ), (7827429495400/2842823169:ℝ), (4323638562500/2842823169:ℝ)]]
theorem additional1_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 3 true ν := by
 have heq : naturalFloor cell1 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_1_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_1_3_g]
def additional1_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(10871824/8427:ℝ), (23958200/8427:ℝ), (13187500/8427:ℝ)]]
theorem additional1_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_1_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_1_3_g]
def additional1_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (205571560000/1339893:ℝ), (198362500000/1339893:ℝ)],
  ![(3741714680000/12059037:ℝ), (24908934668240000/27337836879:ℝ), (16137452668750000/27337836879:ℝ)],
  ![(3720087500000/12059037:ℝ), (20618319856250000/27337836879:ℝ), (12042953125000000/27337836879:ℝ)]]
theorem additional1_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 1 3 b ν := by
 have heq : pairedCleared cell1 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_1_3_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_1_3_g]
theorem additional1_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_1_3 hb hν
def additional1_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(43487296/25281:ℝ), (95832800/25281:ℝ), (52750000/25281:ℝ)]]
theorem additional1_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 4 false ν := by
 have heq : naturalFloor cell1 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_1_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_1_4_g]
def additional1_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(4630758147904/2842823169:ℝ), (10266707727200/2842823169:ℝ), (5681434750000/2842823169:ℝ)]]
theorem additional1_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 4 true ν := by
 have heq : naturalFloor cell1 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_1_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_1_4_g]
def additional1_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(43487296/25281:ℝ), (95832800/25281:ℝ), (52750000/25281:ℝ)]]
theorem additional1_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_1_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_1_4_g]
def additional1_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(251013575000000/639128961:ℝ), (623968024660000/639128961:ℝ), (368369487500000/639128961:ℝ)],
  ![(650129140540000/639128961:ℝ), (3478397231452150000/1448905354587:ℝ), (1984130755906250000/1448905354587:ℝ)],
  ![(397969325000000/639128961:ℝ), (2058755791062500000/1448905354587:ℝ), (1146529726562500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 1 4 b ν := by
 have heq : pairedCleared cell1 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_1_4_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_1_4_g]
theorem additional1_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_1_4 hb hν
def additional1_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(54359120/25281:ℝ), (119791000/25281:ℝ), (65937500/25281:ℝ)]]
theorem additional1_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 5 false ν := by
 have heq : naturalFloor cell1 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_1_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_1_5_g]
def additional1_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(1907870494960/947607723:ℝ), (4235328653000/947607723:ℝ), (2346410312500/947607723:ℝ)]]
theorem additional1_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 5 true ν := by
 have heq : naturalFloor cell1 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_1_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_1_5_g]
def additional1_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(54359120/25281:ℝ), (119791000/25281:ℝ), (65937500/25281:ℝ)]]
theorem additional1_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_1_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_1_5_g]
def additional1_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(502027150000000/639128961:ℝ), (1149878415200000/639128961:ℝ), (642120062500000/639128961:ℝ)],
  ![(1101947403040000/639128961:ℝ), (5636620925487580000/1448905354587:ℝ), (3112976520368750000/1448905354587:ℝ)],
  ![(199591337500000/213042987:ℝ), (112027430731250000/53663161281:ℝ), (551594312500000000/482968451529:ℝ)]]
theorem additional1_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 1 5 b ν := by
 have heq : pairedCleared cell1 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_1_5_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_1_5_g]
theorem additional1_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_1_5 hb hν
def additional1_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(92780944/25281:ℝ), (186924200/25281:ℝ), (94750000/25281:ℝ)]]
theorem additional1_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 6 false ν := by
 have heq : naturalFloor cell1 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_1_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_1_6_g]
def additional1_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(9914434771856/2842823169:ℝ), (20000249765800/2842823169:ℝ), (10154042750000/2842823169:ℝ)]]
theorem additional1_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 1 6 true ν := by
 have heq : naturalFloor cell1 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_1_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_1_6_g]
def additional1_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(92780944/25281:ℝ), (186924200/25281:ℝ), (94750000/25281:ℝ)]]
theorem additional1_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_1_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_1_6_g]
def additional1_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(1377599225000000/639128961:ℝ), (2654566055740000/639128961:ℝ), (1270089387500000/639128961:ℝ)],
  ![(2780980415540000/639128961:ℝ), (12154807879648010000/1448905354587:ℝ), (5819689706706250000/1448905354587:ℝ)],
  ![(467411650000000/213042987:ℝ), (681311189200000000/160989483843:ℝ), (979296554687500000/482968451529:ℝ)]]
theorem additional1_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 1 6 b ν := by
 have heq : pairedCleared cell1 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_1_6_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_1_6_g]
theorem additional1_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_1_6 hb hν
def additional1_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(19241824/25281:ℝ), (12859400/8427:ℝ), (19437500/25281:ℝ)]]
theorem additional1_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 1 false ν := by
 have heq : naturalFloor cell1 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_2_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_2_1_g]
def additional1_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(19241824/25281:ℝ), (12859400/8427:ℝ), (19437500/25281:ℝ)]]
theorem additional1_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 1 true ν := by
 have heq : naturalFloor cell1 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_2_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_2_1_g]
def additional1_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(19241824/25281:ℝ), (12859400/8427:ℝ), (19437500/25281:ℝ)]]
theorem additional1_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_2_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_2_1_g]
def additional1_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(124514975000000/213042987:ℝ), (725269865540000/639128961:ℝ), (350578700000000/639128961:ℝ)],
  ![(266453997860000/213042987:ℝ), (3521913103506290000/1448905354587:ℝ), (1704653535575000000/1448905354587:ℝ)],
  ![(47058287500000/71014329:ℝ), (1867514461356250000/1448905354587:ℝ), (904876820312500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 2 1 b ν := by
 have heq : pairedCleared cell1 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_2_1_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_2_1_g]
theorem additional1_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_2_1 hb hν
def additional1_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(22361216/8427:ℝ), (45668800/8427:ℝ), (23375000/8427:ℝ)]]
theorem additional1_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 2 false ν := by
 have heq : naturalFloor cell1 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_2_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_2_2_g]
def additional1_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(7802833933952/2842823169:ℝ), (15915827473600/2842823169:ℝ), (8135736125000/2842823169:ℝ)]]
theorem additional1_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 2 true ν := by
 have heq : naturalFloor cell1 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_2_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_2_2_g]
def additional1_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(22361216/8427:ℝ), (45668800/8427:ℝ), (23375000/8427:ℝ)]]
theorem additional1_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_2_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_2_2_g]
def additional1_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(1272920500000000/639128961:ℝ), (2566573506080000/639128961:ℝ), (1291360525000000/639128961:ℝ)],
  ![(2566573506080000/639128961:ℝ), (11724000170291720000/1448905354587:ℝ), (5895366175037500000/1448905354587:ℝ)],
  ![(1291360525000000/639128961:ℝ), (5895366175037500000/1448905354587:ℝ), (2962837062500000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 2 2 b ν := by
 have heq : pairedCleared cell1 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_2_2_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_2_2_g]
theorem additional1_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_2_2 hb hν
def additional1_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(77955472/25281:ℝ), (160964600/25281:ℝ), (83312500/25281:ℝ)]]
theorem additional1_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 3 false ν := by
 have heq : naturalFloor cell1 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_2_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_2_3_g]
def additional1_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(8895687270928/2842823169:ℝ), (18355105705400/2842823169:ℝ), (9493532312500/2842823169:ℝ)]]
theorem additional1_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 3 true ν := by
 have heq : naturalFloor cell1 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_2_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_2_3_g]
def additional1_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(77955472/25281:ℝ), (160964600/25281:ℝ), (83312500/25281:ℝ)]]
theorem additional1_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_2_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_2_3_g]
def additional1_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(507978025000000/213042987:ℝ), (1030827965540000/213042987:ℝ), (521703700000000/213042987:ℝ)],
  ![(3018391768580000/639128961:ℝ), (13882223864327150000/1448905354587:ℝ), (7024211939500000000/1448905354587:ℝ)],
  ![(1492165212500000/639128961:ℝ), (6861351013718750000/1448905354587:ℝ), (3471090273437500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 2 3 b ν := by
 have heq : pairedCleared cell1 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_2_3_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_2_3_g]
theorem additional1_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_2_3 hb hν
def additional1_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(88827296/25281:ℝ), (184922800/25281:ℝ), (96500000/25281:ℝ)]]
theorem additional1_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 4 false ν := by
 have heq : naturalFloor cell1 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_2_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_2_4_g]
def additional1_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(88827296/25281:ℝ), (184922800/25281:ℝ), (96500000/25281:ℝ)]]
theorem additional1_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 4 true ν := by
 have heq : naturalFloor cell1 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_2_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_2_4_g]
def additional1_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(88827296/25281:ℝ), (184922800/25281:ℝ), (96500000/25281:ℝ)]]
theorem additional1_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_2_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_2_4_g]
def additional1_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(383463050000000/213042987:ℝ), (88562205080000/23671443:ℝ), (412068475000000/213042987:ℝ)],
  ![(2491432781080000/639128961:ℝ), (11680484298237580000/1448905354587:ℝ), (6011982469587500000/1448905354587:ℝ)],
  ![(1338751150000000/639128961:ℝ), (6249468430525000000/1448905354587:ℝ), (3204489968750000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 2 4 b ν := by
 have heq : pairedCleared cell1 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_2_4_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_2_4_g]
theorem additional1_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_2_4 hb hν
def additional1_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(11077680/2809:ℝ), (23209000/2809:ℝ), (12187500/2809:ℝ)]]
theorem additional1_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 5 false ν := by
 have heq : naturalFloor cell1 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_2_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_2_5_g]
def additional1_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(11081393944880/2842823169:ℝ), (23233662169000/2842823169:ℝ), (12209124687500/2842823169:ℝ)]]
theorem additional1_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 5 true ν := by
 have heq : naturalFloor cell1 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_2_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_2_5_g]
def additional1_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(11077680/2809:ℝ), (23209000/2809:ℝ), (12187500/2809:ℝ)]]
theorem additional1_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_2_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_2_5_g]
def additional1_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(1401402725000000/639128961:ℝ), (2917089927700000/639128961:ℝ), (1509956000000000/639128961:ℝ)],
  ![(2943251043580000/639128961:ℝ), (13838707992273010000/1448905354587:ℝ), (7140828234050000000/1448905354587:ℝ)],
  ![(1539555837500000/639128961:ℝ), (7215453269206250000/1448905354587:ℝ), (3712743179687500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 2 5 b ν := by
 have heq : pairedCleared cell1 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_2_5_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_2_5_g]
theorem additional1_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_2_5 hb hν
def additional1_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(110570944/25281:ℝ), (232839200/25281:ℝ), (122875000/25281:ℝ)]]
theorem additional1_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 6 false ν := by
 have heq : naturalFloor cell1 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_2_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_2_6_g]
def additional1_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(12174247281856/2842823169:ℝ), (25672940400800/2842823169:ℝ), (13566920875000/2842823169:ℝ)]]
theorem additional1_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 2 6 true ν := by
 have heq : naturalFloor cell1 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_2_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_2_6_g]
def additional1_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(110570944/25281:ℝ), (232839200/25281:ℝ), (122875000/25281:ℝ)]]
theorem additional1_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_2_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_2_6_g]
def additional1_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(1652416300000000/639128961:ℝ), (3443000318240000/639128961:ℝ), (1783706575000000/639128961:ℝ)],
  ![(3395069306080000/639128961:ℝ), (15996931686308440000/1448905354587:ℝ), (8269673998512500000/1448905354587:ℝ)],
  ![(580120175000000/213042987:ℝ), (2727146035962500000/482968451529:ℝ), (1406998796875000000/482968451529:ℝ)]]
theorem additional1_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 2 6 b ν := by
 have heq : pairedCleared cell1 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_2_6_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_2_6_g]
theorem additional1_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_2_6 hb hν
def additional1_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(22731824/25281:ℝ), (18189400/8427:ℝ), (31937500/25281:ℝ)]]
theorem additional1_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 1 false ν := by
 have heq : naturalFloor cell1 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_3_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_3_1_g]
def additional1_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(2426498476976/2842823169:ℝ), (5881342121800/2842823169:ℝ), (3466214937500/2842823169:ℝ)]]
theorem additional1_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 1 true ν := by
 have heq : naturalFloor cell1 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_3_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_3_1_g]
def additional1_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(11396824/25281:ℝ), (32295700/25281:ℝ), (7000000/8427:ℝ)]]
theorem additional1_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_3_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_3_1_g]
def additional1_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (3741714680000/12059037:ℝ), (3720087500000/12059037:ℝ)],
  ![(205571560000/1339893:ℝ), (24908934668240000/27337836879:ℝ), (20618319856250000/27337836879:ℝ)],
  ![(198362500000/1339893:ℝ), (16137452668750000/27337836879:ℝ), (12042953125000000/27337836879:ℝ)]]
theorem additional1_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 3 1 b ν := by
 have heq : pairedCleared cell1 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_3_1_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_3_1_g]
theorem additional1_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_3_1 hb hν
def additional1_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(25151216/8427:ℝ), (151626400/25281:ℝ), (76375000/25281:ℝ)]]
theorem additional1_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 2 false ν := by
 have heq : naturalFloor cell1 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_3_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_3_2_g]
def additional1_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(8614359663952/2842823169:ℝ), (17305034453600/2842823169:ℝ), (8713417375000/2842823169:ℝ)]]
theorem additional1_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 2 true ν := by
 have heq : naturalFloor cell1 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_3_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_3_2_g]
def additional1_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(25151216/8427:ℝ), (151626400/25281:ℝ), (76375000/25281:ℝ)]]
theorem additional1_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_3_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_3_2_g]
def additional1_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(507978025000000/213042987:ℝ), (3018391768580000/639128961:ℝ), (1492165212500000/639128961:ℝ)],
  ![(1030827965540000/213042987:ℝ), (13882223864327150000/1448905354587:ℝ), (6861351013718750000/1448905354587:ℝ)],
  ![(521703700000000/213042987:ℝ), (7024211939500000000/1448905354587:ℝ), (3471090273437500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 3 2 b ν := by
 have heq : pairedCleared cell1 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_3_2_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_3_2_g]
theorem additional1_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_3_2 hb hν
def additional1_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(123295472/25281:ℝ), (250054600/25281:ℝ), (127062500/25281:ℝ)]]
theorem additional1_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 3 false ν := by
 have heq : naturalFloor cell1 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_3_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_3_3_g]
def additional1_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1583718858992/315869241:ℝ), (3209197990600/315869241:ℝ), (1629269562500/315869241:ℝ)]]
theorem additional1_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 3 true ν := by
 have heq : naturalFloor cell1 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_3_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_3_3_g]
def additional1_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(123295472/25281:ℝ), (250054600/25281:ℝ), (127062500/25281:ℝ)]]
theorem additional1_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_3_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_3_3_g]
def additional1_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(2423309650000000/639128961:ℝ), (4859695409120000/639128961:ℝ), (2432947037500000/639128961:ℝ)],
  ![(4859695409120000/639128961:ℝ), (22084310931112580000/1448905354587:ℝ), (11052063653181250000/1448905354587:ℝ)],
  ![(2432947037500000/639128961:ℝ), (11052063653181250000/1448905354587:ℝ), (5529050515625000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 3 3 b ν := by
 have heq : pairedCleared cell1 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_3_3_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_3_3_g]
theorem additional1_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_3_3 hb hν
def additional1_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(44722432/8427:ℝ), (91337600/8427:ℝ), (46750000/8427:ℝ)]]
theorem additional1_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 4 false ν := by
 have heq : naturalFloor cell1 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_3_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_3_4_g]
def additional1_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(15346323067904/2842823169:ℝ), (31322060147200/2842823169:ℝ), (16021222250000/2842823169:ℝ)]]
theorem additional1_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 4 true ν := by
 have heq : naturalFloor cell1 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_3_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_3_4_g]
def additional1_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(44722432/8427:ℝ), (91337600/8427:ℝ), (46750000/8427:ℝ)]]
theorem additional1_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_3_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_3_4_g]
def additional1_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(297147025000000/71014329:ℝ), (1795201933220000/213042987:ℝ), (902232537500000/213042987:ℝ)],
  ![(5311513671620000/639128961:ℝ), (24242534625148010000/1448905354587:ℝ), (12180909417643750000/1448905354587:ℝ)],
  ![(2633751725000000/639128961:ℝ), (12018048491862500000/1448905354587:ℝ), (6037303726562500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 3 4 b ν := by
 have heq : pairedCleared cell1 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_3_4_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_3_4_g]
theorem additional1_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_3_4 hb hν
def additional1_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(145039120/25281:ℝ), (297971000/25281:ℝ), (153437500/25281:ℝ)]]
theorem additional1_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 5 false ν := by
 have heq : naturalFloor cell1 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_3_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_3_5_g]
def additional1_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(16439176404880/2842823169:ℝ), (33761338379000/2842823169:ℝ), (17379018437500/2842823169:ℝ)]]
theorem additional1_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 5 true ν := by
 have heq : naturalFloor cell1 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_3_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_3_5_g]
def additional1_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(145039120/25281:ℝ), (297971000/25281:ℝ), (153437500/25281:ℝ)]]
theorem additional1_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_3_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_3_5_g]
def additional1_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(766926100000000/213042987:ℝ), (520477937800000/71014329:ℝ), (792597312500000/213042987:ℝ)],
  ![(4784554684120000/639128961:ℝ), (22040795059058440000/1448905354587:ℝ), (11168679947731250000/1448905354587:ℝ)],
  ![(2480337662500000/639128961:ℝ), (11406165908668750000/1448905354587:ℝ), (5770703421875000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 3 5 b ν := by
 have heq : pairedCleared cell1 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_3_5_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_3_5_g]
theorem additional1_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_3_5 hb hν
def additional1_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(155910944/25281:ℝ), (321929200/25281:ℝ), (166625000/25281:ℝ)]]
theorem additional1_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 6 false ν := by
 have heq : naturalFloor cell1 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_3_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_3_6_g]
def additional1_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(155910944/25281:ℝ), (321929200/25281:ℝ), (166625000/25281:ℝ)]]
theorem additional1_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 3 6 true ν := by
 have heq : naturalFloor cell1 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_3_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_3_6_g]
def additional1_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(155910944/25281:ℝ), (321929200/25281:ℝ), (166625000/25281:ℝ)]]
theorem additional1_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_3_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_3_6_g]
def additional1_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(2551791875000000/639128961:ℝ), (5210211830740000/639128961:ℝ), (2651542512500000/639128961:ℝ)],
  ![(5236372946620000/639128961:ℝ), (24199018753093870000/1448905354587:ℝ), (12297525712193750000/1448905354587:ℝ)],
  ![(2681142350000000/639128961:ℝ), (12372150747350000000/1448905354587:ℝ), (6278956632812500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 3 6 b ν := by
 have heq : pairedCleared cell1 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_3_6_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_3_6_g]
theorem additional1_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_3_6 hb hν
def additional1_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(53771824/25281:ℝ), (113733200/25281:ℝ), (60062500/25281:ℝ)]]
theorem additional1_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 1 false ν := by
 have heq : naturalFloor cell1 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_4_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_4_1_g]
def additional1_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(5787243036976/2842823169:ℝ), (12279589806800/2842823169:ℝ), (6503718062500/2842823169:ℝ)]]
theorem additional1_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 1 true ν := by
 have heq : naturalFloor cell1 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_4_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_4_1_g]
def additional1_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(31101824/25281:ℝ), (69188200/25281:ℝ), (38187500/25281:ℝ)]]
theorem additional1_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_4_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_4_1_g]
def additional1_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(251013575000000/639128961:ℝ), (650129140540000/639128961:ℝ), (397969325000000/639128961:ℝ)],
  ![(623968024660000/639128961:ℝ), (3478397231452150000/1448905354587:ℝ), (2058755791062500000/1448905354587:ℝ)],
  ![(368369487500000/639128961:ℝ), (1984130755906250000/1448905354587:ℝ), (1146529726562500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 4 1 b ν := by
 have heq : pairedCleared cell1 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_4_1_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_4_1_g]
theorem additional1_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_4_1 hb hν
def additional1_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(78943648/25281:ℝ), (167616400/25281:ℝ), (9875000/2809:ℝ)]]
theorem additional1_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 2 false ν := by
 have heq : naturalFloor cell1 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_4_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_4_2_g]
def additional1_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(78943648/25281:ℝ), (167616400/25281:ℝ), (9875000/2809:ℝ)]]
theorem additional1_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 2 true ν := by
 have heq : naturalFloor cell1 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_4_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_4_2_g]
def additional1_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(225495944/75843:ℝ), (480576700/75843:ℝ), (255687500/75843:ℝ)]]
theorem additional1_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_4_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_4_2_g]
def additional1_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(383463050000000/213042987:ℝ), (2491432781080000/639128961:ℝ), (1338751150000000/639128961:ℝ)],
  ![(88562205080000/23671443:ℝ), (11680484298237580000/1448905354587:ℝ), (6249468430525000000/1448905354587:ℝ)],
  ![(412068475000000/213042987:ℝ), (6011982469587500000/1448905354587:ℝ), (3204489968750000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 4 2 b ν := by
 have heq : pairedCleared cell1 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_4_2_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_4_2_g]
theorem additional1_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_4_2 hb hν
def additional1_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(131665472/25281:ℝ), (264674600/25281:ℝ), (14812500/2809:ℝ)]]
theorem additional1_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 3 false ν := by
 have heq : naturalFloor cell1 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_4_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_4_3_g]
def additional1_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(284245197376/53638173:ℝ), (571169601800/53638173:ℝ), (5425812500/1012041:ℝ)]]
theorem additional1_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 3 true ν := by
 have heq : naturalFloor cell1 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_4_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_4_3_g]
def additional1_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(131665472/25281:ℝ), (264674600/25281:ℝ), (14812500/2809:ℝ)]]
theorem additional1_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_4_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_4_3_g]
def additional1_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(297147025000000/71014329:ℝ), (5311513671620000/639128961:ℝ), (2633751725000000/639128961:ℝ)],
  ![(1795201933220000/213042987:ℝ), (24242534625148010000/1448905354587:ℝ), (12018048491862500000/1448905354587:ℝ)],
  ![(902232537500000/213042987:ℝ), (12180909417643750000/1448905354587:ℝ), (6037303726562500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 4 3 b ν := by
 have heq : pairedCleared cell1 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_4_3_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_4_3_g]
theorem additional1_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_4_3 hb hν
def additional1_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(179507296/25281:ℝ), (363102800/25281:ℝ), (184000000/25281:ℝ)]]
theorem additional1_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 4 false ν := by
 have heq : naturalFloor cell1 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_4_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_4_4_g]
def additional1_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(20704105527904/2842823169:ℝ), (41849736357200/2842823169:ℝ), (21191116000000/2842823169:ℝ)]]
theorem additional1_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 4 true ν := by
 have heq : naturalFloor cell1 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_4_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_4_4_g]
def additional1_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(179507296/25281:ℝ), (363102800/25281:ℝ), (184000000/25281:ℝ)]]
theorem additional1_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_4_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_4_4_g]
def additional1_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(3573698800000000/639128961:ℝ), (7152817312160000/639128961:ℝ), (3574533550000000/639128961:ℝ)],
  ![(7152817312160000/639128961:ℝ), (32444621691933440000/1448905354587:ℝ), (16208761131325000000/1448905354587:ℝ)],
  ![(3574533550000000/639128961:ℝ), (16208761131325000000/1448905354587:ℝ), (8095263968750000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 4 4 b ν := by
 have heq : pairedCleared cell1 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_4_4_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_4_4_g]
theorem additional1_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_4_4 hb hν
def additional1_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(190379120/25281:ℝ), (387061000/25281:ℝ), (197187500/25281:ℝ)]]
theorem additional1_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 5 false ν := by
 have heq : naturalFloor cell1 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_4_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_4_5_g]
def additional1_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(2421884318320/315869241:ℝ), (4921001621000/315869241:ℝ), (2505434687500/315869241:ℝ)]]
theorem additional1_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 5 true ν := by
 have heq : naturalFloor cell1 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_4_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_4_5_g]
def additional1_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(190379120/25281:ℝ), (387061000/25281:ℝ), (197187500/25281:ℝ)]]
theorem additional1_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_4_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_4_5_g]
def additional1_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(1274904125000000/213042987:ℝ), (2559575900900000/213042987:ℝ), (427587125000000/71014329:ℝ)],
  ![(7604635574660000/639128961:ℝ), (34602845385968870000/1448905354587:ℝ), (17337606895787500000/1448905354587:ℝ)],
  ![(3775338237500000/639128961:ℝ), (17174745970006250000/1448905354587:ℝ), (8603517179687500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 4 5 b ν := by
 have heq : pairedCleared cell1 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_4_5_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_4_5_g]
theorem additional1_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_4_5 hb hν
def additional1_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(22361216/2809:ℝ), (45668800/2809:ℝ), (23375000/2809:ℝ)]]
theorem additional1_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 6 false ν := by
 have heq : naturalFloor cell1 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_4_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_4_6_g]
def additional1_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(22889812201856/2842823169:ℝ), (46728292820800/2842823169:ℝ), (23906708375000/2842823169:ℝ)]]
theorem additional1_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 4 6 true ν := by
 have heq : naturalFloor cell1 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_4_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_4_6_g]
def additional1_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(22361216/2809:ℝ), (45668800/2809:ℝ), (23375000/2809:ℝ)]]
theorem additional1_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_4_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_4_6_g]
def additional1_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(383463050000000/71014329:ℝ), (775269260360000/71014329:ℝ), (130347350000000/23671443:ℝ)],
  ![(7077676587160000/639128961:ℝ), (32401105819879300000/1448905354587:ℝ), (16325377425875000000/1448905354587:ℝ)],
  ![(3621924175000000/639128961:ℝ), (16562863386812500000/1448905354587:ℝ), (8336916875000000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 4 6 b ν := by
 have heq : pairedCleared cell1 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_4_6_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_4_6_g]
theorem additional1_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_4_6 hb hν
def additional1_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(9423536/2809:ℝ), (172898200/25281:ℝ), (88187500/25281:ℝ)]]
theorem additional1_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 1 false ν := by
 have heq : naturalFloor cell1 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_5_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_5_1_g]
def additional1_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(3049329198992/947607723:ℝ), (6225945830600/947607723:ℝ), (353378562500/105289747:ℝ)]]
theorem additional1_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 1 true ν := by
 have heq : naturalFloor cell1 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_5_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_5_1_g]
def additional1_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(16935608/8427:ℝ), (106080700/25281:ℝ), (55375000/25281:ℝ)]]
theorem additional1_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_5_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_5_1_g]
def additional1_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(502027150000000/639128961:ℝ), (1101947403040000/639128961:ℝ), (199591337500000/213042987:ℝ)],
  ![(1149878415200000/639128961:ℝ), (5636620925487580000/1448905354587:ℝ), (112027430731250000/53663161281:ℝ)],
  ![(642120062500000/639128961:ℝ), (3112976520368750000/1448905354587:ℝ), (551594312500000000/482968451529:ℝ)]]
theorem additional1_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 5 1 b ν := by
 have heq : pairedCleared cell1 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_5_1_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_5_1_g]
theorem additional1_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_5_1 hb hν
def additional1_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(36661216/8427:ℝ), (75593800/8427:ℝ), (13000000/2809:ℝ)]]
theorem additional1_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 2 false ν := by
 have heq : naturalFloor cell1 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_5_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_5_2_g]
def additional1_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(12237878833952/2842823169:ℝ), (25246544248600/2842823169:ℝ), (13031408000000/2842823169:ℝ)]]
theorem additional1_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 2 true ν := by
 have heq : naturalFloor cell1 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_5_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_5_2_g]
def additional1_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(284610944/75843:ℝ), (591254200/75843:ℝ), (307250000/75843:ℝ)]]
theorem additional1_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_5_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_5_2_g]
def additional1_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(1401402725000000/639128961:ℝ), (2943251043580000/639128961:ℝ), (1539555837500000/639128961:ℝ)],
  ![(2917089927700000/639128961:ℝ), (13838707992273010000/1448905354587:ℝ), (7215453269206250000/1448905354587:ℝ)],
  ![(1509956000000000/639128961:ℝ), (7140828234050000000/1448905354587:ℝ), (3712743179687500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 5 2 b ν := by
 have heq : pairedCleared cell1 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_5_2_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_5_2_g]
theorem additional1_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_5_2 hb hν
def additional1_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(45051824/8427:ℝ), (280664600/25281:ℝ), (145812500/25281:ℝ)]]
theorem additional1_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 3 false ν := by
 have heq : naturalFloor cell1 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_5_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_5_3_g]
def additional1_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(15327770070928/2842823169:ℝ), (31815251005400/2842823169:ℝ), (16521594812500/2842823169:ℝ)]]
theorem additional1_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 3 true ν := by
 have heq : naturalFloor cell1 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_5_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_5_3_g]
def additional1_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(45051824/8427:ℝ), (280664600/25281:ℝ), (145812500/25281:ℝ)]]
theorem additional1_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_5_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_5_3_g]
def additional1_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(766926100000000/213042987:ℝ), (4784554684120000/639128961:ℝ), (2480337662500000/639128961:ℝ)],
  ![(520477937800000/71014329:ℝ), (22040795059058440000/1448905354587:ℝ), (11406165908668750000/1448905354587:ℝ)],
  ![(792597312500000/213042987:ℝ), (11168679947731250000/1448905354587:ℝ), (5770703421875000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 5 3 b ν := by
 have heq : pairedCleared cell1 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_5_3_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_5_3_g]
theorem additional1_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_5_3 hb hν
def additional1_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(187877296/25281:ℝ), (41969200/2809:ℝ), (190250000/25281:ℝ)]]
theorem additional1_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 4 false ν := by
 have heq : naturalFloor cell1 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_5_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_5_4_g]
def additional1_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(7171877085968/947607723:ℝ), (14412981112400/947607723:ℝ), (806251750000/105289747:ℝ)]]
theorem additional1_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 4 true ν := by
 have heq : naturalFloor cell1 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_5_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_5_4_g]
def additional1_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(187877296/25281:ℝ), (41969200/2809:ℝ), (190250000/25281:ℝ)]]
theorem additional1_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_5_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_5_4_g]
def additional1_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(1274904125000000/213042987:ℝ), (7604635574660000/639128961:ℝ), (3775338237500000/639128961:ℝ)],
  ![(2559575900900000/213042987:ℝ), (34602845385968870000/1448905354587:ℝ), (17174745970006250000/1448905354587:ℝ)],
  ![(427587125000000/71014329:ℝ), (17337606895787500000/1448905354587:ℝ), (8603517179687500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 5 4 b ν := by
 have heq : pairedCleared cell1 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_5_4_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_5_4_g]
theorem additional1_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_5_4 hb hν
def additional1_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(78573040/8427:ℝ), (158717000/8427:ℝ), (80312500/8427:ℝ)]]
theorem additional1_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 5 false ν := by
 have heq : naturalFloor cell1 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_5_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_5_5_g]
def additional1_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(27154741324880/2842823169:ℝ), (54816690799000/2842823169:ℝ), (27718805937500/2842823169:ℝ)]]
theorem additional1_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 5 true ν := by
 have heq : naturalFloor cell1 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_5_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_5_5_g]
def additional1_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(78573040/8427:ℝ), (158717000/8427:ℝ), (80312500/8427:ℝ)]]
theorem additional1_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_5_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_5_5_g]
def additional1_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(4724087950000000/639128961:ℝ), (9445939215200000/639128961:ℝ), (4716120062500000/639128961:ℝ)],
  ![(9445939215200000/639128961:ℝ), (42804932452754300000/1448905354587:ℝ), (21365458609468750000/1448905354587:ℝ)],
  ![(4716120062500000/639128961:ℝ), (21365458609468750000/1448905354587:ℝ), (10661477421875000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 5 5 b ν := by
 have heq : pairedCleared cell1 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_5_5_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_5_5_g]
theorem additional1_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_5_5 hb hν
def additional1_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(246590944/25281:ℝ), (500109200/25281:ℝ), (254125000/25281:ℝ)]]
theorem additional1_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 6 false ν := by
 have heq : naturalFloor cell1 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_5_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_5_6_g]
def additional1_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(28247594661856/2842823169:ℝ), (57255969030800/2842823169:ℝ), (29076602125000/2842823169:ℝ)]]
theorem additional1_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 5 6 true ν := by
 have heq : naturalFloor cell1 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_5_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_5_6_g]
def additional1_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(246590944/25281:ℝ), (500109200/25281:ℝ), (254125000/25281:ℝ)]]
theorem additional1_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_5_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_5_6_g]
def additional1_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(1658367175000000/213042987:ℝ), (3323949868580000/213042987:ℝ), (1663290212500000/213042987:ℝ)],
  ![(9897757477700000/639128961:ℝ), (44963156146789730000/1448905354587:ℝ), (22494304373931250000/1448905354587:ℝ)],
  ![(4916924750000000/639128961:ℝ), (22331443448150000000/1448905354587:ℝ), (11169730632812500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 5 6 b ν := by
 have heq : pairedCleared cell1 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_5_6_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_5_6_g]
theorem additional1_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_5_6 hb hν
def additional1_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(115851824/25281:ℝ), (25784800/2809:ℝ), (116312500/25281:ℝ)]]
theorem additional1_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 1 false ν := by
 have heq : naturalFloor cell1 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_6_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_6_1_g]
def additional1_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(12508732156976/2842823169:ℝ), (25076085176800/2842823169:ℝ), (12578724312500/2842823169:ℝ)]]
theorem additional1_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 1 true ν := by
 have heq : naturalFloor cell1 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_6_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_6_1_g]
def additional1_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(70511824/25281:ℝ), (142973200/25281:ℝ), (8062500/2809:ℝ)]]
theorem additional1_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_6_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_6_1_g]
def additional1_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(1377599225000000/639128961:ℝ), (2780980415540000/639128961:ℝ), (467411650000000/213042987:ℝ)],
  ![(2654566055740000/639128961:ℝ), (12154807879648010000/1448905354587:ℝ), (681311189200000000/160989483843:ℝ)],
  ![(1270089387500000/639128961:ℝ), (5819689706706250000/1448905354587:ℝ), (979296554687500000/482968451529:ℝ)]]
theorem additional1_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 6 1 b ν := by
 have heq : pairedCleared cell1 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_6_1_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_6_1_g]
theorem additional1_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_6_1 hb hν
def additional1_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(141023648/25281:ℝ), (285946400/25281:ℝ), (16125000/2809:ℝ)]]
theorem additional1_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 2 false ν := by
 have heq : naturalFloor cell1 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_6_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_6_2_g]
def additional1_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(15598623393952/2842823169:ℝ), (31644791933600/2842823169:ℝ), (16068911125000/2842823169:ℝ)]]
theorem additional1_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 2 true ν := by
 have heq : naturalFloor cell1 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_6_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_6_2_g]
def additional1_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(343725944/75843:ℝ), (701931700/75843:ℝ), (358812500/75843:ℝ)]]
theorem additional1_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_6_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_6_2_g]
def additional1_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(1652416300000000/639128961:ℝ), (3395069306080000/639128961:ℝ), (580120175000000/213042987:ℝ)],
  ![(3443000318240000/639128961:ℝ), (15996931686308440000/1448905354587:ℝ), (2727146035962500000/482968451529:ℝ)],
  ![(1783706575000000/639128961:ℝ), (8269673998512500000/1448905354587:ℝ), (1406998796875000000/482968451529:ℝ)]]
theorem additional1_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 6 2 b ν := by
 have heq : pairedCleared cell1 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_6_2_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_6_2_g]
theorem additional1_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_6_2 hb hν
def additional1_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(166195472/25281:ℝ), (339829600/25281:ℝ), (173937500/25281:ℝ)]]
theorem additional1_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 3 false ν := by
 have heq : naturalFloor cell1 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_6_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_6_3_g]
def additional1_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(166195472/25281:ℝ), (339829600/25281:ℝ), (173937500/25281:ℝ)]]
theorem additional1_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 3 true ν := by
 have heq : naturalFloor cell1 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_6_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_6_3_g]
def additional1_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(475916416/75843:ℝ), (974943800/75843:ℝ), (499937500/75843:ℝ)]]
theorem additional1_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_6_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_6_3_g]
def additional1_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(2551791875000000/639128961:ℝ), (5236372946620000/639128961:ℝ), (2681142350000000/639128961:ℝ)],
  ![(5210211830740000/639128961:ℝ), (24199018753093870000/1448905354587:ℝ), (12372150747350000000/1448905354587:ℝ)],
  ![(2651542512500000/639128961:ℝ), (12297525712193750000/1448905354587:ℝ), (6278956632812500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 6 3 b ν := by
 have heq : pairedCleared cell1 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_6_3_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_6_3_g]
theorem additional1_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_6_3 hb hν
def additional1_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(191367296/25281:ℝ), (131237600/8427:ℝ), (202750000/25281:ℝ)]]
theorem additional1_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 4 false ν := by
 have heq : naturalFloor cell1 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_6_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_6_4_g]
def additional1_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(21778405867904/2842823169:ℝ), (44782205447200/2842823169:ℝ), (23049284750000/2842823169:ℝ)]]
theorem additional1_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 4 true ν := by
 have heq : naturalFloor cell1 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_6_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_6_4_g]
def additional1_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(191367296/25281:ℝ), (131237600/8427:ℝ), (202750000/25281:ℝ)]]
theorem additional1_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_6_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_6_4_g]
def additional1_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(383463050000000/71014329:ℝ), (7077676587160000/639128961:ℝ), (3621924175000000/639128961:ℝ)],
  ![(775269260360000/71014329:ℝ), (32401105819879300000/1448905354587:ℝ), (16562863386812500000/1448905354587:ℝ)],
  ![(130347350000000/23671443:ℝ), (16325377425875000000/1448905354587:ℝ), (8336916875000000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 6 4 b ν := by
 have heq : pairedCleared cell1 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_6_4_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_6_4_g]
theorem additional1_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_6_4 hb hν
def additional1_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(81363040/8427:ℝ), (490771000/25281:ℝ), (247187500/25281:ℝ)]]
theorem additional1_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 5 false ν := by
 have heq : naturalFloor cell1 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_6_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_6_5_g]
def additional1_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(27966267054880/2842823169:ℝ), (56205897779000/2842823169:ℝ), (28296487187500/2842823169:ℝ)]]
theorem additional1_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 5 true ν := by
 have heq : naturalFloor cell1 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_6_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_6_5_g]
def additional1_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(81363040/8427:ℝ), (490771000/25281:ℝ), (247187500/25281:ℝ)]]
theorem additional1_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_6_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_6_5_g]
def additional1_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(1658367175000000/213042987:ℝ), (9897757477700000/639128961:ℝ), (4916924750000000/639128961:ℝ)],
  ![(3323949868580000/213042987:ℝ), (44963156146789730000/1448905354587:ℝ), (22331443448150000000/1448905354587:ℝ)],
  ![(1663290212500000/213042987:ℝ), (22494304373931250000/1448905354587:ℝ), (11169730632812500000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 6 5 b ν := by
 have heq : pairedCleared cell1 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_6_5_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_6_5_g]
theorem additional1_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_6_5 hb hν
def additional1_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(291930944/25281:ℝ), (589199200/25281:ℝ), (297875000/25281:ℝ)]]
theorem additional1_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 6 false ν := by
 have heq : naturalFloor cell1 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor0_6_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor0_6_6_g]
def additional1_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(11201792373952/947607723:ℝ), (22594548413600/947607723:ℝ), (11415498625000/947607723:ℝ)]]
theorem additional1_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell1 6 6 true ν := by
 have heq : naturalFloor cell1 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_floor1_6_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_floor1_6_6_g]
def additional1_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(291930944/25281:ℝ), (589199200/25281:ℝ), (297875000/25281:ℝ)]]
theorem additional1_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional1_complement_floor_6_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_complement_floor_6_6_g]
def additional1_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(5874477100000000/639128961:ℝ), (11739061118240000/639128961:ℝ), (5857706575000000/639128961:ℝ)],
  ![(11739061118240000/639128961:ℝ), (53165243213575160000/1448905354587:ℝ), (26522156087612500000/1448905354587:ℝ)],
  ![(5857706575000000/639128961:ℝ), (26522156087612500000/1448905354587:ℝ), (13227690875000000000/1448905354587:ℝ)]]
theorem additional1_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell1 6 6 b ν := by
 have heq : pairedCleared cell1 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional1_paired_cleared_6_6_g (429/625:ℝ) (3/4:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional1_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional1_paired_cleared_6_6_g]
theorem additional1_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) : 0 ≤ pairedGap cell1 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional1_paired_cleared_6_6 hb hν
theorem additional1_floor0_base {ν : ℝ} (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ naturalFloor cell1 (i.val+1) (j.val+1) false ν := by
 fin_cases i <;> fin_cases j
 · exact additional1_floor0_1_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_1_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_1_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_1_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_1_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_1_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_2_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_2_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_2_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_2_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_2_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_2_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_3_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_3_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_3_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_3_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_3_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_3_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_4_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_4_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_4_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_4_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_4_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_4_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_5_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_5_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_5_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_5_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_5_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_5_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_6_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_6_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_6_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_6_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_6_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor0_6_6 (b:=(49/2000:ℝ)) (by norm_num) hν
theorem additional1_floor1_base {ν : ℝ} (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ naturalFloor cell1 (i.val+1) (j.val+1) true ν := by
 fin_cases i <;> fin_cases j
 · exact additional1_floor1_1_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_1_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_1_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_1_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_1_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_1_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_2_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_2_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_2_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_2_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_2_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_2_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_3_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_3_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_3_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_3_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_3_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_3_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_4_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_4_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_4_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_4_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_4_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_4_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_5_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_5_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_5_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_5_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_5_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_5_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_6_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_6_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_6_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_6_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_6_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_floor1_6_6 (b:=(49/2000:ℝ)) (by norm_num) hν
theorem additional1_complement_base {ν : ℝ} (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ complementaryFloor (i.val+1) (j.val+1) ν := by
 fin_cases i <;> fin_cases j
 · exact additional1_complement_floor_1_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_1_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_1_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_1_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_1_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_1_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_2_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_2_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_2_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_2_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_2_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_2_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_3_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_3_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_3_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_3_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_3_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_3_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_4_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_4_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_4_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_4_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_4_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_4_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_5_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_5_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_5_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_5_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_5_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_5_6 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_6_1 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_6_2 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_6_3 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_6_4 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_6_5 (b:=(49/2000:ℝ)) (by norm_num) hν
 · exact additional1_complement_floor_6_6 (b:=(49/2000:ℝ)) (by norm_num) hν
theorem additional1_paired_base {b ν : ℝ} (hb : b ∈ Set.Icc (429/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell1 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact additional1_paired_1_1 hb hν
 · exact additional1_paired_1_2 hb hν
 · exact additional1_paired_1_3 hb hν
 · exact additional1_paired_1_4 hb hν
 · exact additional1_paired_1_5 hb hν
 · exact additional1_paired_1_6 hb hν
 · exact additional1_paired_2_1 hb hν
 · exact additional1_paired_2_2 hb hν
 · exact additional1_paired_2_3 hb hν
 · exact additional1_paired_2_4 hb hν
 · exact additional1_paired_2_5 hb hν
 · exact additional1_paired_2_6 hb hν
 · exact additional1_paired_3_1 hb hν
 · exact additional1_paired_3_2 hb hν
 · exact additional1_paired_3_3 hb hν
 · exact additional1_paired_3_4 hb hν
 · exact additional1_paired_3_5 hb hν
 · exact additional1_paired_3_6 hb hν
 · exact additional1_paired_4_1 hb hν
 · exact additional1_paired_4_2 hb hν
 · exact additional1_paired_4_3 hb hν
 · exact additional1_paired_4_4 hb hν
 · exact additional1_paired_4_5 hb hν
 · exact additional1_paired_4_6 hb hν
 · exact additional1_paired_5_1 hb hν
 · exact additional1_paired_5_2 hb hν
 · exact additional1_paired_5_3 hb hν
 · exact additional1_paired_5_4 hb hν
 · exact additional1_paired_5_5 hb hν
 · exact additional1_paired_5_6 hb hν
 · exact additional1_paired_6_1 hb hν
 · exact additional1_paired_6_2 hb hν
 · exact additional1_paired_6_3 hb hν
 · exact additional1_paired_6_4 hb hν
 · exact additional1_paired_6_5 hb hν
 · exact additional1_paired_6_6 hb hν
end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.additional1_floor0_base
#print axioms QRH.Record12518109Source.additional1_floor1_base
#print axioms QRH.Record12518109Source.additional1_complement_base
#print axioms QRH.Record12518109Source.additional1_paired_base
