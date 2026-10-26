/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Cell09
import Submissions.hailey_collet_1252270103.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell9_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(223591392577/762475812530:ℝ)]]
theorem cell9_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 1 1) := by
 have heq : (-orderedLow cell9 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_1_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_1_1_g]
def cell9_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(1249293939005533664/9801397827329391:ℝ), (2876845765569591100/9801397827329391:ℝ), (1666757417873375000/9801397827329391:ℝ)]]
theorem cell9_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 1 1 ν := by
 have heq : mixedLowHigh cell9 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_1_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_1_1_g]
def cell9_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(35414164/385641:ℝ), (86621600/385641:ℝ), (52750000/385641:ℝ)]]
theorem cell9_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 1 false ν := by
 have heq : naturalFloor cell9 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_1_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_1_1_g]
def cell9_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(4470984977636/43364944809:ℝ), (10685522448400/43364944809:ℝ), (6387997250000/43364944809:ℝ)]]
theorem cell9_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 1 true ν := by
 have heq : naturalFloor cell9 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_1_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_1_1_g]
def cell9_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(35414164/385641:ℝ), (86621600/385641:ℝ), (52750000/385641:ℝ)]]
theorem cell9_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_1_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_1_1_g]
def cell9_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(3398393150000000/148718980881:ℝ), (7662250911220000/148718980881:ℝ), (4191580925000000/148718980881:ℝ)],
  ![(7662250911220000/148718980881:ℝ), (158611684565785240000/1393645569835851:ℝ), (85499002727600000000/1393645569835851:ℝ)],
  ![(4191580925000000/148718980881:ℝ), (85499002727600000000/1393645569835851:ℝ), (45587275562500000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 1 1 b ν := by
 have heq : pairedCleared cell9 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_1_1_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_1_1_g]
theorem cell9_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_1_1 hb hν
def cell9_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(26153091226684113/38123790626500000:ℝ)]]
theorem cell9_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 1 2) := by
 have heq : (-orderedLow cell9 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_1_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_1_2_g]
def cell9_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(953657962519783267169/2940419348198817300:ℝ), (2120746522151425695019/2940419348198817300:ℝ), (23812238288344659325/58808386963976346:ℝ)]]
theorem cell9_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 1 2 ν := by
 have heq : mixedLowHigh cell9 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_1_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_1_2_g]
def cell9_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(70828328/385641:ℝ), (173243200/385641:ℝ), (105500000/385641:ℝ)]]
theorem cell9_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 2 false ν := by
 have heq : naturalFloor cell9 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_1_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_1_2_g]
def cell9_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(70828328/385641:ℝ), (173243200/385641:ℝ), (105500000/385641:ℝ)]]
theorem cell9_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 2 true ν := by
 have heq : naturalFloor cell9 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_1_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_1_2_g]
def cell9_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(70828328/385641:ℝ), (173243200/385641:ℝ), (105500000/385641:ℝ)]]
theorem cell9_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_1_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_1_2_g]
def cell9_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(8992177325000000/148718980881:ℝ), (19569799097440000/148718980881:ℝ), (10433068100000000/148718980881:ℝ)],
  ![(17185378836220000/148718980881:ℝ), (350944321498277860000/1393645569835851:ℝ), (187280679325775000000/1393645569835851:ℝ)],
  ![(8120924675000000/148718980881:ℝ), (166246005607025000000/1393645569835851:ℝ), (88879975843750000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 1 2 b ν := by
 have heq : pairedCleared cell9 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_1_2_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_1_2_g]
theorem cell9_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_1_2 hb hν
def cell9_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(93295919750887/9530947656625000:ℝ)]]
theorem cell9_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 1 3) := by
 have heq : (-orderedLow cell9 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_1_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_1_3_g]
def cell9_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(10964717371889513131/735104837049704325:ℝ), (124938271112316344981/735104837049704325:ℝ), (4911792471400931350/29404193481988173:ℝ)]]
theorem cell9_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 1 3 ν := by
 have heq : mixedLowHigh cell9 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_1_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_1_3_g]
def cell9_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(35414164/128547:ℝ), (86621600/128547:ℝ), (52750000/128547:ℝ)]]
theorem cell9_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 3 false ν := by
 have heq : naturalFloor cell9 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_1_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_1_3_g]
def cell9_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(11458164332908/43364944809:ℝ), (28276526745200/43364944809:ℝ), (17338741750000/43364944809:ℝ)]]
theorem cell9_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 3 true ν := by
 have heq : naturalFloor cell9 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_1_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_1_3_g]
def cell9_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(35414164/128547:ℝ), (86621600/128547:ℝ), (52750000/128547:ℝ)]]
theorem cell9_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_1_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_1_3_g]
def cell9_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (1756312820000/79827687:ℝ), (1639925000000/79827687:ℝ)],
  ![(30268938460000/718449183:ℝ), (834938735334640000/6732587293893:ℝ), (532306939850000000/6732587293893:ℝ)],
  ![(29919775000000/718449183:ℝ), (680485877350000000/6732587293893:ℝ), (390942125000000000/6732587293893:ℝ)]]
theorem cell9_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 1 3 b ν := by
 have heq : pairedCleared cell9 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_1_3_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_1_3_g]
theorem cell9_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_1_3 hb hν
def cell9_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(27546318277317661/38123790626500000:ℝ)]]
theorem cell9_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 1 4) := by
 have heq : (-orderedLow cell9 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_1_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_1_4_g]
def cell9_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(7688008028465200253/36301473434553300:ℝ), (21696862678145848703/36301473434553300:ℝ), (32421507165852225/80669940965674:ℝ)]]
theorem cell9_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 1 4 ν := by
 have heq : mixedLowHigh cell9 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_1_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_1_4_g]
def cell9_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(141656656/385641:ℝ), (346486400/385641:ℝ), (211000000/385641:ℝ)]]
theorem cell9_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 4 false ν := by
 have heq : naturalFloor cell9 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_1_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_1_4_g]
def cell9_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(650076261328/1885432383:ℝ), (1611827343200/1885432383:ℝ), (991918000000/1885432383:ℝ)]]
theorem cell9_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 4 true ν := by
 have heq : naturalFloor cell9 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_1_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_1_4_g]
def cell9_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(141656656/385641:ℝ), (346486400/385641:ℝ), (211000000/385641:ℝ)]]
theorem cell9_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_1_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_1_4_g]
def cell9_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(621531575000000/16524331209:ℝ), (1686617663320000/16524331209:ℝ), (1032963050000000/16524331209:ℝ)],
  ![(1754310909580000/16524331209:ℝ), (40573883905195900000/154849507759539:ℝ), (23552134794125000000/154849507759539:ℝ)],
  ![(1124748575000000/16524331209:ℝ), (24623064387875000000/154849507759539:ℝ), (13801968906250000000/154849507759539:ℝ)]]
theorem cell9_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 1 4 b ν := by
 have heq : pairedCleared cell9 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_1_4_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_1_4_g]
theorem cell9_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_1_4 hb hν
def cell9_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(27359726437815887/19061895313250000:ℝ)]]
theorem cell9_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 1 5) := by
 have heq : (-orderedLow cell9 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_1_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_1_5_g]
def cell9_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(600799215561902194231/1470209674099408650:ℝ), (1507569334705181054981/1470209674099408650:ℝ), (18723486252505340675/29404193481988173:ℝ)]]
theorem cell9_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 1 5 ν := by
 have heq : mixedLowHigh cell9 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_1_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_1_5_g]
def cell9_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(177070820/385641:ℝ), (433108000/385641:ℝ), (263750000/385641:ℝ)]]
theorem cell9_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 5 false ν := by
 have heq : naturalFloor cell9 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_1_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_1_5_g]
def cell9_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(683160877340/1606109067:ℝ), (1698797446000/1606109067:ℝ), (1047758750000/1606109067:ℝ)]]
theorem cell9_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 5 true ν := by
 have heq : naturalFloor cell9 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_1_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_1_5_g]
def cell9_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(177070820/385641:ℝ), (433108000/385641:ℝ), (263750000/385641:ℝ)]]
theorem cell9_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_1_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_1_5_g]
def cell9_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(1243063150000000/16524331209:ℝ), (3009678572900000/16524331209:ℝ), (1726461625000000/16524331209:ℝ)],
  ![(937478744860000/5508110403:ℝ), (6882686321966120000/17205500862171:ℝ), (11620403323900000000/51616502586513:ℝ)],
  ![(1561342325000000/16524331209:ℝ), (33594953596700000000/154849507759539:ℝ), (18612268937500000000/154849507759539:ℝ)]]
theorem cell9_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 1 5 b ν := by
 have heq : pairedCleared cell9 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_1_5_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_1_5_g]
theorem cell9_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_1_5 hb hν
def cell9_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(187798671765935243/38123790626500000:ℝ)]]
theorem cell9_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 1 6) := by
 have heq : (-orderedLow cell9 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_1_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_1_6_g]
def cell9_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(989087271381624185477/980139782732939100:ℝ), (1978724148975035158327/980139782732939100:ℝ), (20263204647580030225/19602795654658782:ℝ)]]
theorem cell9_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 1 6 ν := by
 have heq : mixedLowHigh cell9 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_1_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_1_6_g]
def cell9_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(368134984/385641:ℝ), (737879600/385641:ℝ), (379000000/385641:ℝ)]]
theorem cell9_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 6 false ν := by
 have heq : naturalFloor cell9 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_1_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_1_6_g]
def cell9_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(39441620215816/43364944809:ℝ), (79193782540400/43364944809:ℝ), (40792921000000/43364944809:ℝ)]]
theorem cell9_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 1 6 true ν := by
 have heq : naturalFloor cell9 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_1_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_1_6_g]
def cell9_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(368134984/385641:ℝ), (737879600/385641:ℝ), (379000000/385641:ℝ)]]
theorem cell9_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_1_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_1_6_g]
def cell9_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(31367314025000000/148718980881:ℝ), (59437491842320000/148718980881:ℝ), (27636516800000000/148718980881:ℝ)],
  ![(63040390536220000/148718980881:ℝ), (1120274869228248340000/1393645569835851:ℝ), (521664998218475000000/1393645569835851:ℝ)],
  ![(31600799675000000/148718980881:ℝ), (561976404624725000000/1393645569835851:ℝ), (262050776968750000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 1 6 b ν := by
 have heq : pairedCleared cell9 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_1_6_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_1_6_g]
theorem cell9_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_1_6 hb hν
def cell9_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(46271884098895887/38123790626500000:ℝ)]]
theorem cell9_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 2 1) := by
 have heq : (-orderedLow cell9 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_2_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_2_1_g]
def cell9_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(325098157684728304/1278443194869051:ℝ), (643021037293627100/1278443194869051:ℝ), (323036652388375000/1278443194869051:ℝ)]]
theorem cell9_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 2 1 ν := by
 have heq : mixedLowHigh cell9 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_2_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_2_1_g]
def cell9_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(76974164/385641:ℝ), (153181600/385641:ℝ), (77750000/385641:ℝ)]]
theorem cell9_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 1 false ν := by
 have heq : naturalFloor cell9 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_2_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_2_1_g]
def cell9_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(76974164/385641:ℝ), (153181600/385641:ℝ), (77750000/385641:ℝ)]]
theorem cell9_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 1 true ν := by
 have heq : naturalFloor cell9 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_2_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_2_1_g]
def cell9_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(76974164/385641:ℝ), (153181600/385641:ℝ), (77750000/385641:ℝ)]]
theorem cell9_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_2_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_2_1_g]
def cell9_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(8992177325000000/148718980881:ℝ), (17185378836220000/148718980881:ℝ), (8120924675000000/148718980881:ℝ)],
  ![(19569799097440000/148718980881:ℝ), (350944321498277860000/1393645569835851:ℝ), (166246005607025000000/1393645569835851:ℝ)],
  ![(10433068100000000/148718980881:ℝ), (187280679325775000000/1393645569835851:ℝ), (88879975843750000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 2 1 b ν := by
 have heq : pairedCleared cell9 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_2_1_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_2_1_g]
theorem cell9_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_2_1 hb hν
def cell9_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(986067205107/381237906265:ℝ)]]
theorem cell9_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 2 2) := by
 have heq : (-orderedLow cell9 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_2_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_2_2_g]
def cell9_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(21786085312470461984/29404193481988173:ℝ), (44894722991129806600/29404193481988173:ℝ), (23343871226515250000/29404193481988173:ℝ)]]
theorem cell9_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 2 2 ν := by
 have heq : mixedLowHigh cell9 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_2_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_2_2_g]
def cell9_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(86082776/128547:ℝ), (178554400/128547:ℝ), (93500000/128547:ℝ)]]
theorem cell9_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 2 false ν := by
 have heq : naturalFloor cell9 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_2_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_2_2_g]
def cell9_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(30017161535272/43364944809:ℝ), (62124811476800/43364944809:ℝ), (32454569500000/43364944809:ℝ)]]
theorem cell9_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 2 true ν := by
 have heq : naturalFloor cell9 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_2_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_2_2_g]
def cell9_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(86082776/128547:ℝ), (178554400/128547:ℝ), (93500000/128547:ℝ)]]
theorem cell9_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_2_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_2_2_g]
def cell9_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(8119971500000000/49572993627:ℝ), (16428960007480000/49572993627:ℝ), (8260803950000000/49572993627:ℝ)],
  ![(16428960007480000/49572993627:ℝ), (310885208164590160000/464548523278617:ℝ), (156056271568400000000/464548523278617:ℝ)],
  ![(8260803950000000/49572993627:ℝ), (156056271568400000000/464548523278617:ℝ), (78222662875000000000/464548523278617:ℝ)]]
theorem cell9_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 2 2 b ν := by
 have heq : pairedCleared cell9 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_2_2_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_2_2_g]
theorem cell9_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_2_2 hb hν
def cell9_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(113580242108534113/38123790626500000:ℝ)]]
theorem cell9_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 2 3) := by
 have heq : (-orderedLow cell9 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_2_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_2_3_g]
def cell9_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(2757478312065169366369/2940419348198817300:ℝ), (5747165091593529025019/2940419348198817300:ℝ), (60499436234134909325/58808386963976346:ℝ)]]
theorem cell9_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 2 3 ν := by
 have heq : mixedLowHigh cell9 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_2_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_2_3_g]
def cell9_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(293662492/385641:ℝ), (622284800/385641:ℝ), (333250000/385641:ℝ)]]
theorem cell9_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 3 false ν := by
 have heq : naturalFloor cell9 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_2_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_2_3_g]
def cell9_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(33510751212908/43364944809:ℝ), (70920313625200/43364944809:ℝ), (37929941750000/43364944809:ℝ)]]
theorem cell9_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 3 true ν := by
 have heq : naturalFloor cell9 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_2_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_2_3_g]
def cell9_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(293662492/385641:ℝ), (622284800/385641:ℝ), (333250000/385641:ℝ)]]
theorem cell9_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_2_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_2_3_g]
def cell9_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(434111575000000/2155347549:ℝ), (886875771140000/2155347549:ℝ), (449621725000000/2155347549:ℝ)],
  ![(852318955760000/2155347549:ℝ), (16304177701829900000/20197761881679:ℝ), (8260152047875000000/20197761881679:ℝ)],
  ![(416112400000000/2155347549:ℝ), (7955301704125000000/20197761881679:ℝ), (4028415781250000000/20197761881679:ℝ)]]
theorem cell9_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 2 3 b ν := by
 have heq : pairedCleared cell9 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_2_3_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_2_3_g]
theorem cell9_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_2_3 hb hν
def cell9_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(21950083640213387/9530947656625000:ℝ)]]
theorem cell9_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 2 4) := by
 have heq : (-orderedLow cell9 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_2_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_2_4_g]
def cell9_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(153973268252745345977/245034945683234775:ℝ), (343847637824280725827/245034945683234775:ℝ), (7751797148098685450/9801397827329391:ℝ)]]
theorem cell9_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 2 4 ν := by
 have heq : mixedLowHigh cell9 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_2_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_2_4_g]
def cell9_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(329076656/385641:ℝ), (708906400/385641:ℝ), (386000000/385641:ℝ)]]
theorem cell9_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 4 false ν := by
 have heq : naturalFloor cell9 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_2_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_2_4_g]
def cell9_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(329076656/385641:ℝ), (708906400/385641:ℝ), (386000000/385641:ℝ)]]
theorem cell9_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 4 true ν := by
 have heq : naturalFloor cell9 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_2_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_2_4_g]
def cell9_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(329076656/385641:ℝ), (708906400/385641:ℝ), (386000000/385641:ℝ)]]
theorem cell9_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_2_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_2_4_g]
def cell9_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(20961521350000000/148718980881:ℝ), (44896639894880000/148718980881:ℝ), (23646011200000000/148718980881:ℝ)],
  ![(47890299372440000/148718980881:ℝ), (946876258142255720000/1393645569835851:ℝ), (492857348526550000000/1393645569835851:ℝ)],
  ![(26784224350000000/148718980881:ℝ), (523530388589050000000/1393645569835851:ℝ), (270005732937500000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 2 4 b ν := by
 have heq : pairedCleared cell9 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_2_4_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_2_4_g]
theorem cell9_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_2_4 hb hν
def cell9_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(114973469159167661/38123790626500000:ℝ)]]
theorem cell9_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 2 5) := by
 have heq : (-orderedLow cell9 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_2_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_2_5_g]
def cell9_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(2426548999851067319693/2940419348198817300:ℝ), (5383864446371917074943/2940419348198817300:ℝ), (60322476669696522025/58808386963976346:ℝ)]]
theorem cell9_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 2 5 ν := by
 have heq : mixedLowHigh cell9 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_2_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_2_5_g]
def cell9_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(13499660/14283:ℝ), (29464000/14283:ℝ), (16250000/14283:ℝ)]]
theorem cell9_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 5 false ν := by
 have heq : naturalFloor cell9 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_2_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_2_5_g]
def cell9_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(40497930568180/43364944809:ℝ), (88511317922000/43364944809:ℝ), (48880686250000/43364944809:ℝ)]]
theorem cell9_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 5 true ν := by
 have heq : naturalFloor cell9 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_2_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_2_5_g]
def cell9_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(13499660/14283:ℝ), (29464000/14283:ℝ), (16250000/14283:ℝ)]]
theorem cell9_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_2_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_2_5_g]
def cell9_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(26555305525000000/148718980881:ℝ), (56804188081100000/148718980881:ℝ), (29887498375000000/148718980881:ℝ)],
  ![(57413427297440000/148718980881:ℝ), (1139208895074748340000/1393645569835851:ℝ), (594639025124725000000/1393645569835851:ℝ)],
  ![(30713568100000000/148718980881:ℝ), (604277391468475000000/1393645569835851:ℝ), (313298433218750000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 2 5 b ν := by
 have heq : pairedCleared cell9 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_2_5_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_2_5_g]
theorem cell9_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_2_5 hb hν
def cell9_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(71073301878740887/19061895313250000:ℝ)]]
theorem cell9_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 2 6) := by
 have heq : (-orderedLow cell9 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_2_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_2_6_g]
def cell9_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1502709390334595243831/1470209674099408650:ℝ), (3320778619426232719981/1470209674099408650:ℝ), (37067085225400465675/29404193481988173:ℝ)]]
theorem cell9_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 2 6 ν := by
 have heq : mixedLowHigh cell9 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_2_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_2_6_g]
def cell9_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(399904984/385641:ℝ), (882149600/385641:ℝ), (491500000/385641:ℝ)]]
theorem cell9_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 6 false ν := by
 have heq : naturalFloor cell9 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_2_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_2_6_g]
def cell9_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(43991520245816/43364944809:ℝ), (97306820070400/43364944809:ℝ), (54356058500000/43364944809:ℝ)]]
theorem cell9_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 2 6 true ν := by
 have heq : naturalFloor cell9 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_2_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_2_6_g]
def cell9_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(399904984/385641:ℝ), (882149600/385641:ℝ), (491500000/385641:ℝ)]]
theorem cell9_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_2_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_2_6_g]
def cell9_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(32149089700000000/148718980881:ℝ), (68711736267320000/148718980881:ℝ), (36128985550000000/148718980881:ℝ)],
  ![(66936555222440000/148718980881:ℝ), (1331541532007240960000/1393645569835851:ℝ), (696420701722900000000/1393645569835851:ℝ)],
  ![(34642911850000000/148718980881:ℝ), (685024394347900000000/1393645569835851:ℝ), (356591133500000000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 2 6 b ν := by
 have heq : pairedCleared cell9 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_2_6_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_2_6_g]
theorem cell9_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_2_6 hb hν
def cell9_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(309908045221209/19061895313250000:ℝ)]]
theorem cell9_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 3 1) := by
 have heq : (-orderedLow cell9 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_3_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_3_1_g]
def cell9_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(946608741889526564/9801397827329391:ℝ), (3695088141965209000/9801397827329391:ℝ), (2787684991385000000/9801397827329391:ℝ)]]
theorem cell9_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 3 1 ν := by
 have heq : mixedLowHigh cell9 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_3_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_3_1_g]
def cell9_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(56594164/385641:ℝ), (182801600/385641:ℝ), (127750000/385641:ℝ)]]
theorem cell9_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 1 false ν := by
 have heq : naturalFloor cell9 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_3_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_3_1_g]
def cell9_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(5875259497636/43364944809:ℝ), (19610846968400/43364944809:ℝ), (13909047250000/43364944809:ℝ)]]
theorem cell9_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 1 true ν := by
 have heq : naturalFloor cell9 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_3_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_3_1_g]
def cell9_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(3246388/128547:ℝ), (30732200/128547:ℝ), (28000000/128547:ℝ)]]
theorem cell9_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_3_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_3_1_g]
def cell9_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (30268938460000/718449183:ℝ), (29919775000000/718449183:ℝ)],
  ![(1756312820000/79827687:ℝ), (834938735334640000/6732587293893:ℝ), (680485877350000000/6732587293893:ℝ)],
  ![(1639925000000/79827687:ℝ), (532306939850000000/6732587293893:ℝ), (390942125000000000/6732587293893:ℝ)]]
theorem cell9_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 3 1 b ν := by
 have heq : pairedCleared cell9 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_3_1_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_3_1_g]
theorem cell9_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_3_1 hb hν
def cell9_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(133699034980745887/38123790626500000:ℝ)]]
theorem cell9_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 3 2) := by
 have heq : (-orderedLow cell9 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_3_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_3_2_g]
def cell9_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(25515461122202611984/29404193481988173:ℝ), (51053669552174456600/29404193481988173:ℝ), (25773441977827750000/29404193481988173:ℝ)]]
theorem cell9_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 3 2 ν := by
 have heq : mixedLowHigh cell9 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_3_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_3_2_g]
def cell9_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(299808328/385641:ℝ), (602223200/385641:ℝ), (305500000/385641:ℝ)]]
theorem cell9_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 2 false ν := by
 have heq : naturalFloor cell9 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_3_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_3_2_g]
def cell9_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(34201844325272/43364944809:ℝ), (68664406766800/43364944809:ℝ), (34809482000000/43364944809:ℝ)]]
theorem cell9_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 2 true ν := by
 have heq : naturalFloor cell9 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_3_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_3_2_g]
def cell9_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(299808328/385641:ℝ), (602223200/385641:ℝ), (305500000/385641:ℝ)]]
theorem cell9_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_3_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_3_2_g]
def cell9_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(434111575000000/2155347549:ℝ), (852318955760000/2155347549:ℝ), (416112400000000/2155347549:ℝ)],
  ![(886875771140000/2155347549:ℝ), (16304177701829900000/20197761881679:ℝ), (7955301704125000000/20197761881679:ℝ)],
  ![(449621725000000/2155347549:ℝ), (8260152047875000000/20197761881679:ℝ), (4028415781250000000/20197761881679:ℝ)]]
theorem cell9_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 3 2 b ν := by
 have heq : pairedCleared cell9 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_3_2_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_3_2_g]
theorem cell9_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_3_2 hb hν
def cell9_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(3720677427851/762475812530:ℝ)]]
theorem cell9_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 3 3) := by
 have heq : (-orderedLow cell9 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_3_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_3_3_g]
def cell9_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(39824288807924322976/29404193481988173:ℝ), (81158908685550839900/29404193481988173:ℝ), (41687470199410375000/29404193481988173:ℝ)]]
theorem cell9_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 3 3 ν := by
 have heq : mixedLowHigh cell9 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_3_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_3_3_g]
def cell9_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(481082492/385641:ℝ), (984704800/385641:ℝ), (508250000/385641:ℝ)]]
theorem cell9_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 3 false ν := by
 have heq : naturalFloor cell9 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_3_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_3_3_g]
def cell9_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(18521112697636/14454981603:ℝ), (37854700168400/14454981603:ℝ), (19507047250000/14454981603:ℝ)]]
theorem cell9_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 3 true ν := by
 have heq : naturalFloor cell9 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_3_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_3_3_g]
def cell9_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(481082492/385641:ℝ), (984704800/385641:ℝ), (508250000/385641:ℝ)]]
theorem cell9_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_3_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_3_3_g]
def cell9_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(45321435850000000/148718980881:ℝ), (90911509133660000/148718980881:ℝ), (45373242775000000/148718980881:ℝ)],
  ![(90911509133660000/148718980881:ℝ), (1706699564421755720000/1393645569835851:ℝ), (850838626682800000000/1393645569835851:ℝ)],
  ![(45373242775000000/148718980881:ℝ), (850838626682800000000/1393645569835851:ℝ), (423748701687500000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 3 3 b ν := by
 have heq : pairedCleared cell9 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_3_3_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_3_3_g]
theorem cell9_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_3_3 hb hν
def cell9_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(201007392990384113/38123790626500000:ℝ)]]
theorem cell9_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 3 4) := by
 have heq : (-orderedLow cell9 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_3_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_3_4_g]
def cell9_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(1520432887203518488523/980139782732939100:ℝ), (3124527887011877451673/980139782732939100:ℝ), (32395544726641719775/19602795654658782:ℝ)]]
theorem cell9_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 3 4 ν := by
 have heq : mixedLowHigh cell9 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_3_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_3_4_g]
def cell9_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(172165552/128547:ℝ), (357108800/128547:ℝ), (187000000/128547:ℝ)]]
theorem cell9_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 4 false ν := by
 have heq : naturalFloor cell9 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_3_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_3_4_g]
def cell9_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(59056927770544/43364944809:ℝ), (122359602653600/43364944809:ℝ), (63996514000000/43364944809:ℝ)]]
theorem cell9_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 4 true ν := by
 have heq : naturalFloor cell9 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_3_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_3_4_g]
def cell9_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(172165552/128547:ℝ), (357108800/128547:ℝ), (187000000/128547:ℝ)]]
theorem cell9_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_3_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_3_4_g]
def cell9_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(50915220025000000/148718980881:ℝ), (102819057319880000/148718980881:ℝ), (51614729950000000/148718980881:ℝ)],
  ![(100434637058660000/148718980881:ℝ), (1899032201354248340000/1393645569835851:ℝ), (952620303280975000000/1393645569835851:ℝ)],
  ![(49302586525000000/148718980881:ℝ), (931585629562225000000/1393645569835851:ℝ), (467041401968750000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 3 4 b ν := by
 have heq : pairedCleared cell9 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_3_4_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_3_4_g]
theorem cell9_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_3_4 hb hν
def cell9_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(43806871360675887/9530947656625000:ℝ)]]
theorem cell9_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 3 5) := by
 have heq : (-orderedLow cell9 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_3_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_3_5_g]
def cell9_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(912874892144582562731/735104837049704325:ℝ), (1938147555833368009981/735104837049704325:ℝ), (41598990417191181350/29404193481988173:ℝ)]]
theorem cell9_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 3 5 ν := by
 have heq : mixedLowHigh cell9 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_3_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_3_5_g]
def cell9_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(551910820/385641:ℝ), (1157948000/385641:ℝ), (613750000/385641:ℝ)]]
theorem cell9_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 5 false ν := by
 have heq : naturalFloor cell9 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_3_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_3_5_g]
def cell9_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(62550517448180/43364944809:ℝ), (131155104802000/43364944809:ℝ), (69471886250000/43364944809:ℝ)]]
theorem cell9_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 5 true ν := by
 have heq : naturalFloor cell9 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_3_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_3_5_g]
def cell9_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(551910820/385641:ℝ), (1157948000/385641:ℝ), (613750000/385641:ℝ)]]
theorem cell9_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_3_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_3_5_g]
def cell9_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(41923042700000000/148718980881:ℝ), (86521269006100000/148718980881:ℝ), (44236842125000000/148718980881:ℝ)],
  ![(89514928483660000/148718980881:ℝ), (1720920198070240960000/1393645569835851:ℝ), (875527160504150000000/1393645569835851:ℝ)],
  ![(47375055275000000/148718980881:ℝ), (906200200566650000000/1393645569835851:ℝ), (459086446000000000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 3 5 b ν := by
 have heq : pairedCleared cell9 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_3_5_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_3_5_g]
theorem cell9_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_3_5 hb hν
def cell9_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(202400620041017661/38123790626500000:ℝ)]]
theorem cell9_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 3 6) := by
 have heq : (-orderedLow cell9 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_3_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_3_6_g]
def cell9_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(4230369349396453418893/2940419348198817300:ℝ), (9010283015814020404943/2940419348198817300:ℝ), (97009674615486772025/58808386963976346:ℝ)]]
theorem cell9_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 3 6 ν := by
 have heq : mixedLowHigh cell9 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_3_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_3_6_g]
def cell9_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(587324984/385641:ℝ), (1244569600/385641:ℝ), (666500000/385641:ℝ)]]
theorem cell9_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 6 false ν := by
 have heq : naturalFloor cell9 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_3_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_3_6_g]
def cell9_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(587324984/385641:ℝ), (1244569600/385641:ℝ), (666500000/385641:ℝ)]]
theorem cell9_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 3 6 true ν := by
 have heq : naturalFloor cell9 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_3_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_3_6_g]
def cell9_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(587324984/385641:ℝ), (1244569600/385641:ℝ), (666500000/385641:ℝ)]]
theorem cell9_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_3_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_3_6_g]
def cell9_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(47516826875000000/148718980881:ℝ), (98428817192320000/148718980881:ℝ), (50478329300000000/148718980881:ℝ)],
  ![(99038056408660000/148718980881:ℝ), (1913252835002733580000/1393645569835851:ℝ), (977308837102325000000/1393645569835851:ℝ)],
  ![(51304399025000000/148718980881:ℝ), (986947203446075000000/1393645569835851:ℝ), (502379146281250000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 3 6 b ν := by
 have heq : pairedCleared cell9 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_3_6_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_3_6_g]
theorem cell9_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_3_6 hb hν
def cell9_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(12174766474795661/7624758125300000:ℝ)]]
theorem cell9_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 4 1) := by
 have heq : (-orderedLow cell9 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_4_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_4_1_g]
def cell9_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(1118925649624206488/3267132609109797:ℝ), (2668272760486642300/3267132609109797:ℝ), (1562415641298875000/3267132609109797:ℝ)]]
theorem cell9_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 4 1 ν := by
 have heq : mixedLowHigh cell9 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_4_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_4_1_g]
def cell9_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(191864164/385641:ℝ), (430571600/385641:ℝ), (240250000/385641:ℝ)]]
theorem cell9_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 1 false ν := by
 have heq : naturalFloor cell9 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_4_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_4_1_g]
def cell9_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(20597538077636/43364944809:ℝ), (46527325548400/43364944809:ℝ), (26103247250000/43364944809:ℝ)]]
theorem cell9_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 1 true ν := by
 have heq : naturalFloor cell9 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_4_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_4_1_g]
def cell9_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(98154164/385641:ℝ), (249361600/385641:ℝ), (152750000/385641:ℝ)]]
theorem cell9_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_4_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_4_1_g]
def cell9_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(621531575000000/16524331209:ℝ), (1754310909580000/16524331209:ℝ), (1124748575000000/16524331209:ℝ)],
  ![(1686617663320000/16524331209:ℝ), (40573883905195900000/154849507759539:ℝ), (24623064387875000000/154849507759539:ℝ)],
  ![(1032963050000000/16524331209:ℝ), (23552134794125000000/154849507759539:ℝ), (13801968906250000000/154849507759539:ℝ)]]
theorem cell9_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 4 1 b ν := by
 have heq : pairedCleared cell9 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_4_1_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_4_1_g]
theorem cell9_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_4_1 hb hν
def cell9_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(44023483486146209/19061895313250000:ℝ)]]
theorem cell9_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 4 2) := by
 have heq : (-orderedLow cell9 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_4_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_4_2_g]
def cell9_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(20878029721122440684/29404193481988173:ℝ), (47349450120316660300/29404193481988173:ℝ), (26706653947050125000/29404193481988173:ℝ)]]
theorem cell9_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 4 2 ν := by
 have heq : mixedLowHigh cell9 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_4_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_4_2_g]
def cell9_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(31047592/42849:ℝ), (23401600/14283:ℝ), (39500000/42849:ℝ)]]
theorem cell9_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 2 false ν := by
 have heq : naturalFloor cell9 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_4_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_4_2_g]
def cell9_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(31047592/42849:ℝ), (23401600/14283:ℝ), (39500000/42849:ℝ)]]
theorem cell9_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 2 true ν := by
 have heq : naturalFloor cell9 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_4_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_4_2_g]
def cell9_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(791429984/1156923:ℝ), (1804924600/1156923:ℝ), (1022750000/1156923:ℝ)]]
theorem cell9_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_4_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_4_2_g]
def cell9_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(20961521350000000/148718980881:ℝ), (47890299372440000/148718980881:ℝ), (26784224350000000/148718980881:ℝ)],
  ![(44896639894880000/148718980881:ℝ), (946876258142255720000/1393645569835851:ℝ), (523530388589050000000/1393645569835851:ℝ)],
  ![(23646011200000000/148718980881:ℝ), (492857348526550000000/1393645569835851:ℝ), (270005732937500000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 4 2 b ν := by
 have heq : pairedCleared cell9 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_4_2_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_4_2_g]
theorem cell9_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_4_2 hb hν
def cell9_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(221126185862595887/38123790626500000:ℝ)]]
theorem cell9_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 4 3) := by
 have heq : (-orderedLow cell9 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_4_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_4_3_g]
def cell9_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(14517888205885490992/9801397827329391:ℝ), (29105951748865163300/9801397827329391:ℝ), (14705680316907625000/9801397827329391:ℝ)]]
theorem cell9_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 4 3 ν := by
 have heq : mixedLowHigh cell9 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_4_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_4_3_g]
def cell9_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(58071388/42849:ℝ), (116807200/42849:ℝ), (19750000/14283:ℝ)]]
theorem cell9_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 3 false ν := by
 have heq : naturalFloor cell9 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_4_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_4_3_g]
def cell9_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(59748020882908/43364944809:ℝ), (120103695795200/43364944809:ℝ), (60876054250000/43364944809:ℝ)]]
theorem cell9_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 3 true ν := by
 have heq : naturalFloor cell9 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_4_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_4_3_g]
def cell9_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(58071388/42849:ℝ), (116807200/42849:ℝ), (19750000/14283:ℝ)]]
theorem cell9_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_4_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_4_3_g]
def cell9_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(50915220025000000/148718980881:ℝ), (100434637058660000/148718980881:ℝ), (49302586525000000/148718980881:ℝ)],
  ![(102819057319880000/148718980881:ℝ), (1899032201354248340000/1393645569835851:ℝ), (931585629562225000000/1393645569835851:ℝ)],
  ![(51614729950000000/148718980881:ℝ), (952620303280975000000/1393645569835851:ℝ), (467041401968750000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 4 3 b ν := by
 have heq : pairedCleared cell9 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_4_3_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_4_3_g]
theorem cell9_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_4_3 hb hν
def cell9_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(2734610222744/381237906265:ℝ)]]
theorem cell9_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 4 4) := by
 have heq : (-orderedLow cell9 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_4_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_4_4_g]
def cell9_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(19287497434459394656/9801397827329391:ℝ), (39141031459990624400/9801397827329391:ℝ), (20010356390768500000/9801397827329391:ℝ)]]
theorem cell9_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 4 4 ν := by
 have heq : mixedLowHigh cell9 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_4_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_4_4_g]
def cell9_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(30605072/16767:ℝ), (62336800/16767:ℝ), (32000000/16767:ℝ)]]
theorem cell9_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 4 false ν := by
 have heq : naturalFloor cell9 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_4_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_4_4_g]
def cell9_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(81109514650544/43364944809:ℝ), (165003389533600/43364944809:ℝ), (84587714000000/43364944809:ℝ)]]
theorem cell9_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 4 true ν := by
 have heq : naturalFloor cell9 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_4_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_4_4_g]
def cell9_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(30605072/16767:ℝ), (62336800/16767:ℝ), (32000000/16767:ℝ)]]
theorem cell9_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_4_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_4_4_g]
def cell9_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(66282957200000000/148718980881:ℝ), (132536138244880000/148718980881:ℝ), (65964073700000000/148718980881:ℝ)],
  ![(132536138244880000/148718980881:ℝ), (2480743504349740960000/1393645569835851:ℝ), (1233508438660400000000/1393645569835851:ℝ)],
  ![(65964073700000000/148718980881:ℝ), (1233508438660400000000/1393645569835851:ℝ), (612829414750000000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 4 4 b ν := by
 have heq : pairedCleared cell9 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_4_4_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_4_4_g]
theorem cell9_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_4_4 hb hν
def cell9_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(288434543872234113/38123790626500000:ℝ)]]
theorem cell9_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 4 5) := by
 have heq : (-orderedLow cell9 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_4_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_4_5_g]
def cell9_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(6365119011155941564769/2940419348198817300:ℝ), (13000002230477735685019/2940419348198817300:ℝ), (133873832125715409325/58808386963976346:ℝ)]]
theorem cell9_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 4 5 ν := by
 have heq : mixedLowHigh cell9 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_4_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_4_5_g]
def cell9_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(739330820/385641:ℝ), (1520368000/385641:ℝ), (788750000/385641:ℝ)]]
theorem cell9_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 5 false ν := by
 have heq : naturalFloor cell9 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_4_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_4_5_g]
def cell9_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(28201034776060/14454981603:ℝ), (57932963894000/14454981603:ℝ), (30021028750000/14454981603:ℝ)]]
theorem cell9_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 5 true ν := by
 have heq : naturalFloor cell9 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_4_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_4_5_g]
def cell9_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(739330820/385641:ℝ), (1520368000/385641:ℝ), (788750000/385641:ℝ)]]
theorem cell9_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_4_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_4_5_g]
def cell9_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(71876741375000000/148718980881:ℝ), (144443686431100000/148718980881:ℝ), (72205560875000000/148718980881:ℝ)],
  ![(142059266169880000/148718980881:ℝ), (2673076141282233580000/1393645569835851:ℝ), (1335290115258575000000/1393645569835851:ℝ)],
  ![(69893417450000000/148718980881:ℝ), (1314255441539825000000/1393645569835851:ℝ), (656122115031250000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 4 5 b ν := by
 have heq : pairedCleared cell9 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_4_5_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_4_5_g]
theorem cell9_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_4_5 hb hν
def cell9_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(65663659081138387/9530947656625000:ℝ)]]
theorem cell9_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 4 6) := by
 have heq : (-orderedLow cell9 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_4_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_4_6_g]
def cell9_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(1363829979530929087531/735104837049704325:ℝ), (2844752198193893842481/735104837049704325:ℝ), (59942589390086306350/29404193481988173:ℝ)]]
theorem cell9_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 4 6 ν := by
 have heq : mixedLowHigh cell9 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_4_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_4_6_g]
def cell9_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(86082776/42849:ℝ), (178554400/42849:ℝ), (93500000/42849:ℝ)]]
theorem cell9_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 6 false ν := by
 have heq : naturalFloor cell9 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_4_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_4_6_g]
def cell9_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(88096694005816/43364944809:ℝ), (182594393830400/43364944809:ℝ), (95538458500000/43364944809:ℝ)]]
theorem cell9_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 4 6 true ν := by
 have heq : naturalFloor cell9 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_4_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_4_6_g]
def cell9_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(86082776/42849:ℝ), (178554400/42849:ℝ), (93500000/42849:ℝ)]]
theorem cell9_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_4_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_4_6_g]
def cell9_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(20961521350000000/49572993627:ℝ), (42715299372440000/49572993627:ℝ), (21609224350000000/49572993627:ℝ)],
  ![(43713185864960000/49572993627:ℝ), (831654712666075400000/464548523278617:ℝ), (419398990827250000000/464548523278617:ℝ)],
  ![(22655295400000000/49572993627:ℝ), (429623337514750000000/464548523278617:ℝ), (216055719687500000000/464548523278617:ℝ)]]
theorem cell9_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 4 6 b ν := by
 have heq : pairedCleared cell9 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_4_6_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_4_6_g]
theorem cell9_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_4_6 hb hν
def cell9_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(7570490541094637/2382736914156250:ℝ)]]
theorem cell9_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 5 1) := by
 have heq : (-orderedLow cell9 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_5_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_5_1_g]
def cell9_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(5766945155855712364/9801397827329391:ℝ), (12314548420954644800/9801397827329391:ℝ), (6586808856408250000/9801397827329391:ℝ)]]
theorem cell9_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 5 1 ν := by
 have heq : mixedLowHigh cell9 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_5_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_5_1_g]
def cell9_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(327134164/385641:ℝ), (678341600/385641:ℝ), (352750000/385641:ℝ)]]
theorem cell9_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 1 false ν := by
 have heq : naturalFloor cell9 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_5_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_5_1_g]
def cell9_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(11773272219212/14454981603:ℝ), (24481268042800/14454981603:ℝ), (12765815750000/14454981603:ℝ)]]
theorem cell9_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 1 true ν := by
 have heq : naturalFloor cell9 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_5_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_5_1_g]
def cell9_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(186569164/385641:ℝ), (406526600/385641:ℝ), (221500000/385641:ℝ)]]
theorem cell9_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_5_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_5_1_g]
def cell9_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(1243063150000000/16524331209:ℝ), (937478744860000/5508110403:ℝ), (1561342325000000/16524331209:ℝ)],
  ![(3009678572900000/16524331209:ℝ), (6882686321966120000/17205500862171:ℝ), (33594953596700000000/154849507759539:ℝ)],
  ![(1726461625000000/16524331209:ℝ), (11620403323900000000/51616502586513:ℝ), (18612268937500000000/154849507759539:ℝ)]]
theorem cell9_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 5 1 b ν := by
 have heq : pairedCleared cell9 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_5_1_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_5_1_g]
theorem cell9_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_5_1 hb hν
def cell9_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(29660196651165661/7624758125300000:ℝ)]]
theorem cell9_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 5 2) := by
 have heq : (-orderedLow cell9 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_5_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_5_2_g]
def cell9_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(28108534342071719384/29404193481988173:ℝ), (60278640538800814000/29404193481988173:ℝ), (32405339744585000000/29404193481988173:ℝ)]]
theorem cell9_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 5 2 ν := by
 have heq : mixedLowHigh cell9 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_5_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_5_2_g]
def cell9_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(46077592/42849:ℝ), (97734800/42849:ℝ), (52000000/42849:ℝ)]]
theorem cell9_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 2 false ν := by
 have heq : naturalFloor cell9 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_5_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_5_2_g]
def cell9_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(46143714635272/43364944809:ℝ), (97966614576800/43364944809:ℝ), (52169819500000/43364944809:ℝ)]]
theorem cell9_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 2 true ν := by
 have heq : naturalFloor cell9 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_5_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_5_2_g]
def cell9_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1056674984/1156923:ℝ), (2276419600/1156923:ℝ), (1229000000/1156923:ℝ)]]
theorem cell9_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_5_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_5_2_g]
def cell9_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(26555305525000000/148718980881:ℝ), (57413427297440000/148718980881:ℝ), (30713568100000000/148718980881:ℝ)],
  ![(56804188081100000/148718980881:ℝ), (1139208895074748340000/1393645569835851:ℝ), (604277391468475000000/1393645569835851:ℝ)],
  ![(29887498375000000/148718980881:ℝ), (594639025124725000000/1393645569835851:ℝ), (313298433218750000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 5 2 b ν := by
 have heq : pairedCleared cell9 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_5_2_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_5_2_g]
theorem cell9_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_5_2 hb hν
def cell9_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(87737058927071209/19061895313250000:ℝ)]]
theorem cell9_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 5 3) := by
 have heq : (-orderedLow cell9 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_5_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_5_3_g]
def cell9_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(38916233216576301676/29404193481988173:ℝ), (83613635814737693600/29404193481988173:ℝ), (45050252919945250000/29404193481988173:ℝ)]]
theorem cell9_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 5 3 ν := by
 have heq : mixedLowHigh cell9 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_5_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_5_3_g]
def cell9_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(502262492/385641:ℝ), (1080884800/385641:ℝ), (583250000/385641:ℝ)]]
theorem cell9_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 3 false ν := by
 have heq : naturalFloor cell9 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_5_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_5_3_g]
def cell9_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(56967612612908/43364944809:ℝ), (122489425025200/43364944809:ℝ), (66042191750000/43364944809:ℝ)]]
theorem cell9_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 3 true ν := by
 have heq : naturalFloor cell9 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_5_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_5_3_g]
def cell9_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(502262492/385641:ℝ), (1080884800/385641:ℝ), (583250000/385641:ℝ)]]
theorem cell9_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_5_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_5_3_g]
def cell9_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(41923042700000000/148718980881:ℝ), (89514928483660000/148718980881:ℝ), (47375055275000000/148718980881:ℝ)],
  ![(86521269006100000/148718980881:ℝ), (1720920198070240960000/1393645569835851:ℝ), (906200200566650000000/1393645569835851:ℝ)],
  ![(44236842125000000/148718980881:ℝ), (875527160504150000000/1393645569835851:ℝ), (459086446000000000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 5 3 b ν := by
 have heq : pairedCleared cell9 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_5_3_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_5_3_g]
theorem cell9_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_5_3 hb hν
def cell9_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(308553336744445887/38123790626500000:ℝ)]]
theorem cell9_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 5 4) := by
 have heq : (-orderedLow cell9 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_5_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_5_4_g]
def cell9_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(61591868113110333968/29404193481988173:ℝ), (123582040941016523200/29404193481988173:ℝ), (62460639923618000000/29404193481988173:ℝ)]]
theorem cell9_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 5 4 ν := by
 have heq : mixedLowHigh cell9 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_5_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_5_4_g]
def cell9_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(745476656/385641:ℝ), (1500306400/385641:ℝ), (761000000/385641:ℝ)]]
theorem cell9_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 4 false ν := by
 have heq : naturalFloor cell9 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_5_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_5_4_g]
def cell9_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(28431399146848/14454981603:ℝ), (57180994941200/14454981603:ℝ), (28980875500000/14454981603:ℝ)]]
theorem cell9_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 4 true ν := by
 have heq : naturalFloor cell9 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_5_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_5_4_g]
def cell9_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(745476656/385641:ℝ), (1500306400/385641:ℝ), (761000000/385641:ℝ)]]
theorem cell9_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_5_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_5_4_g]
def cell9_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(71876741375000000/148718980881:ℝ), (142059266169880000/148718980881:ℝ), (69893417450000000/148718980881:ℝ)],
  ![(144443686431100000/148718980881:ℝ), (2673076141282233580000/1393645569835851:ℝ), (1314255441539825000000/1393645569835851:ℝ)],
  ![(72205560875000000/148718980881:ℝ), (1335290115258575000000/1393645569835851:ℝ), (656122115031250000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 5 4 b ν := by
 have heq : pairedCleared cell9 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_5_4_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_5_4_g]
theorem cell9_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_5_4 hb hν
def cell9_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(1443552692625/152495162506:ℝ)]]
theorem cell9_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 5 5) := by
 have heq : (-orderedLow cell9 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_5_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_5_5_g]
def cell9_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(75900695798832044960/29404193481988173:ℝ), (153687280074392906500/29404193481988173:ℝ), (78374668145200625000/29404193481988173:ℝ)]]
theorem cell9_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 5 5 ν := by
 have heq : mixedLowHigh cell9 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_5_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_5_5_g]
def cell9_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(308916940/128547:ℝ), (627596000/128547:ℝ), (321250000/128547:ℝ)]]
theorem cell9_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 5 false ν := by
 have heq : naturalFloor cell9 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_5_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_5_5_g]
def cell9_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(106655691208180/43364944809:ℝ), (216442678562000/43364944809:ℝ), (110654286250000/43364944809:ℝ)]]
theorem cell9_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 5 true ν := by
 have heq : naturalFloor cell9 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_5_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_5_5_g]
def cell9_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(308916940/128547:ℝ), (627596000/128547:ℝ), (321250000/128547:ℝ)]]
theorem cell9_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_5_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_5_5_g]
def cell9_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(9693830950000000/16524331209:ℝ), (19351196372900000/16524331209:ℝ), (9617211625000000/16524331209:ℝ)],
  ![(19351196372900000/16524331209:ℝ), (361643049364191800000/154849507759539:ℝ), (179575361182000000000/154849507759539:ℝ)],
  ![(9617211625000000/16524331209:ℝ), (179575361182000000000/154849507759539:ℝ), (89101125312500000000/154849507759539:ℝ)]]
theorem cell9_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 5 5 b ν := by
 have heq : pairedCleared cell9 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_5_5_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_5_5_g]
theorem cell9_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_5_5 hb hν
def cell9_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(375861694754084113/38123790626500000:ℝ)]]
theorem cell9_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 5 6) := by
 have heq : (-orderedLow cell9 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_5_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_5_6_g]
def cell9_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(8168939360701327663969/2940419348198817300:ℝ), (16626420799919839015019/2940419348198817300:ℝ), (170561030071505659325/58808386963976346:ℝ)]]
theorem cell9_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 5 6 ν := by
 have heq : mixedLowHigh cell9 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_5_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_5_6_g]
def cell9_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(962164984/385641:ℝ), (1969409600/385641:ℝ), (1016500000/385641:ℝ)]]
theorem cell9_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 6 false ν := by
 have heq : naturalFloor cell9 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_5_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_5_6_g]
def cell9_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(110149280885816/43364944809:ℝ), (225238180710400/43364944809:ℝ), (116129658500000/43364944809:ℝ)]]
theorem cell9_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 5 6 true ν := by
 have heq : naturalFloor cell9 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_5_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_5_6_g]
def cell9_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(962164984/385641:ℝ), (1969409600/385641:ℝ), (1016500000/385641:ℝ)]]
theorem cell9_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_5_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_5_6_g]
def cell9_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(3438454175000000/5508110403:ℝ), (6891419094160000/5508110403:ℝ), (3436903400000000/5508110403:ℝ)],
  ![(20409321697900000/16524331209:ℝ), (383013342356690980000/154849507759539:ℝ), (190884436359575000000/154849507759539:ℝ)],
  ![(10053805375000000/16524331209:ℝ), (188547250390825000000/154849507759539:ℝ), (93911425343750000000/154849507759539:ℝ)]]
theorem cell9_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 5 6 b ν := by
 have heq : pairedCleared cell9 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_5_6_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_5_6_g]
theorem cell9_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_5_6 hb hν
def cell9_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(234334907087044757/38123790626500000:ℝ)]]
theorem cell9_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 6 1) := by
 have heq : (-orderedLow cell9 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_6_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_6_1_g]
def cell9_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(218989049038999442323/163356630455489850:ℝ), (145666107376250323891/54452210151829950:ℝ), (4373253992231469775/3267132609109797:ℝ)]]
theorem cell9_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 6 1 ν := by
 have heq : mixedLowHigh cell9 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_6_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_6_1_g]
def cell9_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(462404164/385641:ℝ), (926111600/385641:ℝ), (465250000/385641:ℝ)]]
theorem cell9_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 1 false ν := by
 have heq : naturalFloor cell9 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_6_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_6_1_g]
def cell9_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(50042095237636/43364944809:ℝ), (100360282708400/43364944809:ℝ), (50491647250000/43364944809:ℝ)]]
theorem cell9_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 1 true ν := by
 have heq : naturalFloor cell9 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_6_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_6_1_g]
def cell9_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(30553796/42849:ℝ), (62632400/42849:ℝ), (10750000/14283:ℝ)]]
theorem cell9_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_6_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_6_1_g]
def cell9_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(31367314025000000/148718980881:ℝ), (63040390536220000/148718980881:ℝ), (31600799675000000/148718980881:ℝ)],
  ![(59437491842320000/148718980881:ℝ), (1120274869228248340000/1393645569835851:ℝ), (561976404624725000000/1393645569835851:ℝ)],
  ![(27636516800000000/148718980881:ℝ), (521664998218475000000/1393645569835851:ℝ), (262050776968750000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 6 1 b ν := by
 have heq : pairedCleared cell9 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_6_1_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_6_1_g]
theorem cell9_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_6_1 hb hν
def cell9_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(6517343735605131/1191368457078125:ℝ)]]
theorem cell9_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 6 2) := by
 have heq : (-orderedLow cell9 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_6_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_6_2_g]
def cell9_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(35339038963020998084/29404193481988173:ℝ), (73207830957284967700/29404193481988173:ℝ), (38104025542119875000/29404193481988173:ℝ)]]
theorem cell9_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 6 2 ν := by
 have heq : mixedLowHigh cell9 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_6_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_6_2_g]
def cell9_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(61107592/42849:ℝ), (125264800/42849:ℝ), (21500000/14283:ℝ)]]
theorem cell9_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 2 false ν := by
 have heq : naturalFloor cell9 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_6_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_6_2_g]
def cell9_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(60865993215272/43364944809:ℝ), (124883093156800/43364944809:ℝ), (64364019500000/43364944809:ℝ)]]
theorem cell9_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 2 true ν := by
 have heq : naturalFloor cell9 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_6_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_6_2_g]
def cell9_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(1321919984/1156923:ℝ), (2747914600/1156923:ℝ), (1435250000/1156923:ℝ)]]
theorem cell9_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_6_2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_6_2_g]
def cell9_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(32149089700000000/148718980881:ℝ), (66936555222440000/148718980881:ℝ), (34642911850000000/148718980881:ℝ)],
  ![(68711736267320000/148718980881:ℝ), (1331541532007240960000/1393645569835851:ℝ), (685024394347900000000/1393645569835851:ℝ)],
  ![(36128985550000000/148718980881:ℝ), (696420701722900000000/1393645569835851:ℝ), (356591133500000000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 6 2 b ν := by
 have heq : pairedCleared cell9 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_6_2_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_6_2_g]
theorem cell9_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_6_2 hb hν
def cell9_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(47145626827535661/7624758125300000:ℝ)]]
theorem cell9_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 6 3) := by
 have heq : (-orderedLow cell9 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_6_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_6_3_g]
def cell9_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(46146737837525580376/29404193481988173:ℝ), (96542826233221847300/29404193481988173:ℝ), (50748938717480125000/29404193481988173:ℝ)]]
theorem cell9_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 6 3 ν := by
 have heq : mixedLowHigh cell9 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_6_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_6_3_g]
def cell9_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(27718804/16767:ℝ), (57767600/16767:ℝ), (30250000/16767:ℝ)]]
theorem cell9_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 3 false ν := by
 have heq : naturalFloor cell9 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_6_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_6_3_g]
def cell9_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(27718804/16767:ℝ), (57767600/16767:ℝ), (30250000/16767:ℝ)]]
theorem cell9_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 3 true ν := by
 have heq : naturalFloor cell9 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_6_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_6_3_g]
def cell9_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(1818887476/1156923:ℝ), (3804754400/1156923:ℝ), (1999750000/1156923:ℝ)]]
theorem cell9_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_6_3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_6_3_g]
def cell9_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(47516826875000000/148718980881:ℝ), (99038056408660000/148718980881:ℝ), (51304399025000000/148718980881:ℝ)],
  ![(98428817192320000/148718980881:ℝ), (1913252835002733580000/1393645569835851:ℝ), (986947203446075000000/1393645569835851:ℝ)],
  ![(50478329300000000/148718980881:ℝ), (977308837102325000000/1393645569835851:ℝ), (502379146281250000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 6 3 b ν := by
 have heq : pairedCleared cell9 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_6_3_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_6_3_g]
theorem cell9_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_6_3 hb hν
def cell9_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(131450634367996209/19061895313250000:ℝ)]]
theorem cell9_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 6 4) := by
 have heq : (-orderedLow cell9 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_6_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_6_4_g]
def cell9_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(18984812237343387556/9801397827329391:ℝ), (39959273836386242300/9801397827329391:ℝ), (21131283964280125000/9801397827329391:ℝ)]]
theorem cell9_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 6 4 ν := by
 have heq : mixedLowHigh cell9 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_6_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_6_4_g]
def cell9_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(725096656/385641:ℝ), (1529926400/385641:ℝ), (811000000/385641:ℝ)]]
theorem cell9_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 4 false ν := by
 have heq : naturalFloor cell9 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_6_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_6_4_g]
def cell9_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(82513789170544/43364944809:ℝ), (173928714053600/43364944809:ℝ), (92108764000000/43364944809:ℝ)]]
theorem cell9_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 4 true ν := by
 have heq : naturalFloor cell9 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_6_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_6_4_g]
def cell9_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(725096656/385641:ℝ), (1529926400/385641:ℝ), (811000000/385641:ℝ)]]
theorem cell9_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_6_4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_6_4_g]
def cell9_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(20961521350000000/49572993627:ℝ), (43713185864960000/49572993627:ℝ), (22655295400000000/49572993627:ℝ)],
  ![(42715299372440000/49572993627:ℝ), (831654712666075400000/464548523278617:ℝ), (429623337514750000000/464548523278617:ℝ)],
  ![(21609224350000000/49572993627:ℝ), (419398990827250000000/464548523278617:ℝ), (216055719687500000000/464548523278617:ℝ)]]
theorem cell9_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 6 4 b ν := by
 have heq : pairedCleared cell9 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_6_4_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_6_4_g]
theorem cell9_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_6_4 hb hν
def cell9_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(395980487626295887/38123790626500000:ℝ)]]
theorem cell9_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 6 5) := by
 have heq : (-orderedLow cell9 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_6_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_6_5_g]
def cell9_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(79630071608564194960/29404193481988173:ℝ), (159846226635437556500/29404193481988173:ℝ), (80804238896513125000/29404193481988173:ℝ)]]
theorem cell9_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 6 5 ν := by
 have heq : mixedLowHigh cell9 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_6_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_6_5_g]
def cell9_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(968310820/385641:ℝ), (1949348000/385641:ℝ), (988750000/385641:ℝ)]]
theorem cell9_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 5 false ν := by
 have heq : naturalFloor cell9 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_6_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_6_5_g]
def cell9_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(110840373998180/43364944809:ℝ), (222982273852000/43364944809:ℝ), (113009198750000/43364944809:ℝ)]]
theorem cell9_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 5 true ν := by
 have heq : naturalFloor cell9 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_6_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_6_5_g]
def cell9_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(968310820/385641:ℝ), (1949348000/385641:ℝ), (988750000/385641:ℝ)]]
theorem cell9_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_6_5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_6_5_g]
def cell9_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(3438454175000000/5508110403:ℝ), (20409321697900000/16524331209:ℝ), (10053805375000000/16524331209:ℝ)],
  ![(6891419094160000/5508110403:ℝ), (383013342356690980000/154849507759539:ℝ), (188547250390825000000/154849507759539:ℝ)],
  ![(3436903400000000/5508110403:ℝ), (190884436359575000000/154849507759539:ℝ), (93911425343750000000/154849507759539:ℝ)]]
theorem cell9_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 6 5 b ν := by
 have heq : pairedCleared cell9 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_6_5_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_6_5_g]
theorem cell9_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_6_5 hb hν
def cell9_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(4483153240381/381237906265:ℝ)]]
theorem cell9_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell9 6 6) := by
 have heq : (-orderedLow cell9 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell9_ordered_6_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordered_6_6_g]
def cell9_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(93938899294285905952/29404193481988173:ℝ), (189951465768813939800/29404193481988173:ℝ), (96718267118095750000/29404193481988173:ℝ)]]
theorem cell9_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell9 6 6 ν := by
 have heq : mixedLowHigh cell9 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_mixed_6_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_mixed_6_6_g]
def cell9_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(1149584984/385641:ℝ), (2331829600/385641:ℝ), (1191500000/385641:ℝ)]]
theorem cell9_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 6 false ν := by
 have heq : naturalFloor cell9 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor0_6_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor0_6_6_g]
def cell9_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(4896365472808/1606109067:ℝ), (9921554355200/1606109067:ℝ), (5063735500000/1606109067:ℝ)]]
theorem cell9_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell9 6 6 true ν := by
 have heq : naturalFloor cell9 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_floor1_6_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_floor1_6_6_g]
def cell9_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(1149584984/385641:ℝ), (2331829600/385641:ℝ), (1191500000/385641:ℝ)]]
theorem cell9_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell9_complement_floor_6_6_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement_floor_6_6_g]
def cell9_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(108205999900000000/148718980881:ℝ), (215785396467320000/148718980881:ℝ), (107145735550000000/148718980881:ℝ)],
  ![(215785396467320000/148718980881:ℝ), (4028831384205711440000/1393645569835851:ℝ), (1998848062615600000000/1393645569835851:ℝ)],
  ![(107145735550000000/148718980881:ℝ), (1998848062615600000000/1393645569835851:ℝ), (990990840875000000000/1393645569835851:ℝ)]]
theorem cell9_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell9 6 6 b ν := by
 have heq : pairedCleared cell9 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell9_paired_cleared_6_6_g (3129/5000:ℝ) (3/4:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_cleared_6_6_g]
theorem cell9_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell9 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell9_paired_cleared_6_6 hb hν
def cell9_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(24634080561850887/38123790626500000:ℝ)]]
theorem cell9_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell9.q/K)+1+17/50*(cell9.q/cell9.priorL)+17/25*(cell9.q/cell9.priorL)*cell9.priorB) := by
 have heq : ((2-17/50-17/25)*(cell9.q/K)+1+17/50*(cell9.q/cell9.priorL)+17/25*(cell9.q/cell9.priorL)*cell9.priorB) = Record12518109.Bernstein.bsum 0 0 (24634080561850887/38123790626500000:ℝ) cell9_increment0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_increment0_g]
def cell9_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(509017284611/1017095500000:ℝ)]]
theorem cell9_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell9.q/cell9.priorL)*(1-cell9.priorB)) := by
 have heq : (1+17/25*(cell9.q/cell9.priorL)*(1-cell9.priorB)) = Record12518109.Bernstein.bsum 0 0 (509017284611/1017095500000:ℝ) cell9_increment1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_increment1_g]
def cell9_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(2035599603833/4068382000000:ℝ)]]
theorem cell9_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell9.q/cell9.priorL)*(1-cell9.priorB)) := by
 have heq : (1+omega*(cell9.q/cell9.priorL)*(1-cell9.priorB)) = Record12518109.Bernstein.bsum 0 0 (2035599603833/4068382000000:ℝ) cell9_increment2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_increment2_g]
def cell9_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(38678764/385641:ℝ), (76590800/385641:ℝ), (39454600/385641:ℝ)]]
theorem cell9_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (191477/125000:ℝ) cell9_high_increment_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_high_increment_g]
def cell9_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(6881168986/985527:ℝ), (621356343578/8869743:ℝ), (1107558187378/8869743:ℝ), (515881979126/8869743:ℝ)]]
theorem cell9_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (836062031799/62500000000:ℝ) cell9_three_gate0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_three_gate0_g]
def cell9_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(17707082/385641:ℝ), (51207436/385641:ℝ), (35042918/385641:ℝ)]]
theorem cell9_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (8853541/12500000:ℝ) cell9_three_gate1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_three_gate1_g]
def cell9_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(4096943220536/43364944809:ℝ), (8140053794200/43364944809:ℝ), (4216570352900/43364944809:ℝ)]]
theorem cell9_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell9.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell9.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (40700268971/28112250000:ℝ) cell9_three_gate2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_three_gate2_g]
def cell9_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(53617/112449:ℝ)]]
theorem cell9_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (1-cell9.q/K/3) := by
 have heq : (1-cell9.q/K/3) = Record12518109.Bernstein.bsum 0 0 (53617/112449:ℝ) cell9_paired_margin0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_margin0_g]
def cell9_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(8073309/93710000:ℝ)]]
theorem cell9_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (gamma cell9-13/50) := by
 have heq : (gamma cell9-13/50) = Record12518109.Bernstein.bsum 0 0 (8073309/93710000:ℝ) cell9_paired_margin1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_margin1_g]
def cell9_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(7253/74968:ℝ)]]
theorem cell9_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (cell9.q-gamma cell9) := by
 have heq : (cell9.q-gamma cell9) = Record12518109.Bernstein.bsum 0 0 (7253/74968:ℝ) cell9_paired_margin2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_margin2_g]
def cell9_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(197909487/655970000:ℝ)]]
theorem cell9_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < (min (cell9.q+rho cell9.q) (3/4+rho (3/4))-gamma cell9) := by
 have heq : (min (cell9.q+rho cell9.q) (3/4+rho (3/4))-gamma cell9) = Record12518109.Bernstein.bsum 0 0 (197909487/655970000:ℝ) cell9_paired_margin3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_paired_margin3_g]
theorem cell9_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (3129/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell9 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell9_paired_1_1 hb hν
 · exact cell9_paired_1_2 hb hν
 · exact cell9_paired_1_3 hb hν
 · exact cell9_paired_1_4 hb hν
 · exact cell9_paired_1_5 hb hν
 · exact cell9_paired_1_6 hb hν
 · exact cell9_paired_2_1 hb hν
 · exact cell9_paired_2_2 hb hν
 · exact cell9_paired_2_3 hb hν
 · exact cell9_paired_2_4 hb hν
 · exact cell9_paired_2_5 hb hν
 · exact cell9_paired_2_6 hb hν
 · exact cell9_paired_3_1 hb hν
 · exact cell9_paired_3_2 hb hν
 · exact cell9_paired_3_3 hb hν
 · exact cell9_paired_3_4 hb hν
 · exact cell9_paired_3_5 hb hν
 · exact cell9_paired_3_6 hb hν
 · exact cell9_paired_4_1 hb hν
 · exact cell9_paired_4_2 hb hν
 · exact cell9_paired_4_3 hb hν
 · exact cell9_paired_4_4 hb hν
 · exact cell9_paired_4_5 hb hν
 · exact cell9_paired_4_6 hb hν
 · exact cell9_paired_5_1 hb hν
 · exact cell9_paired_5_2 hb hν
 · exact cell9_paired_5_3 hb hν
 · exact cell9_paired_5_4 hb hν
 · exact cell9_paired_5_5 hb hν
 · exact cell9_paired_5_6 hb hν
 · exact cell9_paired_6_1 hb hν
 · exact cell9_paired_6_2 hb hν
 · exact cell9_paired_6_3 hb hν
 · exact cell9_paired_6_4 hb hν
 · exact cell9_paired_6_5 hb hν
 · exact cell9_paired_6_6 hb hν
end
end Record12518109Admission
