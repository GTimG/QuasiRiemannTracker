/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Cell10
import Submissions.hailey_collet_1252270103.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell10_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(1337475262021/4574854875180:ℝ)]]
theorem cell10_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 1 1) := by
 have heq : (-orderedLow cell10 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_1_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_1_1_g]
def cell10_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(44728388517622190656/363728640448804839:ℝ), (34413700477219907100/121242880149601613:ℝ), (59967627475832750000/363728640448804839:ℝ)]]
theorem cell10_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 1 1 ν := by
 have heq : mixedLowHigh cell10 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_1_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_1_1_g]
def cell10_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(140691684/1590121:ℝ), (345331200/1590121:ℝ), (211000000/1590121:ℝ)]]
theorem cell10_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 1 false ν := by
 have heq : naturalFloor cell10 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_1_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_1_1_g]
def cell10_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(4101108574796/41263272999:ℝ), (1092376609200/4584808111:ℝ), (5895334000000/41263272999:ℝ)]]
theorem cell10_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 1 true ν := by
 have heq : naturalFloor cell10 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_1_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_1_1_g]
def cell10_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(140691684/1590121:ℝ), (345331200/1590121:ℝ), (211000000/1590121:ℝ)]]
theorem cell10_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_1_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_1_1_g]
def cell10_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(165355701800000000/7585454383923:ℝ), (124286025703240000/2528484794641:ℝ), (203922504100000000/7585454383923:ℝ)],
  ![(124286025703240000/2528484794641:ℝ), (5150499777893771280000/47436903232259801:ℝ), (2775499746363400000000/47436903232259801:ℝ)],
  ![(203922504100000000/7585454383923:ℝ), (2775499746363400000000/47436903232259801:ℝ), (4438061393500000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 1 1 b ν := by
 have heq : pairedCleared cell10 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_1_1_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_1_1_g]
theorem cell10_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_1_1 hb hν
def cell10_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(156678251055349349/228742743759000000:ℝ)]]
theorem cell10_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 1 2) := by
 have heq : (-orderedLow cell10 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_1_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_1_2_g]
def cell10_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(11402986561463027340967/36372864044880483900:ℝ), (8465890895822624764089/12124288014960161300:ℝ), (142856690383638908225/363728640448804839:ℝ)]]
theorem cell10_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 1 2 ν := by
 have heq : mixedLowHigh cell10 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_1_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_1_2_g]
def cell10_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(281383368/1590121:ℝ), (690662400/1590121:ℝ), (422000000/1590121:ℝ)]]
theorem cell10_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 2 false ν := by
 have heq : naturalFloor cell10 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_1_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_1_2_g]
def cell10_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(281383368/1590121:ℝ), (690662400/1590121:ℝ), (422000000/1590121:ℝ)]]
theorem cell10_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 2 true ν := by
 have heq : naturalFloor cell10 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_1_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_1_2_g]
def cell10_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(281383368/1590121:ℝ), (690662400/1590121:ℝ), (422000000/1590121:ℝ)]]
theorem cell10_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_1_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_1_2_g]
def cell10_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(436303939900000000/7585454383923:ℝ), (316601313506480000/2528484794641:ℝ), (506340258200000000/7585454383923:ℝ)],
  ![(833493065209720000/7585454383923:ℝ), (11361959078927056920000/47436903232259801:ℝ), (18189094420510300000000/142310709696779403:ℝ)],
  ![(131203084700000000/2528484794641:ℝ), (5378931932920100000000/47436903232259801:ℝ), (2875665696750000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 1 2 b ν := by
 have heq : pairedCleared cell10 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_1_2_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_1_2_g]
theorem cell10_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_1_2 hb hν
def cell10_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(436540402198151/57185685939750000:ℝ)]]
theorem cell10_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 1 3) := by
 have heq : (-orderedLow cell10 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_1_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_1_3_g]
def cell10_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(8439241812987635341/699478154709240075:ℝ), (37726879014007390647/233159384903080025:ℝ), (4525405323421816700/27979126188369603:ℝ)]]
theorem cell10_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 1 3 ν := by
 have heq : mixedLowHigh cell10 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_1_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_1_3_g]
def cell10_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(422075052/1590121:ℝ), (1035993600/1590121:ℝ), (633000000/1590121:ℝ)]]
theorem cell10_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 3 false ν := by
 have heq : naturalFloor cell10 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_1_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_1_3_g]
def cell10_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(136533258617044/536422548987:ℝ), (37575301558800/59602505443:ℝ), (208081526000000/536422548987:ℝ)]]
theorem cell10_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 3 true ν := by
 have heq : naturalFloor cell10 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_1_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_1_3_g]
def cell10_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(422075052/1590121:ℝ), (1035993600/1590121:ℝ), (633000000/1590121:ℝ)]]
theorem cell10_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_1_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_1_3_g]
def cell10_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (42237014520000/2005142581:ℝ), (39398100000000/2005142581:ℝ)],
  ![(242237014520000/6015427743:ℝ), (4459475178012960000/37618479962141:ℝ), (8524991266400000000/112855439886423:ℝ)],
  ![(239398100000000/6015427743:ℝ), (3632752588800000000/37618479962141:ℝ), (6257867000000000000/112855439886423:ℝ)]]
theorem cell10_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 1 3 b ν := by
 have heq : pairedCleared cell10 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_1_3_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_1_3_g]
theorem cell10_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_1_3 hb hν
def cell10_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(164748327565971953/228742743759000000:ℝ)]]
theorem cell10_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 1 4) := by
 have heq : (-orderedLow cell10 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_1_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_1_4_g]
def cell10_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(7368988283976165313099/36372864044880483900:ℝ), (6986318556829018367733/12124288014960161300:ℝ), (141719332112289775325/363728640448804839:ℝ)]]
theorem cell10_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 1 4 ν := by
 have heq : mixedLowHigh cell10 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_1_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_1_4_g]
def cell10_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(562766736/1590121:ℝ), (1381324800/1590121:ℝ), (844000000/1590121:ℝ)]]
theorem cell10_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 4 false ν := by
 have heq : naturalFloor cell10 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_1_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_1_4_g]
def cell10_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(178142682189392/536422548987:ℝ), (49262504378400/59602505443:ℝ), (273802618000000/536422548987:ℝ)]]
theorem cell10_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 4 true ν := by
 have heq : naturalFloor cell10 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_1_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_1_4_g]
def cell10_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(562766736/1590121:ℝ), (1381324800/1590121:ℝ), (844000000/1590121:ℝ)]]
theorem cell10_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_1_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_1_4_g]
def cell10_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(270948238100000000/7585454383923:ℝ), (245576163112960000/2528484794641:ℝ), (451460766400000000/7585454383923:ℝ)],
  ![(255365287803240000/2528484794641:ℝ), (11834857500507628200000/47436903232259801:ℝ), (6870869722783500000000/47436903232259801:ℝ)],
  ![(491567754100000000/7585454383923:ℝ), (7184333201033500000000/47436903232259801:ℝ), (12080105983750000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 1 4 b ν := by
 have heq : pairedCleared cell10 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_1_4_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_1_4_g]
theorem cell10_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_1_4 hb hν
def cell10_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(163875246761575651/114371371879500000:ℝ)]]
theorem cell10_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 1 5) := by
 have heq : (-orderedLow cell10 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_1_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_1_5_g]
def cell10_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(7149567996838486794233/18186432022440241950:ℝ), (6005419702464826210911/6062144007480080650:ℝ), (224608395020095933550/363728640448804839:ℝ)]]
theorem cell10_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 1 5 ν := by
 have heq : mixedLowHigh cell10 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_1_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_1_5_g]
def cell10_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(703458420/1590121:ℝ), (1726656000/1590121:ℝ), (1055000000/1590121:ℝ)]]
theorem cell10_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 5 false ν := by
 have heq : naturalFloor cell10 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_1_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_1_5_g]
def cell10_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(73250701920580/178807516329:ℝ), (60949707198000/59602505443:ℝ), (113174570000000/178807516329:ℝ)]]
theorem cell10_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 5 true ν := by
 have heq : naturalFloor cell10 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_1_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_1_5_g]
def cell10_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(703458420/1590121:ℝ), (1726656000/1590121:ℝ), (1055000000/1590121:ℝ)]]
theorem cell10_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_1_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_1_5_g]
def cell10_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(541896476200000000/7585454383923:ℝ), (437891450916200000/2528484794641:ℝ), (753878520500000000/7585454383923:ℝ)],
  ![(1226730851509720000/7585454383923:ℝ), (18046316801540913840000/47436903232259801:ℝ), (30475204349770600000000/142310709696779403:ℝ)],
  ![(227084834700000000/2528484794641:ℝ), (9787765387590200000000/47436903232259801:ℝ), (5423013893500000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 1 5 b ν := by
 have heq : pairedCleared cell10 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_1_5_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_1_5_g]
theorem cell10_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_1_5 hb hν
def cell10_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(1126621170287802839/228742743759000000:ℝ)]]
theorem cell10_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 1 6) := by
 have heq : (-orderedLow cell10 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_1_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_1_6_g]
def cell10_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(35601190293755751863833/36372864044880483900:ℝ), (23732185314481276475911/12124288014960161300:ℝ), (364683143867652091775/363728640448804839:ℝ)]]
theorem cell10_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 1 6 ν := by
 have heq : mixedLowHigh cell10 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_1_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_1_6_g]
def cell10_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(1472450104/1590121:ℝ), (2950287200/1590121:ℝ), (1516000000/1590121:ℝ)]]
theorem cell10_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 6 false ν := by
 have heq : naturalFloor cell10 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_1_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_1_6_g]
def cell10_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(473316649434088/536422548987:ℝ), (105558228917600/59602505443:ℝ), (489581552000000/536422548987:ℝ)]]
theorem cell10_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 1 6 true ν := by
 have heq : naturalFloor cell10 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_1_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_1_6_g]
def cell10_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(1472450104/1590121:ℝ), (2950287200/1590121:ℝ), (1516000000/1590121:ℝ)]]
theorem cell10_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_1_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_1_6_g]
def cell10_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(506698964100000000/2528484794641:ℝ), (959762464719440000/2528484794641:ℝ), (445903758200000000/2528484794641:ℝ)],
  ![(3054333017609720000/7585454383923:ℝ), (36207796283060199480000/47436903232259801:ℝ), (50542188846190700000000/142310709696779403:ℝ)],
  ![(1530656254100000000/7585454383923:ℝ), (18158422779146900000000/47436903232259801:ℝ), (25382739877250000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 1 6 b ν := by
 have heq : pairedCleared cell10 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_1_6_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_1_6_g]
theorem cell10_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_1_6 hb hν
def cell10_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(277260636881980651/228742743759000000:ℝ)]]
theorem cell10_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 2 1) := by
 have heq : (-orderedLow cell10 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_2_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_2_1_g]
def cell10_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(29899689075799893552/121242880149601613:ℝ), (177347560618012211300/363728640448804839:ℝ), (89103407952407750000/363728640448804839:ℝ)]]
theorem cell10_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 2 1 ν := by
 have heq : mixedLowHigh cell10 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_2_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_2_1_g]
def cell10_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(923835052/4770363:ℝ), (1837753600/4770363:ℝ), (311000000/1590121:ℝ)]]
theorem cell10_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 1 false ν := by
 have heq : naturalFloor cell10 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_2_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_2_1_g]
def cell10_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(923835052/4770363:ℝ), (1837753600/4770363:ℝ), (311000000/1590121:ℝ)]]
theorem cell10_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 1 true ν := by
 have heq : naturalFloor cell10 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_2_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_2_1_g]
def cell10_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(923835052/4770363:ℝ), (1837753600/4770363:ℝ), (311000000/1590121:ℝ)]]
theorem cell10_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_2_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_2_1_g]
def cell10_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(436303939900000000/7585454383923:ℝ), (833493065209720000/7585454383923:ℝ), (131203084700000000/2528484794641:ℝ)],
  ![(316601313506480000/2528484794641:ℝ), (11361959078927056920000/47436903232259801:ℝ), (5378931932920100000000/47436903232259801:ℝ)],
  ![(506340258200000000/7585454383923:ℝ), (18189094420510300000000/142310709696779403:ℝ), (2875665696750000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 2 1 b ν := by
 have heq : pairedCleared cell10 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_2_1_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_2_1_g]
theorem cell10_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_2_1 hb hν
def cell10_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(5912330137201/2287427437590:ℝ)]]
theorem cell10_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 2 2) := by
 have heq : (-orderedLow cell10 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_2_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_2_2_g]
def cell10_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(261114481661748341312/363728640448804839:ℝ), (179419942707041134200/121242880149601613:ℝ), (280055175582965500000/363728640448804839:ℝ)]]
theorem cell10_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 2 2 ν := by
 have heq : mixedLowHigh cell10 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_2_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_2_2_g]
def cell10_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1031823368/1590121:ℝ), (2141102400/1590121:ℝ), (1122000000/1590121:ℝ)]]
theorem cell10_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 2 false ν := by
 have heq : naturalFloor cell10 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_2_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_2_2_g]
def cell10_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(359787505624696/536422548987:ℝ), (82768634359200/59602505443:ℝ), (389421584000000/536422548987:ℝ)]]
theorem cell10_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 2 true ν := by
 have heq : naturalFloor cell10 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_2_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_2_2_g]
def cell10_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1031823368/1590121:ℝ), (2141102400/1590121:ℝ), (1122000000/1590121:ℝ)]]
theorem cell10_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_2_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_2_2_g]
def cell10_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(1175451694000000000/7585454383923:ℝ), (792806148206480000/2528484794641:ℝ), (1195807008200000000/7585454383923:ℝ)],
  ![(792806148206480000/2528484794641:ℝ), (30035472139852342560000/47436903232259801:ℝ), (15075096186726800000000/47436903232259801:ℝ)],
  ![(1195807008200000000/7585454383923:ℝ), (15075096186726800000000/47436903232259801:ℝ), (22665457787000000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 2 2 b ν := by
 have heq : pairedCleared cell10 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_2_2_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_2_2_g]
theorem cell10_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_2_2 hb hν
def cell10_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(681037501674399349/228742743759000000:ℝ)]]
theorem cell10_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 2 3) := by
 have heq : (-orderedLow cell10 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_2_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_2_3_g]
def cell10_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(33041595875875642406567/36372864044880483900:ℝ), (22966515118804747474089/12124288014960161300:ℝ), (362944238490771658225/363728640448804839:ℝ)]]
theorem cell10_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 2 3 ν := by
 have heq : mixedLowHigh cell10 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_2_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_2_3_g]
def cell10_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(1172515052/1590121:ℝ), (2486433600/1590121:ℝ), (1333000000/1590121:ℝ)]]
theorem cell10_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 3 false ν := by
 have heq : naturalFloor cell10 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_2_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_2_3_g]
def cell10_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(401396929197044/536422548987:ℝ), (94455837178800/59602505443:ℝ), (455142676000000/536422548987:ℝ)]]
theorem cell10_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 3 true ν := by
 have heq : naturalFloor cell10 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_2_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_2_3_g]
def cell10_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(1172515052/1590121:ℝ), (2486433600/1590121:ℝ), (1333000000/1590121:ℝ)]]
theorem cell10_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_2_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_2_3_g]
def cell10_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(482133310700000000/2528484794641:ℝ), (985121436009720000/2528484794641:ℝ), (499408254100000000/2528484794641:ℝ)],
  ![(2839053432719440000/7585454383923:ℝ), (36246931440885628200000/47436903232259801:ℝ), (55087883741600500000000/142310709696779403:ℝ)],
  ![(1385493758200000000/7585454383923:ℝ), (17678528373283500000000/47436903232259801:ℝ), (26854393483750000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 2 3 b ν := by
 have heq : pairedCleared cell10 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_2_3_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_2_3_g]
theorem cell10_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_2_3 hb hν
def cell10_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(131526353056960651/57185685939750000:ℝ)]]
theorem cell10_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 2 4) := by
 have heq : (-orderedLow cell10 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_2_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_2_4_g]
def cell10_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(5519362472171993025833/9093216011220120975:ℝ), (4115605482927626755911/3031072003740040325:ℝ), (278917817311616367100/363728640448804839:ℝ)]]
theorem cell10_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 2 4 ν := by
 have heq : mixedLowHigh cell10 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_2_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_2_4_g]
def cell10_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1313206736/1590121:ℝ), (2831764800/1590121:ℝ), (1544000000/1590121:ℝ)]]
theorem cell10_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 4 false ν := by
 have heq : naturalFloor cell10 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_2_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_2_4_g]
def cell10_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1313206736/1590121:ℝ), (2831764800/1590121:ℝ), (1544000000/1590121:ℝ)]]
theorem cell10_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 4 true ν := by
 have heq : naturalFloor cell10 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_2_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_2_4_g]
def cell10_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1313206736/1590121:ℝ), (2831764800/1590121:ℝ), (1544000000/1590121:ℝ)]]
theorem cell10_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_2_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_2_4_g]
def cell10_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(1010095992200000000/7585454383923:ℝ), (721780997812960000/2528484794641:ℝ), (1140927516400000000/7585454383923:ℝ)],
  ![(2311021242819440000/7585454383923:ℝ), (30508370561432913840000/47436903232259801:ℝ), (47648803308020600000000/142310709696779403:ℝ)],
  ![(431255169400000000/2528484794641:ℝ), (16880497454840200000000/47436903232259801:ℝ), (8706188893500000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 2 4 b ν := by
 have heq : pairedCleared cell10 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_2_4_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_2_4_g]
theorem cell10_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_2_4 hb hν
def cell10_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(689107578185021953/228742743759000000:ℝ)]]
theorem cell10_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 2 5) := by
 have heq : (-orderedLow cell10 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_2_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_2_5_g]
def cell10_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(29007597598388780378699/36372864044880483900:ℝ), (21486942779811141077733/12124288014960161300:ℝ), (361806880219422525325/363728640448804839:ℝ)]]
theorem cell10_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 2 5 ν := by
 have heq : mixedLowHigh cell10 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_2_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_2_5_g]
def cell10_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(111838340/122317:ℝ), (244392000/122317:ℝ), (135000000/122317:ℝ)]]
theorem cell10_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 5 false ν := by
 have heq : naturalFloor cell10 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_2_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_2_5_g]
def cell10_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(484615776341740/536422548987:ℝ), (117830242818000/59602505443:ℝ), (586584860000000/536422548987:ℝ)]]
theorem cell10_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 5 true ν := by
 have heq : naturalFloor cell10 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_2_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_2_5_g]
def cell10_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(111838340/122317:ℝ), (244392000/122317:ℝ), (135000000/122317:ℝ)]]
theorem cell10_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_2_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_2_5_g]
def cell10_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(1281044230300000000/7585454383923:ℝ), (914096285616200000/2528484794641:ℝ), (1443345270500000000/7585454383923:ℝ)],
  ![(923885410306480000/2528484794641:ℝ), (36719829862466199480000/47436903232259801:ℝ), (19170466163146900000000/47436903232259801:ℝ)],
  ![(1483452258200000000/7585454383923:ℝ), (19483929641396900000000/47436903232259801:ℝ), (30307502377250000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 2 5 b ν := by
 have heq : pairedCleared cell10 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_2_5_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_2_5_g]
theorem cell10_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_2_5 hb hν
def cell10_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(426054872071100651/114371371879500000:ℝ)]]
theorem cell10_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 2 6) := by
 have heq : (-orderedLow cell10 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_2_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_2_6_g]
def cell10_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(17968872654044794327033/18186432022440241950:ℝ), (13255731813955887565911/6062144007480080650:ℝ), (444695943127228683550/363728640448804839:ℝ)]]
theorem cell10_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 2 6 ν := by
 have heq : mixedLowHigh cell10 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_2_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_2_6_g]
def cell10_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1594590104/1590121:ℝ), (3522427200/1590121:ℝ), (1966000000/1590121:ℝ)]]
theorem cell10_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 6 false ν := by
 have heq : naturalFloor cell10 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_2_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_2_6_g]
def cell10_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(526225199914088/536422548987:ℝ), (129517445637600/59602505443:ℝ), (652305952000000/536422548987:ℝ)]]
theorem cell10_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 2 6 true ν := by
 have heq : naturalFloor cell10 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_2_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_2_6_g]
def cell10_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1594590104/1590121:ℝ), (3522427200/1590121:ℝ), (1966000000/1590121:ℝ)]]
theorem cell10_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_2_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_2_6_g]
def cell10_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(517330822800000000/2528484794641:ℝ), (1106411573419440000/2528484794641:ℝ), (581921008200000000/2528484794641:ℝ)],
  ![(3232291219019440000/7585454383923:ℝ), (42931289163499485120000/47436903232259801:ℝ), (67373993670860800000000/142310709696779403:ℝ)],
  ![(1673139008200000000/7585454383923:ℝ), (22087361827953600000000/47436903232259801:ℝ), (34496438074000000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 2 6 b ν := by
 have heq : pairedCleared cell10 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_2_6_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_2_6_g]
theorem cell10_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_2_6 hb hν
def cell10_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(458201789396519/38123790626500000:ℝ)]]
theorem cell10_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 3 1) := by
 have heq : (-orderedLow cell10 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_3_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_3_1_g]
def cell10_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(33006817666890940856/363728640448804839:ℝ), (131834786148996971500/363728640448804839:ℝ), (100282883043901250000/363728640448804839:ℝ)]]
theorem cell10_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 3 1 ν := by
 have heq : mixedLowHigh cell10 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_3_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_3_1_g]
def cell10_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(666355052/4770363:ℝ), (2180273600/4770363:ℝ), (511000000/1590121:ℝ)]]
theorem cell10_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 1 false ν := by
 have heq : naturalFloor cell10 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_3_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_3_1_g]
def cell10_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(69078465292348/536422548987:ℝ), (77952655698800/178807516329:ℝ), (166925192000000/536422548987:ℝ)]]
theorem cell10_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 1 true ν := by
 have heq : naturalFloor cell10 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_3_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_3_1_g]
def cell10_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(103525052/4770363:ℝ), (1092443600/4770363:ℝ), (336000000/1590121:ℝ)]]
theorem cell10_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_3_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_3_1_g]
def cell10_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (242237014520000/6015427743:ℝ), (239398100000000/6015427743:ℝ)],
  ![(42237014520000/2005142581:ℝ), (4459475178012960000/37618479962141:ℝ), (3632752588800000000/37618479962141:ℝ)],
  ![(39398100000000/2005142581:ℝ), (8524991266400000000/112855439886423:ℝ), (6257867000000000000/112855439886423:ℝ)]]
theorem cell10_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 3 1 b ν := by
 have heq : pairedCleared cell10 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_3_1_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_3_1_g]
theorem cell10_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_3_1 hb hν
def cell10_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(267206629167010217/76247581253000000:ℝ)]]
theorem cell10_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 3 2) := by
 have heq : (-orderedLow cell10 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_3_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_3_2_g]
def cell10_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(306085160371525831312/363728640448804839:ℝ), (612366287307475892600/363728640448804839:ℝ), (309190956059540500000/363728640448804839:ℝ)]]
theorem cell10_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 3 2 ν := by
 have heq : mixedLowHigh cell10 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_3_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_3_2_g]
def cell10_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(276710008/366951:ℝ), (555774400/366951:ℝ), (94000000/122317:ℝ)]]
theorem cell10_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 2 false ν := by
 have heq : naturalFloor cell10 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_3_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_3_2_g]
def cell10_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(410357421914696/536422548987:ℝ), (274587733507600/178807516329:ℝ), (417697159000000/536422548987:ℝ)]]
theorem cell10_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 2 true ν := by
 have heq : naturalFloor cell10 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_3_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_3_2_g]
def cell10_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(276710008/366951:ℝ), (555774400/366951:ℝ), (94000000/122317:ℝ)]]
theorem cell10_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_3_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_3_2_g]
def cell10_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(482133310700000000/2528484794641:ℝ), (2839053432719440000/7585454383923:ℝ), (1385493758200000000/7585454383923:ℝ)],
  ![(985121436009720000/2528484794641:ℝ), (36246931440885628200000/47436903232259801:ℝ), (17678528373283500000000/47436903232259801:ℝ)],
  ![(499408254100000000/2528484794641:ℝ), (55087883741600500000000/142310709696779403:ℝ), (26854393483750000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 3 2 b ν := by
 have heq : pairedCleared cell10 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_3_2_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_3_2_g]
theorem cell10_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_3_2 hb hν
def cell10_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(7437281762261/1524951625060:ℝ)]]
theorem cell10_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 3 3) := by
 have heq : (-orderedLow cell10 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_3_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_3_3_g]
def cell10_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(159166858268624830656/121242880149601613:ℝ), (324426184936862361300/121242880149601613:ℝ), (166714241230032750000/121242880149601613:ℝ)]]
theorem cell10_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 3 3 ν := by
 have heq : mixedLowHigh cell10 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_3_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_3_3_g]
def cell10_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1922955052/1590121:ℝ), (3936873600/1590121:ℝ), (2033000000/1590121:ℝ)]]
theorem cell10_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 3 false ν := by
 have heq : naturalFloor cell10 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_3_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_3_3_g]
def cell10_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(222086866592348/178807516329:ℝ), (151336372798800/59602505443:ℝ), (234067942000000/178807516329:ℝ)]]
theorem cell10_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 3 true ν := by
 have heq : naturalFloor cell10 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_3_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_3_3_g]
def cell10_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1922955052/1590121:ℝ), (3936873600/1590121:ℝ), (2033000000/1590121:ℝ)]]
theorem cell10_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_3_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_3_3_g]
def cell10_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(728515895400000000/2528484794641:ℝ), (1461326270709720000/2528484794641:ℝ), (729230504100000000/2528484794641:ℝ)],
  ![(1461326270709720000/2528484794641:ℝ), (54920444501810913840000/47436903232259801:ℝ), (27374692627090200000000/47436903232259801:ℝ)],
  ![(729230504100000000/2528484794641:ℝ), (27374692627090200000000/47436903232259801:ℝ), (13630951393500000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 3 3 b ν := by
 have heq : pairedCleared cell10 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_3_3_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_3_3_g]
theorem cell10_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_3_3 hb hν
def cell10_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(401798917431149783/76247581253000000:ℝ)]]
theorem cell10_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 3 4) := by
 have heq : (-orderedLow cell10 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_3_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_3_4_g]
def cell10_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(18226735063429419157389/12124288014960161300:ℝ), (37467139341786870184089/12124288014960161300:ℝ), (194343928865968136075/121242880149601613:ℝ)]]
theorem cell10_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 3 4 ν := by
 have heq : mixedLowHigh cell10 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_3_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_3_4_g]
def cell10_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2063646736/1590121:ℝ), (4282204800/1590121:ℝ), (2244000000/1590121:ℝ)]]
theorem cell10_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 4 false ν := by
 have heq : naturalFloor cell10 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_3_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_3_4_g]
def cell10_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(707870023349392/536422548987:ℝ), (163023575618400/59602505443:ℝ), (767924918000000/536422548987:ℝ)]]
theorem cell10_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 4 true ν := by
 have heq : naturalFloor cell10 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_3_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_3_4_g]
def cell10_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2063646736/1590121:ℝ), (4282204800/1590121:ℝ), (2244000000/1590121:ℝ)]]
theorem cell10_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_3_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_3_4_g]
def cell10_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(2456495924300000000/7585454383923:ℝ), (1653641558512960000/2528484794641:ℝ), (2490109266400000000/7585454383923:ℝ)],
  ![(4844613800229160000/7585454383923:ℝ), (61131903802844199480000/47436903232259801:ℝ), (91986673062690700000000/142310709696779403:ℝ)],
  ![(2377378262300000000/7585454383923:ℝ), (29978124813646900000000/47436903232259801:ℝ), (45081789877250000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 3 4 b ν := by
 have heq : pairedCleared cell10 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_3_4_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_3_4_g]
theorem cell10_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_3_4 hb hν
def cell10_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(87538721903907717/19061895313250000:ℝ)]]
theorem cell10_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 3 5) := by
 have heq : (-orderedLow cell10 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_3_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_3_5_g]
def cell10_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(3643004933591715597411/3031072003740040325:ℝ), (7740761538673157433411/3031072003740040325:ℝ), (166335121806249705700/121242880149601613:ℝ)]]
theorem cell10_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 3 5 ν := by
 have heq : mixedLowHigh cell10 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_3_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_3_5_g]
def cell10_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(2204338420/1590121:ℝ), (4627536000/1590121:ℝ), (2455000000/1590121:ℝ)]]
theorem cell10_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 5 false ν := by
 have heq : naturalFloor cell10 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_3_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_3_5_g]
def cell10_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(749479446921740/536422548987:ℝ), (174710778438000/59602505443:ℝ), (833646010000000/536422548987:ℝ)]]
theorem cell10_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 5 true ν := by
 have heq : naturalFloor cell10 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_3_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_3_5_g]
def cell10_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(2204338420/1590121:ℝ), (4627536000/1590121:ℝ), (2455000000/1590121:ℝ)]]
theorem cell10_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_3_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_3_5_g]
def cell10_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(2020191984400000000/7585454383923:ℝ), (1390301120316200000/2528484794641:ℝ), (2132812020500000000/7585454383923:ℝ)],
  ![(4316581610329160000/7585454383923:ℝ), (55393342923391485120000/47436903232259801:ℝ), (84547592629110800000000/142310709696779403:ℝ)],
  ![(2285650012300000000/7585454383923:ℝ), (29180093895203600000000/47436903232259801:ℝ), (44345963074000000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 3 5 b ν := by
 have heq : pairedCleared cell10 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_3_5_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_3_5_g]
theorem cell10_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_3_5 hb hν
def cell10_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(404488942934690651/76247581253000000:ℝ)]]
theorem cell10_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 3 6) := by
 have heq : (-orderedLow cell10 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_3_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_3_6_g]
def cell10_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(16882068970933798481433/12124288014960161300:ℝ), (35987567002793263787733/12124288014960161300:ℝ), (193964809442185091775/121242880149601613:ℝ)]]
theorem cell10_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 3 6 ν := by
 have heq : mixedLowHigh cell10 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_3_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_3_6_g]
def cell10_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2345030104/1590121:ℝ), (4972867200/1590121:ℝ), (2666000000/1590121:ℝ)]]
theorem cell10_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 6 false ν := by
 have heq : naturalFloor cell10 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_3_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_3_6_g]
def cell10_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2345030104/1590121:ℝ), (4972867200/1590121:ℝ), (2666000000/1590121:ℝ)]]
theorem cell10_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 3 6 true ν := by
 have heq : naturalFloor cell10 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_3_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_3_6_g]
def cell10_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2345030104/1590121:ℝ), (4972867200/1590121:ℝ), (2666000000/1590121:ℝ)]]
theorem cell10_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_3_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_3_6_g]
def cell10_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(763713407500000000/2528484794641:ℝ), (1582616408119440000/2528484794641:ℝ), (811743258200000000/2528484794641:ℝ)],
  ![(1592405532809720000/2528484794641:ℝ), (61604802224424770760000/47436903232259801:ℝ), (31470062603510300000000/47436903232259801:ℝ)],
  ![(825112254100000000/2528484794641:ℝ), (31783526081760300000000/47436903232259801:ℝ), (16178299590250000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 3 6 b ν := by
 have heq : pairedCleared cell10 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_3_6_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_3_6_g]
theorem cell10_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_3_6 hb hν
def cell10_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(72821259079649953/45748548751800000:ℝ)]]
theorem cell10_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 4 1) := by
 have heq : (-orderedLow cell10 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_4_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_4_1_g]
def cell10_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(120033634010161901056/363728640448804839:ℝ), (95742254507837143900/121242880149601613:ℝ), (168648044075144750000/363728640448804839:ℝ)]]
theorem cell10_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 4 1 ν := by
 have heq : mixedLowHigh cell10 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_4_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_4_1_g]
def cell10_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(764591684/1590121:ℝ), (1719231200/1590121:ℝ), (961000000/1590121:ℝ)]]
theorem cell10_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 1 false ν := by
 have heq : naturalFloor cell10 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_4_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_4_1_g]
def cell10_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(246227722922348/536422548987:ℝ), (61928249969600/59602505443:ℝ), (313272217000000/536422548987:ℝ)]]
theorem cell10_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 1 true ν := by
 have heq : naturalFloor cell10 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_4_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_4_1_g]
def cell10_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(29951668/122317:ℝ), (76462400/122317:ℝ), (47000000/122317:ℝ)]]
theorem cell10_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_4_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_4_1_g]
def cell10_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(270948238100000000/7585454383923:ℝ), (255365287803240000/2528484794641:ℝ), (491567754100000000/7585454383923:ℝ)],
  ![(245576163112960000/2528484794641:ℝ), (11834857500507628200000/47436903232259801:ℝ), (7184333201033500000000/47436903232259801:ℝ)],
  ![(451460766400000000/7585454383923:ℝ), (6870869722783500000000/47436903232259801:ℝ), (12080105983750000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 4 1 b ν := by
 have heq : pairedCleared cell10 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_4_1_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_4_1_g]
theorem cell10_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_4_1 hb hν
def cell10_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(263554230677714557/114371371879500000:ℝ)]]
theorem cell10_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 4 2) := by
 have heq : (-orderedLow cell10 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_4_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_4_2_g]
def cell10_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(83130970270339030504/121242880149601613:ℝ), (566853512838460652800/363728640448804839:ℝ), (320370431151034000000/363728640448804839:ℝ)]]
theorem cell10_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 4 2 ν := by
 have heq : mixedLowHigh cell10 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_4_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_4_2_g]
def cell10_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(3339750104/4770363:ℝ), (7567587200/4770363:ℝ), (1422000000/1590121:ℝ)]]
theorem cell10_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 2 false ν := by
 have heq : naturalFloor cell10 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_4_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_4_2_g]
def cell10_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(3339750104/4770363:ℝ), (7567587200/4770363:ℝ), (1422000000/1590121:ℝ)]]
theorem cell10_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 2 true ν := by
 have heq : naturalFloor cell10 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_4_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_4_2_g]
def cell10_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(1050713368/1590121:ℝ), (7204977200/4770363:ℝ), (4091000000/4770363:ℝ)]]
theorem cell10_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_4_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_4_2_g]
def cell10_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(1010095992200000000/7585454383923:ℝ), (2311021242819440000/7585454383923:ℝ), (431255169400000000/2528484794641:ℝ)],
  ![(721780997812960000/2528484794641:ℝ), (30508370561432913840000/47436903232259801:ℝ), (16880497454840200000000/47436903232259801:ℝ)],
  ![(1140927516400000000/7585454383923:ℝ), (47648803308020600000000/142310709696779403:ℝ), (8706188893500000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 4 2 b ν := by
 have heq : pairedCleared cell10 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_4_2_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_4_2_g]
theorem cell10_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_4_2 hb hν
def cell10_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(1325979138120080651/228742743759000000:ℝ)]]
theorem cell10_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 4 3) := by
 have heq : (-orderedLow cell10 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_4_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_4_3_g]
def cell10_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(522471253515651981968/363728640448804839:ℝ), (1047385013996939573900/363728640448804839:ℝ), (176426168055557750000/121242880149601613:ℝ)]]
theorem cell10_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 4 3 ν := by
 have heq : mixedLowHigh cell10 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_4_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_4_3_g]
def cell10_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(6270625156/4770363:ℝ), (12612380800/4770363:ℝ), (2133000000/1590121:ℝ)]]
theorem cell10_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 3 false ν := by
 have heq : naturalFloor cell10 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_4_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_4_3_g]
def cell10_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(716830516067044/536422548987:ℝ), (480290948826400/178807516329:ℝ), (730479401000000/536422548987:ℝ)]]
theorem cell10_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 3 true ν := by
 have heq : naturalFloor cell10 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_4_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_4_3_g]
def cell10_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(6270625156/4770363:ℝ), (12612380800/4770363:ℝ), (2133000000/1590121:ℝ)]]
theorem cell10_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_4_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_4_3_g]
def cell10_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(2456495924300000000/7585454383923:ℝ), (4844613800229160000/7585454383923:ℝ), (2377378262300000000/7585454383923:ℝ)],
  ![(1653641558512960000/2528484794641:ℝ), (61131903802844199480000/47436903232259801:ℝ), (29978124813646900000000/47436903232259801:ℝ)],
  ![(2490109266400000000/7585454383923:ℝ), (91986673062690700000000/142310709696779403:ℝ), (45081789877250000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 4 3 b ν := by
 have heq : pairedCleared cell10 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_4_3_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_4_3_g]
theorem cell10_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_4_3 hb hν
def cell10_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(8199757574791/1143713718795:ℝ)]]
theorem cell10_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 4 4) := by
 have heq : (-orderedLow cell10 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_4_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_4_4_g]
def cell10_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(53375897534615434048/27979126188369603:ℝ), (36110186705129506800/9326375396123201:ℝ), (4261717584599000000/2152240476028431:ℝ)]]
theorem cell10_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 4 4 ν := by
 have heq : mixedLowHigh cell10 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_4_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_4_4_g]
def cell10_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(2814086736/1590121:ℝ), (5732644800/1590121:ℝ), (2944000000/1590121:ℝ)]]
theorem cell10_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 4 false ν := by
 have heq : naturalFloor cell10 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_4_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_4_4_g]
def cell10_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(972733693929392/536422548987:ℝ), (219904111238400/59602505443:ℝ), (1014986068000000/536422548987:ℝ)]]
theorem cell10_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 4 true ν := by
 have heq : naturalFloor cell10 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_4_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_4_4_g]
def cell10_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(2814086736/1590121:ℝ), (5732644800/1590121:ℝ), (2944000000/1590121:ℝ)]]
theorem cell10_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_4_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_4_4_g]
def cell10_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(3195643678400000000/7585454383923:ℝ), (2129846393212960000/2528484794641:ℝ), (3179576016400000000/7585454383923:ℝ)],
  ![(2129846393212960000/2528484794641:ℝ), (79805416863769485120000/47436903232259801:ℝ), (39674289067453600000000/47436903232259801:ℝ)],
  ![(3179576016400000000/7585454383923:ℝ), (39674289067453600000000/47436903232259801:ℝ), (59120250574000000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 4 4 b ν := by
 have heq : pairedCleared cell10 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_4_4_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_4_4_g]
theorem cell10_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_4_4 hb hν
def cell10_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(1729756002912499349/228742743759000000:ℝ)]]
theorem cell10_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 4 5) := by
 have heq : (-orderedLow cell10 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_4_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_4_5_g]
def cell10_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(76318814504700872537767/36372864044880483900:ℝ), (51967763564768992894089/12124288014960161300:ℝ), (803119334705037158225/363728640448804839:ℝ)]]
theorem cell10_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 4 5 ν := by
 have heq : mixedLowHigh cell10 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_4_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_4_5_g]
def cell10_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(2954778420/1590121:ℝ), (6077976000/1590121:ℝ), (3155000000/1590121:ℝ)]]
theorem cell10_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 5 false ν := by
 have heq : naturalFloor cell10 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_4_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_4_5_g]
def cell10_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(26008797884660/13754424333:ℝ), (17814716466000/4584808111:ℝ), (27710440000000/13754424333:ℝ)]]
theorem cell10_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 5 true ν := by
 have heq : naturalFloor cell10 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_4_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_4_5_g]
def cell10_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(2954778420/1590121:ℝ), (6077976000/1590121:ℝ), (3155000000/1590121:ℝ)]]
theorem cell10_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_4_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_4_5_g]
def cell10_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(3466591916500000000/7585454383923:ℝ), (2322161681016200000/2528484794641:ℝ), (3481993770500000000/7585454383923:ℝ)],
  ![(6850174167738880000/7585454383923:ℝ), (86016876164802770760000/47436903232259801:ℝ), (128885462383780900000000/142310709696779403:ℝ)],
  ![(1123087588800000000/2528484794641:ℝ), (42277721254010300000000/47436903232259801:ℝ), (21103062090250000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 4 5 b ν := by
 have heq : pairedCleared cell10 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_4_5_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_4_5_g]
theorem cell10_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_4_5 hb hν
def cell10_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(393705978366485651/57185685939750000:ℝ)]]
theorem cell10_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 4 6) := by
 have heq : (-orderedLow cell10 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_4_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_4_6_g]
def cell10_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(16338667129378300558633/9093216011220120975:ℝ), (11365917594418688110911/3031072003740040325:ℝ), (719092913525881867100/363728640448804839:ℝ)]]
theorem cell10_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 4 6 ν := by
 have heq : mixedLowHigh cell10 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_4_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_4_6_g]
def cell10_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3095470104/1590121:ℝ), (6423307200/1590121:ℝ), (3366000000/1590121:ℝ)]]
theorem cell10_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 6 false ν := by
 have heq : naturalFloor cell10 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_4_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_4_6_g]
def cell10_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(1055952541074088/536422548987:ℝ), (243278516877600/59602505443:ℝ), (1146428252000000/536422548987:ℝ)]]
theorem cell10_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 4 6 true ν := by
 have heq : naturalFloor cell10 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_4_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_4_6_g]
def cell10_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3095470104/1590121:ℝ), (6423307200/1590121:ℝ), (3366000000/1590121:ℝ)]]
theorem cell10_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_4_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_4_6_g]
def cell10_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(1010095992200000000/2528484794641:ℝ), (2058821242819440000/2528484794641:ℝ), (1041565508200000000/2528484794641:ℝ)],
  ![(6322141977838880000/7585454383923:ℝ), (80278315285350056400000/47436903232259801:ℝ), (121446381950201000000000/142310709696779403:ℝ)],
  ![(3277534516400000000/7585454383923:ℝ), (41479690335567000000000/47436903232259801:ℝ), (62573359467500000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 4 6 b ν := by
 have heq : pairedCleared cell10 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_4_6_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_4_6_g]
theorem cell10_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_4_6 hb hν
def cell10_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(22670730626878763/7148210742468750:ℝ)]]
theorem cell10_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 5 1) := by
 have heq : (-orderedLow cell10 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_5_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_5_1_g]
def cell10_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(69020150117810953752/121242880149601613:ℝ), (442618740898025891900/363728640448804839:ℝ), (237013205106388250000/363728640448804839:ℝ)]]
theorem cell10_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 5 1 ν := by
 have heq : mixedLowHigh cell10 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_5_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_5_1_g]
def cell10_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(3921195052/4770363:ℝ), (8135113600/4770363:ℝ), (1411000000/1590121:ℝ)]]
theorem cell10_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 1 false ν := by
 have heq : naturalFloor cell10 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_5_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_5_1_g]
def cell10_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(141125660184116/178807516329:ℝ), (293616844118800/178807516329:ℝ), (153206414000000/178807516329:ℝ)]]
theorem cell10_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 1 true ν := by
 have heq : naturalFloor cell10 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_5_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_5_1_g]
def cell10_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(2232705052/4770363:ℝ), (4871623600/4770363:ℝ), (886000000/1590121:ℝ)]]
theorem cell10_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_5_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_5_1_g]
def cell10_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(541896476200000000/7585454383923:ℝ), (1226730851509720000/7585454383923:ℝ), (227084834700000000/2528484794641:ℝ)],
  ![(437891450916200000/2528484794641:ℝ), (18046316801540913840000/47436903232259801:ℝ), (9787765387590200000000/47436903232259801:ℝ)],
  ![(753878520500000000/7585454383923:ℝ), (30475204349770600000000/142310709696779403:ℝ), (5423013893500000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 5 1 b ν := by
 have heq : pairedCleared cell10 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_5_1_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_5_1_g]
theorem cell10_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_5_1 hb hν
def cell10_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(177693109203459953/45748548751800000:ℝ)]]
theorem cell10_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 5 2) := by
 have heq : (-orderedLow cell10 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_5_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_5_2_g]
def cell10_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(336419727154288051712/363728640448804839:ℝ), (240748496737658371000/121242880149601613:ℝ), (388735592182277500000/363728640448804839:ℝ)]]
theorem cell10_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 5 2 ν := by
 have heq : mixedLowHigh cell10 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_5_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_5_2_g]
def cell10_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(127363336/122317:ℝ), (270384800/122317:ℝ), (144000000/122317:ℝ)]]
theorem cell10_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 2 false ν := by
 have heq : naturalFloor cell10 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_5_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_5_2_g]
def cell10_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(552700817074696/536422548987:ℝ), (130495988409200/59602505443:ℝ), (626054459000000/536422548987:ℝ)]]
theorem cell10_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 2 true ν := by
 have heq : naturalFloor cell10 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_5_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_5_2_g]
def cell10_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(4216730104/4770363:ℝ), (3031522400/1590121:ℝ), (4916000000/4770363:ℝ)]]
theorem cell10_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_5_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_5_2_g]
def cell10_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(1281044230300000000/7585454383923:ℝ), (923885410306480000/2528484794641:ℝ), (1483452258200000000/7585454383923:ℝ)],
  ![(914096285616200000/2528484794641:ℝ), (36719829862466199480000/47436903232259801:ℝ), (19483929641396900000000/47436903232259801:ℝ)],
  ![(1443345270500000000/7585454383923:ℝ), (19170466163146900000000/47436903232259801:ℝ), (30307502377250000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 5 2 b ν := by
 have heq : pairedCleared cell10 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_5_2_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_5_2_g]
theorem cell10_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_5_2 hb hν
def cell10_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(525733855987239557/114371371879500000:ℝ)]]
theorem cell10_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 5 3) := by
 have heq : (-orderedLow cell10 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_5_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_5_3_g]
def cell10_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(465779003955143242168/363728640448804839:ℝ), (1001872239527924334100/363728640448804839:ℝ), (180152659752722250000/121242880149601613:ℝ)]]
theorem cell10_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 5 3 ν := by
 have heq : mixedLowHigh cell10 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_5_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_5_3_g]
def cell10_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(6013145156/4770363:ℝ), (12954900800/4770363:ℝ), (2333000000/1590121:ℝ)]]
theorem cell10_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 3 false ν := by
 have heq : naturalFloor cell10 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_5_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_5_3_g]
def cell10_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(682024653597044/536422548987:ℝ), (489359086336400/178807516329:ℝ), (792489676000000/536422548987:ℝ)]]
theorem cell10_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 3 true ν := by
 have heq : naturalFloor cell10 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_5_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_5_3_g]
def cell10_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(6013145156/4770363:ℝ), (12954900800/4770363:ℝ), (2333000000/1590121:ℝ)]]
theorem cell10_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_5_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_5_3_g]
def cell10_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(2020191984400000000/7585454383923:ℝ), (4316581610329160000/7585454383923:ℝ), (2285650012300000000/7585454383923:ℝ)],
  ![(1390301120316200000/2528484794641:ℝ), (55393342923391485120000/47436903232259801:ℝ), (29180093895203600000000/47436903232259801:ℝ)],
  ![(2132812020500000000/7585454383923:ℝ), (84547592629110800000000/142310709696779403:ℝ), (44345963074000000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 5 3 b ν := by
 have heq : pairedCleared cell10 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_5_3_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_5_3_g]
theorem cell10_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_5_3 hb hν
def cell10_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(1850338388739130651/228742743759000000:ℝ)]]
theorem cell10_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 5 4) := by
 have heq : (-orderedLow cell10 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_5_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_5_4_g]
def cell10_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(246285782219926044208/121242880149601613:ℝ), (1482403740686403255200/363728640448804839:ℝ), (749366052273806000000/363728640448804839:ℝ)]]
theorem cell10_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 5 4 ν := by
 have heq : mixedLowHigh cell10 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_5_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_5_4_g]
def cell10_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(8944020208/4770363:ℝ), (17999694400/4770363:ℝ), (3044000000/1590121:ℝ)]]
theorem cell10_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 4 false ν := by
 have heq : naturalFloor cell10 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_5_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_5_4_g]
def cell10_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(113700401135488/59602505443:ℝ), (685994164145200/178807516329:ℝ), (347753881000000/178807516329:ℝ)]]
theorem cell10_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 4 true ν := by
 have heq : naturalFloor cell10 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_5_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_5_4_g]
def cell10_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(8944020208/4770363:ℝ), (17999694400/4770363:ℝ), (3044000000/1590121:ℝ)]]
theorem cell10_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_5_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_5_4_g]
def cell10_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(3466591916500000000/7585454383923:ℝ), (6850174167738880000/7585454383923:ℝ), (1123087588800000000/2528484794641:ℝ)],
  ![(2322161681016200000/2528484794641:ℝ), (86016876164802770760000/47436903232259801:ℝ), (42277721254010300000000/47436903232259801:ℝ)],
  ![(3481993770500000000/7585454383923:ℝ), (128885462383780900000000/142310709696779403:ℝ), (21103062090250000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 5 4 b ν := by
 have heq : pairedCleared cell10 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_5_4_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_5_4_g]
theorem cell10_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_5_4 hb hν
def cell10_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(8657243062309/914970975036:ℝ)]]
theorem cell10_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 5 5) := by
 have heq : (-orderedLow cell10 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_5_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_5_5_g]
def cell10_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(910272761094126793280/363728640448804839:ℝ), (614438669396504815500/121242880149601613:ℝ), (940317819904363750000/363728640448804839:ℝ)]]
theorem cell10_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 5 5 ν := by
 have heq : mixedLowHigh cell10 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_5_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_5_5_g]
def cell10_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(3705218420/1590121:ℝ), (7528416000/1590121:ℝ), (3855000000/1590121:ℝ)]]
theorem cell10_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 5 false ν := by
 have heq : naturalFloor cell10 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_5_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_5_5_g]
def cell10_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(1279206788081740/536422548987:ℝ), (288471849678000/59602505443:ℝ), (1327768310000000/536422548987:ℝ)]]
theorem cell10_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 5 true ν := by
 have heq : naturalFloor cell10 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_5_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_5_5_g]
def cell10_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(3705218420/1590121:ℝ), (7528416000/1590121:ℝ), (3855000000/1590121:ℝ)]]
theorem cell10_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_5_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_5_5_g]
def cell10_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(323518436200000000/583496491071:ℝ), (16558381749800000/14961448489:ℝ), (320881578500000000/583496491071:ℝ)],
  ![(16558381749800000/14961448489:ℝ), (8053106863517542800000/3648992556327677:ℝ), (3997991192909000000000/3648992556327677:ℝ)],
  ![(320881578500000000/583496491071:ℝ), (3997991192909000000000/3648992556327677:ℝ), (5949818997500000000000/10946977668983031:ℝ)]]
theorem cell10_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 5 5 b ν := by
 have heq : pairedCleared cell10 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_5_5_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_5_5_g]
theorem cell10_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_5_5 hb hν
def cell10_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(2254115253531549349/228742743759000000:ℝ)]]
theorem cell10_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 5 6) := by
 have heq : (-orderedLow cell10 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_5_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_5_6_g]
def cell10_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(97957423819113487603367/36372864044880483900:ℝ), (66468387787751115604089/12124288014960161300:ℝ), (1023206882812169908225/363728640448804839:ℝ)]]
theorem cell10_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 5 6 ν := by
 have heq : mixedLowHigh cell10 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_5_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_5_6_g]
def cell10_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(3845910104/1590121:ℝ), (7873747200/1590121:ℝ), (4066000000/1590121:ℝ)]]
theorem cell10_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 6 false ν := by
 have heq : naturalFloor cell10 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_5_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_5_6_g]
def cell10_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(1320816211654088/536422548987:ℝ), (300159052497600/59602505443:ℝ), (1393489402000000/536422548987:ℝ)]]
theorem cell10_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 5 6 true ν := by
 have heq : naturalFloor cell10 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_5_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_5_6_g]
def cell10_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(3845910104/1590121:ℝ), (7873747200/1590121:ℝ), (4066000000/1590121:ℝ)]]
theorem cell10_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_5_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_5_6_g]
def cell10_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(1492229302900000000/2528484794641:ℝ), (2990681803519440000/2528484794641:ℝ), (1491292758200000000/2528484794641:ℝ)],
  ![(8855734535248600000/7585454383923:ℝ), (110901848526761342040000/47436903232259801:ℝ), (165784251704871100000000/142310709696779403:ℝ)],
  ![(4361147270500000000/7585454383923:ℝ), (54577317694373700000000/47436903232259801:ℝ), (81536582664250000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 5 6 b ν := by
 have heq : pairedCleared cell10 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_5_6_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_5_6_g]
theorem cell10_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_5_6 hb hν
def cell10_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(468251573375242387/76247581253000000:ℝ)]]
theorem cell10_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 6 1) := by
 have heq : (-orderedLow cell10 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_6_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_6_1_g]
def cell10_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(23651510183279430362101/18186432022440241950:ℝ), (47193456966419329361801/18186432022440241950:ℝ), (472293850224593199350/363728640448804839:ℝ)]]
theorem cell10_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 6 1 ν := by
 have heq : mixedLowHigh cell10 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_6_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_6_1_g]
def cell10_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(5548615052/4770363:ℝ), (11112533600/4770363:ℝ), (1861000000/1590121:ℝ)]]
theorem cell10_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 1 false ν := by
 have heq : naturalFloor cell10 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_6_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_6_1_g]
def cell10_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(600526238182348/536422548987:ℝ), (401448938328800/178807516329:ℝ), (605966267000000/536422548987:ℝ)]]
theorem cell10_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 1 true ν := by
 have heq : naturalFloor cell10 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_6_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_6_1_g]
def cell10_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(3297295052/4770363:ℝ), (6761213600/4770363:ℝ), (1161000000/1590121:ℝ)]]
theorem cell10_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_6_1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_6_1_g]
def cell10_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(506698964100000000/2528484794641:ℝ), (3054333017609720000/7585454383923:ℝ), (1530656254100000000/7585454383923:ℝ)],
  ![(959762464719440000/2528484794641:ℝ), (36207796283060199480000/47436903232259801:ℝ), (18158422779146900000000/47436903232259801:ℝ)],
  ![(445903758200000000/2528484794641:ℝ), (50542188846190700000000/142310709696779403:ℝ), (25382739877250000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 6 1 b ν := by
 have heq : pairedCleared cell10 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_6_1_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_6_1_g]
theorem cell10_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_6_1 hb hν
def cell10_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(26037971472482717/4765473828312500:ℝ)]]
theorem cell10_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 6 2) := by
 have heq : (-orderedLow cell10 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_6_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_6_2_g]
def cell10_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(423446543497559011912/363728640448804839:ℝ), (877637467587489573200/363728640448804839:ℝ), (457100753213521000000/363728640448804839:ℝ)]]
theorem cell10_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 6 2 ν := by
 have heq : mixedLowHigh cell10 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_6_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_6_2_g]
def cell10_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(6594590104/4770363:ℝ), (13522427200/4770363:ℝ), (2322000000/1590121:ℝ)]]
theorem cell10_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 2 false ν := by
 have heq : naturalFloor cell10 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_6_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_6_2_g]
def cell10_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(729850074704696/536422548987:ℝ), (499320059437600/178807516329:ℝ), (772401484000000/536422548987:ℝ)]]
theorem cell10_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 2 true ν := by
 have heq : naturalFloor cell10 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_6_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_6_2_g]
def cell10_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(5281320104/4770363:ℝ), (10984157200/4770363:ℝ), (5741000000/4770363:ℝ)]]
theorem cell10_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_6_2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_6_2_g]
def cell10_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(517330822800000000/2528484794641:ℝ), (3232291219019440000/7585454383923:ℝ), (1673139008200000000/7585454383923:ℝ)],
  ![(1106411573419440000/2528484794641:ℝ), (42931289163499485120000/47436903232259801:ℝ), (22087361827953600000000/47436903232259801:ℝ)],
  ![(581921008200000000/2528484794641:ℝ), (67373993670860800000000/142310709696779403:ℝ), (34496438074000000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 6 2 b ν := by
 have heq : pairedCleared cell10 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_6_2_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_6_2_g]
theorem cell10_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_6_2 hb hν
def cell10_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(94188319775756651/15249516250600000:ℝ)]]
theorem cell10_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 6 3) := by
 have heq : (-orderedLow cell10 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_6_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_6_3_g]
def cell10_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(184268606766138067456/121242880149601613:ℝ), (385754738967479598100/121242880149601613:ℝ), (202941046763136750000/121242880149601613:ℝ)]]
theorem cell10_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 6 3 ν := by
 have heq : mixedLowHigh cell10 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_6_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_6_3_g]
def cell10_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2546855052/1590121:ℝ), (5310773600/1590121:ℝ), (2783000000/1590121:ℝ)]]
theorem cell10_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 3 false ν := by
 have heq : naturalFloor cell10 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_6_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_6_3_g]
def cell10_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2546855052/1590121:ℝ), (5310773600/1590121:ℝ), (2783000000/1590121:ℝ)]]
theorem cell10_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 3 true ν := by
 have heq : naturalFloor cell10 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_6_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_6_3_g]
def cell10_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(7265345156/4770363:ℝ), (5069033600/1590121:ℝ), (7999000000/4770363:ℝ)]]
theorem cell10_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_6_3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_6_3_g]
def cell10_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(763713407500000000/2528484794641:ℝ), (1592405532809720000/2528484794641:ℝ), (825112254100000000/2528484794641:ℝ)],
  ![(1582616408119440000/2528484794641:ℝ), (61604802224424770760000/47436903232259801:ℝ), (31783526081760300000000/47436903232259801:ℝ)],
  ![(811743258200000000/2528484794641:ℝ), (31470062603510300000000/47436903232259801:ℝ), (16178299590250000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 6 3 b ν := by
 have heq : pairedCleared cell10 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_6_3_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_6_3_g]
theorem cell10_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_6_3 hb hν
def cell10_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(262637827098921519/38123790626500000:ℝ)]]
theorem cell10_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 6 4) := by
 have heq : (-orderedLow cell10 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_6_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_6_4_g]
def cell10_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(682165097099269392824/363728640448804839:ℝ), (1436890966217388015400/363728640448804839:ℝ), (760545527365299500000/363728640448804839:ℝ)]]
theorem cell10_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 6 4 ν := by
 have heq : mixedLowHigh cell10 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_6_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_6_4_g]
def cell10_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(8686540208/4770363:ℝ), (18342214400/4770363:ℝ), (3244000000/1590121:ℝ)]]
theorem cell10_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 4 false ν := by
 have heq : naturalFloor cell10 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_6_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_6_4_g]
def cell10_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(988497747749392/536422548987:ℝ), (695062301655200/178807516329:ℝ), (1105271918000000/536422548987:ℝ)]]
theorem cell10_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 4 true ν := by
 have heq : naturalFloor cell10 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_6_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_6_4_g]
def cell10_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(8686540208/4770363:ℝ), (18342214400/4770363:ℝ), (3244000000/1590121:ℝ)]]
theorem cell10_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_6_4_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_6_4_g]
def cell10_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(1010095992200000000/2528484794641:ℝ), (6322141977838880000/7585454383923:ℝ), (3277534516400000000/7585454383923:ℝ)],
  ![(2058821242819440000/2528484794641:ℝ), (80278315285350056400000/47436903232259801:ℝ), (41479690335567000000000/47436903232259801:ℝ)],
  ![(1041565508200000000/2528484794641:ℝ), (121446381950201000000000/142310709696779403:ℝ), (62573359467500000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 6 4 b ν := by
 have heq : pairedCleared cell10 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_6_4_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_6_4_g]
theorem cell10_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_6_4 hb hν
def cell10_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(791565879786060217/76247581253000000:ℝ)]]
theorem cell10_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 6 5) := by
 have heq : (-orderedLow cell10 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_6_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_6_5_g]
def cell10_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(955243439803904283280/363728640448804839:ℝ), (1917422467375866936500/363728640448804839:ℝ), (969453600380938750000/363728640448804839:ℝ)]]
theorem cell10_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 6 5 ν := by
 have heq : mixedLowHigh cell10 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_6_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_6_5_g]
def cell10_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(11617415260/4770363:ℝ), (23387008000/4770363:ℝ), (3955000000/1590121:ℝ)]]
theorem cell10_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 5 false ν := by
 have heq : naturalFloor cell10 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_6_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_6_5_g]
def cell10_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(1329776704371740/536422548987:ℝ), (891697379464000/178807516329:ℝ), (1356043885000000/536422548987:ℝ)]]
theorem cell10_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 5 true ν := by
 have heq : naturalFloor cell10 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_6_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_6_5_g]
def cell10_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(11617415260/4770363:ℝ), (23387008000/4770363:ℝ), (3955000000/1590121:ℝ)]]
theorem cell10_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_6_5_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_6_5_g]
def cell10_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(1492229302900000000/2528484794641:ℝ), (8855734535248600000/7585454383923:ℝ), (4361147270500000000/7585454383923:ℝ)],
  ![(2990681803519440000/2528484794641:ℝ), (110901848526761342040000/47436903232259801:ℝ), (54577317694373700000000/47436903232259801:ℝ)],
  ![(1491292758200000000/2528484794641:ℝ), (165784251704871100000000/142310709696779403:ℝ), (81536582664250000000000/142310709696779403:ℝ)]]
theorem cell10_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 6 5 b ν := by
 have heq : pairedCleared cell10 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_6_5_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_6_5_g]
theorem cell10_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_6_5 hb hν
def cell10_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(8962233387321/762475812530:ℝ)]]
theorem cell10_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell10 6 6) := by
 have heq : (-orderedLow cell10 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell10_ordered_6_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_ordered_6_6_g]
def cell10_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(375552951412750981312/121242880149601613:ℝ), (759444911626326042600/121242880149601613:ℝ), (386801789337165500000/121242880149601613:ℝ)]]
theorem cell10_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell10 6 6 ν := by
 have heq : mixedLowHigh cell10 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_mixed_6_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_mixed_6_6_g]
def cell10_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(4596350104/1590121:ℝ), (9324187200/1590121:ℝ), (4766000000/1590121:ℝ)]]
theorem cell10_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 6 false ν := by
 have heq : naturalFloor cell10 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor0_6_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor0_6_6_g]
def cell10_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(528559960744696/178807516329:ℝ), (357039588117600/59602505443:ℝ), (546850184000000/178807516329:ℝ)]]
theorem cell10_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell10 6 6 true ν := by
 have heq : naturalFloor cell10 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_floor1_6_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_floor1_6_6_g]
def cell10_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(4596350104/1590121:ℝ), (9324187200/1590121:ℝ), (4766000000/1590121:ℝ)]]
theorem cell10_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell10_complement_floor_6_6_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_complement_floor_6_6_g]
def cell10_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(1738611887600000000/2528484794641:ℝ), (3466886638219440000/2528484794641:ℝ), (1721115008200000000/2528484794641:ℝ)],
  ![(3466886638219440000/2528484794641:ℝ), (129575361587686627680000/47436903232259801:ℝ), (64273481948180400000000/47436903232259801:ℝ)],
  ![(1721115008200000000/2528484794641:ℝ), (64273481948180400000000/47436903232259801:ℝ), (31858347787000000000000/47436903232259801:ℝ)]]
theorem cell10_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell10 6 6 b ν := by
 have heq : pairedCleared cell10 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell10_paired_cleared_6_6_g (6239/10000:ℝ) (3/4:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_cleared_6_6_g]
theorem cell10_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell10 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell10_paired_cleared_6_6 hb hν
def cell10_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(147702976640785651/228742743759000000:ℝ)]]
theorem cell10_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell10.q/K)+1+17/50*(cell10.q/cell10.priorL)+17/25*(cell10.q/cell10.priorL)*cell10.priorB) := by
 have heq : ((2-17/50-17/25)*(cell10.q/K)+1+17/50*(cell10.q/cell10.priorL)+17/25*(cell10.q/cell10.priorL)*cell10.priorB) = Record12518109.Bernstein.bsum 0 0 (147702976640785651/228742743759000000:ℝ) cell10_increment0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_increment0_g]
def cell10_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(1018031718101/2034191000000:ℝ)]]
theorem cell10_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell10.q/cell10.priorL)*(1-cell10.priorB)) := by
 have heq : (1+17/25*(cell10.q/cell10.priorL)*(1-cell10.priorB)) = Record12518109.Bernstein.bsum 0 0 (1018031718101/2034191000000:ℝ) cell10_increment1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_increment1_g]
def cell10_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(4071190654303/8136764000000:ℝ)]]
theorem cell10_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell10.q/cell10.priorL)*(1-cell10.priorB)) := by
 have heq : (1+omega*(cell10.q/cell10.priorL)*(1-cell10.priorB)) = Record12518109.Bernstein.bsum 0 0 (4071190654303/8136764000000:ℝ) cell10_increment2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_increment2_g]
def cell10_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(154798884/1590121:ℝ), (918876800/4770363:ℝ), (473561600/4770363:ℝ)]]
theorem cell10_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (287149/187500:ℝ) cell10_high_increment_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_high_increment_g]
def cell10_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(12658656051658/2005142581:ℝ), (133152488523826/2005142581:ℝ), (239933374845026/2005142581:ℝ), (112148843948342/2005142581:ℝ)]]
theorem cell10_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (6329328025829/500000000000:ℝ) cell10_three_gate0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_three_gate0_g]
def cell10_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(70345842/1590121:ℝ), (204639516/1590121:ℝ), (140654158/1590121:ℝ)]]
theorem cell10_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (35172921/50000000:ℝ) cell10_three_gate1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_three_gate1_g]
def cell10_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(49196349908248/536422548987:ℝ), (32556989269400/178807516329:ℝ), (50620308095900/536422548987:ℝ)]]
theorem cell10_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell10.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell10.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (162784946347/112449000000:ℝ) cell10_three_gate2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_three_gate2_g]
def cell10_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(643499/1349388:ℝ)]]
theorem cell10_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (1-cell10.q/K/3) := by
 have heq : (1-cell10.q/K/3) = Record12518109.Bernstein.bsum 0 0 (643499/1349388:ℝ) cell10_paired_margin0_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_margin0_g]
def cell10_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(94641337/1125660000:ℝ)]]
theorem cell10_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (gamma cell10-13/50) := by
 have heq : (gamma cell10-13/50) = Record12518109.Bernstein.bsum 0 0 (94641337/1125660000:ℝ) cell10_paired_margin1_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_margin1_g]
def cell10_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(44069/450264:ℝ)]]
theorem cell10_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (cell10.q-gamma cell10) := by
 have heq : (cell10.q-gamma cell10) = Record12518109.Bernstein.bsum 0 0 (44069/450264:ℝ) cell10_paired_margin2_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_margin2_g]
def cell10_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(2393677541/7879620000:ℝ)]]
theorem cell10_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (1/25:ℝ) (81/2000:ℝ)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4:ℝ)) : 0 < (min (cell10.q+rho cell10.q) (3/4+rho (3/4))-gamma cell10) := by
 have heq : (min (cell10.q+rho cell10.q) (3/4+rho (3/4))-gamma cell10) = Record12518109.Bernstein.bsum 0 0 (2393677541/7879620000:ℝ) cell10_paired_margin3_g (1/25:ℝ) (81/2000:ℝ) (6239/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell10, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell10_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell10_paired_margin3_g]
theorem cell10_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (6239/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6239/10000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell10 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell10_paired_1_1 hb hν
 · exact cell10_paired_1_2 hb hν
 · exact cell10_paired_1_3 hb hν
 · exact cell10_paired_1_4 hb hν
 · exact cell10_paired_1_5 hb hν
 · exact cell10_paired_1_6 hb hν
 · exact cell10_paired_2_1 hb hν
 · exact cell10_paired_2_2 hb hν
 · exact cell10_paired_2_3 hb hν
 · exact cell10_paired_2_4 hb hν
 · exact cell10_paired_2_5 hb hν
 · exact cell10_paired_2_6 hb hν
 · exact cell10_paired_3_1 hb hν
 · exact cell10_paired_3_2 hb hν
 · exact cell10_paired_3_3 hb hν
 · exact cell10_paired_3_4 hb hν
 · exact cell10_paired_3_5 hb hν
 · exact cell10_paired_3_6 hb hν
 · exact cell10_paired_4_1 hb hν
 · exact cell10_paired_4_2 hb hν
 · exact cell10_paired_4_3 hb hν
 · exact cell10_paired_4_4 hb hν
 · exact cell10_paired_4_5 hb hν
 · exact cell10_paired_4_6 hb hν
 · exact cell10_paired_5_1 hb hν
 · exact cell10_paired_5_2 hb hν
 · exact cell10_paired_5_3 hb hν
 · exact cell10_paired_5_4 hb hν
 · exact cell10_paired_5_5 hb hν
 · exact cell10_paired_5_6 hb hν
 · exact cell10_paired_6_1 hb hν
 · exact cell10_paired_6_2 hb hν
 · exact cell10_paired_6_3 hb hν
 · exact cell10_paired_6_4 hb hν
 · exact cell10_paired_6_5 hb hν
 · exact cell10_paired_6_6 hb hν
end
end Record12518109Admission
