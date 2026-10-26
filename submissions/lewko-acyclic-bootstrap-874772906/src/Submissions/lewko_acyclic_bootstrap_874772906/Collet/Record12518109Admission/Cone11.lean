/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell11
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell11_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(1332759048563/4574854875180:ℝ)]]
theorem cell11_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 1 1) := by
 have heq : (-orderedLow cell11 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_1_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_1_1_g]
def cell11_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(14814683742764130368/125510304777169517:ℝ), (102864288179041606900/376530914331508551:ℝ), (59926360608075250000/376530914331508551:ℝ)]]
theorem cell11_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 1 1 ν := by
 have heq : mixedLowHigh cell11 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_1_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_1_1_g]
def cell11_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(139577956/1646089:ℝ), (343993600/1646089:ℝ), (211000000/1646089:ℝ)]]
theorem cell11_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 1 false ν := by
 have heq : naturalFloor cell11 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_1_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_1_1_g]
def cell11_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(5880544474748/61700353987:ℝ), (127323779529200/555303185883:ℝ), (76620092000000/555303185883:ℝ)]]
theorem cell11_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 1 true ν := by
 have heq : naturalFloor cell11 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_1_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_1_1_g]
def cell11_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(139577956/1646089:ℝ), (343993600/1646089:ℝ), (211000000/1646089:ℝ)]]
theorem cell11_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_1_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_1_1_g]
def cell11_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(55982105400000000/2709608995921:ℝ), (378738071862440000/8128826987763:ℝ), (207081536900000000/8128826987763:ℝ)],
  ![(378738071862440000/8128826987763:ℝ), (15712546448585221040000/152683757311152429:ℝ), (8464091377435400000000/152683757311152429:ℝ)],
  ![(207081536900000000/8128826987763:ℝ), (8464091377435400000000/152683757311152429:ℝ), (4509550041500000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 1 1 b ν := by
 have heq : pairedCleared cell11 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_1_1_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_1_1_g]
theorem cell11_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_1_1 hb hν
def cell11_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(156400013228790547/228742743759000000:ℝ)]]
theorem cell11_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 1 2) := by
 have heq : (-orderedLow cell11 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_1_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_1_2_g]
def cell11_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(3785259592805284317901/12551030477716951700:ℝ), (25338284845201699830403/37653091433150855100:ℝ), (142837307982510537175/376530914331508551:ℝ)]]
theorem cell11_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 1 2 ν := by
 have heq : mixedLowHigh cell11 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_1_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_1_2_g]
def cell11_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(279155912/1646089:ℝ), (687987200/1646089:ℝ), (422000000/1646089:ℝ)]]
theorem cell11_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 2 false ν := by
 have heq : naturalFloor cell11 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_1_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_1_2_g]
def cell11_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(279155912/1646089:ℝ), (687987200/1646089:ℝ), (422000000/1646089:ℝ)]]
theorem cell11_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 2 true ν := by
 have heq : naturalFloor cell11 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_1_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_1_2_g]
def cell11_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(279155912/1646089:ℝ), (687987200/1646089:ℝ), (422000000/1646089:ℝ)]]
theorem cell11_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_1_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_1_2_g]
def cell11_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(147244319700000000/2709608995921:ℝ), (961927220424880000/8128826987763:ℝ), (512773823800000000/8128826987763:ℝ)],
  ![(281153321587480000/2709608995921:ℝ), (11514947958625410520000/50894585770384143:ℝ), (6144299874342700000000/50894585770384143:ℝ)],
  ![(132672262300000000/2709608995921:ℝ), (5447449009092700000000/50894585770384143:ℝ), (2912180020750000000000/50894585770384143:ℝ)]]
theorem cell11_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 1 2 b ν := by
 have heq : pairedCleared cell11 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_1_2_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_1_2_g]
theorem cell11_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_1_2 hb hν
def cell11_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(293847109631953/57185685939750000:ℝ)]]
theorem cell11_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 1 3) := by
 have heq : (-orderedLow cell11 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_1_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_1_3_g]
def cell11_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(28148477488031053299/3137757619429237925:ℝ), (1439022769919880627097/9413272858287713775:ℝ), (58701464470209601300/376530914331508551:ℝ)]]
theorem cell11_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 1 3 ν := by
 have heq : mixedLowHigh cell11 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_1_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_1_3_g]
def cell11_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(418733868/1646089:ℝ), (1031980800/1646089:ℝ), (633000000/1646089:ℝ)]]
theorem cell11_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 3 false ν := by
 have heq : naturalFloor cell11 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_1_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_1_3_g]
def cell11_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(15046657624244/61700353987:ℝ), (336857056387600/555303185883:ℝ), (208100776000000/555303185883:ℝ)]]
theorem cell11_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 3 true ν := by
 have heq : naturalFloor cell11 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_1_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_1_3_g]
def cell11_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(418733868/1646089:ℝ), (1031980800/1646089:ℝ), (633000000/1646089:ℝ)]]
theorem cell11_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_1_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_1_3_g]
def cell11_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (42336130680000/2111932187:ℝ), (39444300000000/2111932187:ℝ)],
  ![(242336130680000/6335796561:ℝ), (13400927317849760000/119005266805263:ℝ), (8534354897600000000/119005266805263:ℝ)],
  ![(239444300000000/6335796561:ℝ), (10910404397600000000/119005266805263:ℝ), (6261101000000000000/119005266805263:ℝ)]]
theorem cell11_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 1 3 b ν := by
 have heq : pairedCleared cell11 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_1_3_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_1_3_g]
theorem cell11_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_1_3 hb hν
def cell11_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(164135127242048359/228742743759000000:ℝ)]]
theorem cell11_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 1 4) := by
 have heq : (-orderedLow cell11 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_1_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_1_4_g]
def cell11_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(2416385128480995494297/12551030477716951700:ℝ), (20807947106977061648791/37653091433150855100:ℝ), (141612411844644888475/376530914331508551:ℝ)]]
theorem cell11_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 1 4 ν := by
 have heq : mixedLowHigh cell11 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_1_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_1_4_g]
def cell11_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(558311824/1646089:ℝ), (1375974400/1646089:ℝ), (844000000/1646089:ℝ)]]
theorem cell11_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 4 false ν := by
 have heq : naturalFloor cell11 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_1_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_1_4_g]
def cell11_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(19629714198992/61700353987:ℝ), (441623694816800/555303185883:ℝ), (273841118000000/555303185883:ℝ)]]
theorem cell11_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 4 true ν := by
 have heq : naturalFloor cell11 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_1_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_1_4_g]
def cell11_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(558311824/1646089:ℝ), (1375974400/1646089:ℝ), (844000000/1646089:ℝ)]]
theorem cell11_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_1_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_1_4_g]
def cell11_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(91262214300000000/2709608995921:ℝ), (746140915549760000/8128826987763:ℝ), (457513397600000000/8128826987763:ℝ)],
  ![(775639148562440000/8128826987763:ℝ), (36025687176092252600000/152683757311152429:ℝ), (20918385579213500000000/152683757311152429:ℝ)],
  ![(498142286900000000/8128826987763:ℝ), (21876304491963500000000/152683757311152429:ℝ), (12259982603750000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 1 4 b ν := by
 have heq : pairedCleared cell11 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_1_4_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_1_4_g]
theorem cell11_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_1_4 hb hν
def cell11_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(163547433022784453/114371371879500000:ℝ)]]
theorem cell11_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 1 5) := by
 have heq : (-orderedLow cell11 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_1_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_1_5_g]
def cell11_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(2360088173504933387699/6275515238858475850:ℝ), (17929901567137300394597/18826545716575427550:ℝ), (224523359219080175650/376530914331508551:ℝ)]]
theorem cell11_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 1 5 ν := by
 have heq : mixedLowHigh cell11 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_1_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_1_5_g]
def cell11_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(697889780/1646089:ℝ), (1719968000/1646089:ℝ), (1055000000/1646089:ℝ)]]
theorem cell11_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 5 false ν := by
 have heq : naturalFloor cell11 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_1_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_1_5_g]
def cell11_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(24212770773740/61700353987:ℝ), (182130111082000/185101061961:ℝ), (113193820000000/185101061961:ℝ)]]
theorem cell11_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 5 true ν := by
 have heq : naturalFloor cell11 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_1_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_1_5_g]
def cell11_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(697889780/1646089:ℝ), (1719968000/1646089:ℝ), (1055000000/1646089:ℝ)]]
theorem cell11_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_1_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_1_5_g]
def cell11_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(182524428600000000/2709608995921:ℝ), (1329330064112200000/8128826987763:ℝ), (763205684500000000/8128826987763:ℝ)],
  ![(413453680487480000/2709608995921:ℝ), (18285994867794421040000/50894585770384143:ℝ), (10295731274935400000000/50894585770384143:ℝ)],
  ![(229692512300000000/2709608995921:ℝ), (9918186713935400000000/50894585770384143:ℝ), (5495657541500000000000/50894585770384143:ℝ)]]
theorem cell11_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 1 5 b ν := by
 have heq : pairedCleared cell11 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_1_5_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_1_5_g]
theorem cell11_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_1_5 hb hν
def cell11_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(1126423332036656017/228742743759000000:ℝ)]]
theorem cell11_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 1 6) := by
 have heq : (-orderedLow cell11 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_1_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_1_6_g]
def cell11_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(11864926499291708056499/12551030477716951700:ℝ), (71153104556806049929597/37653091433150855100:ℝ), (364619992533265462825/376530914331508551:ℝ)]]
theorem cell11_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 1 6 ν := by
 have heq : mixedLowHigh cell11 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_1_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_1_6_g]
def cell11_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(1472367736/1646089:ℝ), (2948861600/1646089:ℝ), (1516000000/1646089:ℝ)]]
theorem cell11_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 6 false ν := by
 have heq : naturalFloor cell11 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_1_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_1_6_g]
def cell11_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(52593784048488/61700353987:ℝ), (949675331975200/555303185883:ℝ), (489658552000000/555303185883:ℝ)]]
theorem cell11_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 1 6 true ν := by
 have heq : naturalFloor cell11 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_1_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_1_6_g]
def cell11_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(1472367736/1646089:ℝ), (2948861600/1646089:ℝ), (1516000000/1646089:ℝ)]]
theorem cell11_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_1_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_1_6_g]
def cell11_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(512293176900000000/2709608995921:ℝ), (969927938224880000/2709608995921:ℝ), (450214323800000000/2709608995921:ℝ)],
  ![(3087247536362440000/8128826987763:ℝ), (109874033585040273640000/152683757311152429:ℝ), (51078555905398900000000/152683757311152429:ℝ)],
  ![(1546657786900000000/8128826987763:ℝ), (55084946326648900000000/152683757311152429:ℝ), (25644500145250000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 1 6 b ν := by
 have heq : pairedCleared cell11 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_1_6_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_1_6_g]
theorem cell11_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_1_6 hb hν
def cell11_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(276831442689839453/228742743759000000:ℝ)]]
theorem cell11_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 2 1) := by
 have heq : (-orderedLow cell11 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_2_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_2_1_g]
def cell11_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(89667294938008121104/376530914331508551:ℝ), (177201233004182336900/376530914331508551:ℝ), (89040061723500250000/376530914331508551:ℝ)]]
theorem cell11_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 2 1 ν := by
 have heq : mixedLowHigh cell11 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_2_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_2_1_g]
def cell11_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(924013868/4938267:ℝ), (1837260800/4938267:ℝ), (311000000/1646089:ℝ)]]
theorem cell11_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 1 false ν := by
 have heq : naturalFloor cell11 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_2_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_2_1_g]
def cell11_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(924013868/4938267:ℝ), (1837260800/4938267:ℝ), (311000000/1646089:ℝ)]]
theorem cell11_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 1 true ν := by
 have heq : naturalFloor cell11 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_2_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_2_1_g]
def cell11_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(924013868/4938267:ℝ), (1837260800/4938267:ℝ), (311000000/1646089:ℝ)]]
theorem cell11_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_2_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_2_1_g]
def cell11_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(147244319700000000/2709608995921:ℝ), (281153321587480000/2709608995921:ℝ), (132672262300000000/2709608995921:ℝ)],
  ![(961927220424880000/8128826987763:ℝ), (11514947958625410520000/50894585770384143:ℝ), (5447449009092700000000/50894585770384143:ℝ)],
  ![(512773823800000000/8128826987763:ℝ), (6144299874342700000000/50894585770384143:ℝ), (2912180020750000000000/50894585770384143:ℝ)]]
theorem cell11_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 2 1 b ν := by
 have heq : pairedCleared cell11 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_2_1_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_2_1_g]
theorem cell11_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_2_1 hb hν
def cell11_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(5907613923743/2287427437590:ℝ)]]
theorem cell11_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 2 2) := by
 have heq : (-orderedLow cell11 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_2_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_2_2_g]
def cell11_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(86915700232532220736/125510304777169517:ℝ), (537707495230395093800/376530914331508551:ℝ), (279972641847450500000/376530914331508551:ℝ)]]
theorem cell11_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 2 2 ν := by
 have heq : mixedLowHigh cell11 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_2_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_2_2_g]
def cell11_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1030475912/1646089:ℝ), (2139307200/1646089:ℝ), (1122000000/1646089:ℝ)]]
theorem cell11_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 2 false ν := by
 have heq : naturalFloor cell11 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_2_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_2_2_g]
def cell11_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(39922816509496/61700353987:ℝ), (744246007098400/555303185883:ℝ), (389383084000000/555303185883:ℝ)]]
theorem cell11_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 2 true ν := by
 have heq : naturalFloor cell11 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_2_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_2_2_g]
def cell11_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1030475912/1646089:ℝ), (2139307200/1646089:ℝ), (1122000000/1646089:ℝ)]]
theorem cell11_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_2_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_2_2_g]
def cell11_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(394205082000000000/2709608995921:ℝ), (2393084757324880000/8128826987763:ℝ), (1203049073800000000/8128826987763:ℝ)],
  ![(2393084757324880000/8128826987763:ℝ), (90769880224419242080000/152683757311152429:ℝ), (45551333492870800000000/152683757311152429:ℝ)],
  ![(1203049073800000000/8128826987763:ℝ), (45551333492870800000000/152683757311152429:ℝ), (22824605083000000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 2 2 b ν := by
 have heq : pairedCleared cell11 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_2_2_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_2_2_g]
theorem cell11_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_2_2 hb hν
def cell11_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(680523453174940547/228742743759000000:ℝ)]]
theorem cell11_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 2 3) := by
 have heq : (-orderedLow cell11 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_2_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_2_3_g]
def cell11_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(10995361241782093354701/12551030477716951700:ℝ), (68822605550337048520403/37653091433150855100:ℝ), (362883589221885787175/376530914331508551:ℝ)]]
theorem cell11_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 2 3 ν := by
 have heq : mixedLowHigh cell11 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_2_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_2_3_g]
def cell11_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(1170053868/1646089:ℝ), (2483300800/1646089:ℝ), (1333000000/1646089:ℝ)]]
theorem cell11_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 3 false ν := by
 have heq : naturalFloor cell11 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_2_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_2_3_g]
def cell11_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(44505873084244/61700353987:ℝ), (849012645527600/555303185883:ℝ), (455123426000000/555303185883:ℝ)]]
theorem cell11_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 3 true ν := by
 have heq : naturalFloor cell11 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_2_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_2_3_g]
def cell11_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(1170053868/1646089:ℝ), (2483300800/1646089:ℝ), (1333000000/1646089:ℝ)]]
theorem cell11_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_2_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_2_3_g]
def cell11_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(485467296300000000/2709608995921:ℝ), (992091301962440000/2709608995921:ℝ), (502913786900000000/2709608995921:ℝ)],
  ![(2857806650224880000/8128826987763:ℝ), (109602177651710252600000/152683757311152429:ℝ), (55520141738463500000000/152683757311152429:ℝ)],
  ![(1393984323800000000/8128826987763:ℝ), (53429589142713500000000/152683757311152429:ℝ), (27051595103750000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 2 3 b ν := by
 have heq : pairedCleared cell11 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_2_3_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_2_3_g]
theorem cell11_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_2_3 hb hν
def cell11_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(131324707096169453/57185685939750000:ℝ)]]
theorem cell11_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 2 4) := by
 have heq : (-orderedLow cell11 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_2_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_2_4_g]
def cell11_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1830673889732233312499/3137757619429237925:ℝ), (12310102946203717799597/9413272858287713775:ℝ), (278747745709584851300/376530914331508551:ℝ)]]
theorem cell11_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 2 4 ν := by
 have heq : mixedLowHigh cell11 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_2_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_2_4_g]
def cell11_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1309631824/1646089:ℝ), (2827294400/1646089:ℝ), (1544000000/1646089:ℝ)]]
theorem cell11_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 4 false ν := by
 have heq : naturalFloor cell11 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_2_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_2_4_g]
def cell11_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1309631824/1646089:ℝ), (2827294400/1646089:ℝ), (1544000000/1646089:ℝ)]]
theorem cell11_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 4 true ν := by
 have heq : naturalFloor cell11 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_2_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_2_4_g]
def cell11_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(1309631824/1646089:ℝ), (2827294400/1646089:ℝ), (1544000000/1646089:ℝ)]]
theorem cell11_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_2_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_2_4_g]
def cell11_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(338222976600000000/2709608995921:ℝ), (2177298452449760000/8128826987763:ℝ), (1147788647600000000/8128826987763:ℝ)],
  ![(775087980374960000/2709608995921:ℝ), (30750241174878421040000/50894585770384143:ℝ), (16012273149685400000000/50894585770384143:ℝ)],
  ![(434391524600000000/2709608995921:ℝ), (17028430319185400000000/50894585770384143:ℝ), (8782682541500000000000/50894585770384143:ℝ)]]
theorem cell11_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 2 4 b ν := by
 have heq : pairedCleared cell11 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_2_4_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_2_4_g]
theorem cell11_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_2_4 hb hν
def cell11_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(688258567188198359/228742743759000000:ℝ)]]
theorem cell11_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 2 5) := by
 have heq : (-orderedLow cell11 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_2_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_2_5_g]
def cell11_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(9626486777457804531097/12551030477716951700:ℝ), (64292267812112410338791/37653091433150855100:ℝ), (361658693084020138475/376530914331508551:ℝ)]]
theorem cell11_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 2 5 ν := by
 have heq : mixedLowHigh cell11 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_2_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_2_5_g]
def cell11_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1449209780/1646089:ℝ), (3171288000/1646089:ℝ), (1755000000/1646089:ℝ)]]
theorem cell11_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 5 false ν := by
 have heq : naturalFloor cell11 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_2_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_2_5_g]
def cell11_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(53671986233740/61700353987:ℝ), (1058545922386000/555303185883:ℝ), (586604110000000/555303185883:ℝ)]]
theorem cell11_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 5 true ν := by
 have heq : naturalFloor cell11 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_2_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_2_5_g]
def cell11_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1449209780/1646089:ℝ), (3171288000/1646089:ℝ), (1755000000/1646089:ℝ)]]
theorem cell11_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_2_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_2_5_g]
def cell11_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(429485190900000000/2709608995921:ℝ), (2760487601012200000/8128826987763:ℝ), (1453480934500000000/8128826987763:ℝ)],
  ![(2789985834024880000/8128826987763:ℝ), (111083020951926273640000/152683757311152429:ℝ), (58005627694648900000000/152683757311152429:ℝ)],
  ![(1494109823800000000/8128826987763:ℝ), (58963546607398900000000/152683757311152429:ℝ), (30575037645250000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 2 5 b ν := by
 have heq : pairedCleared cell11 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_2_5_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_2_5_g]
theorem cell11_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_2_5 hb hν
def cell11_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(425609152995859453/114371371879500000:ℝ)]]
theorem cell11_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 2 6) := by
 have heq : (-orderedLow cell11 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_2_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_2_6_g]
def cell11_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(5965138997993337906099/6275515238858475850:ℝ), (39672061919704974739597/18826545716575427550:ℝ), (444569640458455425650/376530914331508551:ℝ)]]
theorem cell11_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 2 6 ν := by
 have heq : mixedLowHigh cell11 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_2_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_2_6_g]
def cell11_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1588787736/1646089:ℝ), (3515281600/1646089:ℝ), (1966000000/1646089:ℝ)]]
theorem cell11_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 6 false ν := by
 have heq : naturalFloor cell11 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_2_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_2_6_g]
def cell11_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(58255042808488/61700353987:ℝ), (1163312560815200/555303185883:ℝ), (652344452000000/555303185883:ℝ)]]
theorem cell11_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 2 6 true ν := by
 have heq : naturalFloor cell11 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_2_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_2_6_g]
def cell11_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1588787736/1646089:ℝ), (3515281600/1646089:ℝ), (1966000000/1646089:ℝ)]]
theorem cell11_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_2_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_2_6_g]
def cell11_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(520747405200000000/2709608995921:ℝ), (1114558916524880000/2709608995921:ℝ), (586391073800000000/2709608995921:ℝ)],
  ![(3254707726924880000/8128826987763:ℝ), (129915318379217284160000/152683757311152429:ℝ), (67974435940241600000000/152683757311152429:ℝ)],
  ![(1685045073800000000/8128826987763:ℝ), (66841802257241600000000/152683757311152429:ℝ), (34802027666000000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 2 6 b ν := by
 have heq : pairedCleared cell11 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_2_6_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_2_6_g]
theorem cell11_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_2_6 hb hν
def cell11_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(271069440817057/38123790626500000:ℝ)]]
theorem cell11_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 3 1) := by
 have heq : (-orderedLow cell11 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_3_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_3_1_g]
def cell11_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(31767225204182661704/376530914331508551:ℝ), (43486186333566792500/125510304777169517:ℝ), (100197457453843750000/376530914331508551:ℝ)]]
theorem cell11_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 3 1 ν := by
 have heq : mixedLowHigh cell11 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_3_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_3_1_g]
def cell11_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(651573868/4938267:ℝ), (2164820800/4938267:ℝ), (511000000/1646089:ℝ)]]
theorem cell11_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 1 false ν := by
 have heq : naturalFloor cell11 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_3_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_3_1_g]
def cell11_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(22476711444244/185101061961:ℝ), (232153363589200/555303185883:ℝ), (166944442000000/555303185883:ℝ)]]
theorem cell11_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 1 true ν := by
 have heq : naturalFloor cell11 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_3_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_3_1_g]
def cell11_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(88083868/4938267:ℝ), (1076330800/4938267:ℝ), (336000000/1646089:ℝ)]]
theorem cell11_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_3_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_3_1_g]
def cell11_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (242336130680000/6335796561:ℝ), (239444300000000/6335796561:ℝ)],
  ![(42336130680000/2111932187:ℝ), (13400927317849760000/119005266805263:ℝ), (10910404397600000000/119005266805263:ℝ)],
  ![(39444300000000/2111932187:ℝ), (8534354897600000000/119005266805263:ℝ), (6261101000000000000/119005266805263:ℝ)]]
theorem cell11_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 3 1 b ν := by
 have heq : pairedCleared cell11 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_3_1_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_3_1_g]
theorem cell11_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_3_1 hb hν
def cell11_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(266984960878663151/76247581253000000:ℝ)]]
theorem cell11_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 3 2) := by
 have heq : (-orderedLow cell11 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_3_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_3_2_g]
def cell11_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(305970344407312392208/376530914331508551:ℝ), (204014813351845274600/125510304777169517:ℝ), (309086342962875500000/376530914331508551:ℝ)]]
theorem cell11_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 3 2 ν := by
 have heq : mixedLowHigh cell11 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_3_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_3_2_g]
def cell11_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(3596707736/4938267:ℝ), (7223201600/4938267:ℝ), (1222000000/1646089:ℝ)]]
theorem cell11_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 2 false ν := by
 have heq : naturalFloor cell11 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_3_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_3_2_g]
def cell11_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(136761627918488/185101061961:ℝ), (823520367268400/555303185883:ℝ), (417677909000000/555303185883:ℝ)]]
theorem cell11_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 2 true ν := by
 have heq : naturalFloor cell11 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_3_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_3_2_g]
def cell11_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(3596707736/4938267:ℝ), (7223201600/4938267:ℝ), (1222000000/1646089:ℝ)]]
theorem cell11_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_3_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_3_2_g]
def cell11_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(485467296300000000/2709608995921:ℝ), (2857806650224880000/8128826987763:ℝ), (1393984323800000000/8128826987763:ℝ)],
  ![(992091301962440000/2709608995921:ℝ), (109602177651710252600000/152683757311152429:ℝ), (53429589142713500000000/152683757311152429:ℝ)],
  ![(502913786900000000/2709608995921:ℝ), (55520141738463500000000/152683757311152429:ℝ), (27051595103750000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 3 2 b ν := by
 have heq : pairedCleared cell11 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_3_2_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_3_2_g]
theorem cell11_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_3_2 hb hν
def cell11_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(7432565548803/1524951625060:ℝ)]]
theorem cell11_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 3 3) := by
 have heq : (-orderedLow cell11 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_3_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_3_3_g]
def cell11_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(159016716722300311104/125510304777169517:ℝ), (324183567427249526900/125510304777169517:ℝ), (166672974362275250000/125510304777169517:ℝ)]]
theorem cell11_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 3 3 ν := by
 have heq : mixedLowHigh cell11 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_3_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_3_3_g]
def cell11_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1921373868/1646089:ℝ), (3934620800/1646089:ℝ), (2033000000/1646089:ℝ)]]
theorem cell11_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 3 false ν := by
 have heq : naturalFloor cell11 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_3_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_3_3_g]
def cell11_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(73965088544244/61700353987:ℝ), (453722744889200/185101061961:ℝ), (234048692000000/185101061961:ℝ)]]
theorem cell11_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 3 true ν := by
 have heq : naturalFloor cell11 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_3_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_3_3_g]
def cell11_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1921373868/1646089:ℝ), (3934620800/1646089:ℝ), (2033000000/1646089:ℝ)]]
theorem cell11_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_3_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_3_3_g]
def cell11_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(732428058600000000/2709608995921:ℝ), (1469143814262440000/2709608995921:ℝ), (733005536900000000/2709608995921:ℝ)],
  ![(1469143814262440000/2709608995921:ℝ), (55275738000084421040000/50894585770384143:ℝ), (27546191869435400000000/50894585770384143:ℝ)],
  ![(733005536900000000/2709608995921:ℝ), (27546191869435400000000/50894585770384143:ℝ), (13713220041500000000000/50894585770384143:ℝ)]]
theorem cell11_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 3 3 b ν := by
 have heq : pairedCleared cell11 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_3_3_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_3_3_g]
theorem cell11_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_3_3 hb hν
def cell11_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(401548964373696849/76247581253000000:ℝ)]]
theorem cell11_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 3 4) := by
 have heq : (-orderedLow cell11 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_3_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_3_4_g]
def cell11_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(18205462890758902391501/12551030477716951700:ℝ), (37435642085157465736801/12551030477716951700:ℝ), (194309956820420345725/125510304777169517:ℝ)]]
theorem cell11_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 3 4 ν := by
 have heq : mixedLowHigh cell11 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_3_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_3_4_g]
def cell11_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2060951824/1646089:ℝ), (4278614400/1646089:ℝ), (2244000000/1646089:ℝ)]]
theorem cell11_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 4 false ν := by
 have heq : naturalFloor cell11 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_3_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_3_4_g]
def cell11_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(78548145118992/61700353987:ℝ), (1465934873096800/555303185883:ℝ), (767886418000000/555303185883:ℝ)]]
theorem cell11_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 4 true ν := by
 have heq : naturalFloor cell11 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_3_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_3_4_g]
def cell11_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2060951824/1646089:ℝ), (4278614400/1646089:ℝ), (2244000000/1646089:ℝ)]]
theorem cell11_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_3_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_3_4_g]
def cell11_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(823690272900000000/2709608995921:ℝ), (4990620591349760000/8128826987763:ℝ), (2504708897600000000/8128826987763:ℝ)],
  ![(4872153335687320000/8128826987763:ℝ), (184659511427544273640000/152683757311152429:ℝ), (92607383853898900000000/152683757311152429:ℝ)],
  ![(2389951860700000000/8128826987763:ℝ), (90516831258148900000000/152683757311152429:ℝ), (45366650145250000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 3 4 b ν := by
 have heq : pairedCleared cell11 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_3_4_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_3_4_g]
theorem cell11_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_3_4 hb hν
def cell11_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(87451855694235651/19061895313250000:ℝ)]]
theorem cell11_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 3 5) := by
 have heq : (-orderedLow cell11 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_3_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_3_5_g]
def cell11_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(3633199301976435571699/3137757619429237925:ℝ), (7727061040829184990699/3137757619429237925:ℝ), (166264675649653367100/125510304777169517:ℝ)]]
theorem cell11_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 3 5 ν := by
 have heq : mixedLowHigh cell11 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_3_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_3_5_g]
def cell11_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(2200529780/1646089:ℝ), (4622608000/1646089:ℝ), (2455000000/1646089:ℝ)]]
theorem cell11_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 5 false ν := by
 have heq : naturalFloor cell11 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_3_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_3_5_g]
def cell11_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(83131201693740/61700353987:ℝ), (1570701511526000/555303185883:ℝ), (833626760000000/555303185883:ℝ)]]
theorem cell11_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 5 true ν := by
 have heq : naturalFloor cell11 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_3_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_3_5_g]
def cell11_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(2200529780/1646089:ℝ), (4622608000/1646089:ℝ), (2455000000/1646089:ℝ)]]
theorem cell11_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_3_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_3_5_g]
def cell11_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(676445953200000000/2709608995921:ℝ), (4191645137912200000/8128826987763:ℝ), (2143756184500000000/8128826987763:ℝ)],
  ![(4339610626587320000/8128826987763:ℝ), (167308057300469284160000/152683757311152429:ℝ), (85124061564491600000000/152683757311152429:ℝ)],
  ![(2299142110700000000/8128826987763:ℝ), (88172533072991600000000/152683757311152429:ℝ), (44663102666000000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 3 5 b ν := by
 have heq : pairedCleared cell11 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_3_5_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_3_5_g]
theorem cell11_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_3_5 hb hν
def cell11_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(404127335711449453/76247581253000000:ℝ)]]
theorem cell11_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 3 6) := by
 have heq : (-orderedLow cell11 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_3_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_3_6_g]
def cell11_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(16836588426434613567897/12551030477716951700:ℝ), (35925529505749253009597/12551030477716951700:ℝ), (193901658107798462825/125510304777169517:ℝ)]]
theorem cell11_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 3 6 ν := by
 have heq : mixedLowHigh cell11 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_3_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_3_6_g]
def cell11_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2340107736/1646089:ℝ), (4966601600/1646089:ℝ), (2666000000/1646089:ℝ)]]
theorem cell11_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 6 false ν := by
 have heq : naturalFloor cell11 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_3_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_3_6_g]
def cell11_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2340107736/1646089:ℝ), (4966601600/1646089:ℝ), (2666000000/1646089:ℝ)]]
theorem cell11_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 3 6 true ν := by
 have heq : naturalFloor cell11 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_3_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_3_6_g]
def cell11_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(2340107736/1646089:ℝ), (4966601600/1646089:ℝ), (2666000000/1646089:ℝ)]]
theorem cell11_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_3_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_3_6_g]
def cell11_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(767708167500000000/2709608995921:ℝ), (1591611428824880000/2709608995921:ℝ), (816482823800000000/2709608995921:ℝ)],
  ![(1601444173162440000/2709608995921:ℝ), (20682261636417810520000/16964861923461381:ℝ), (10565874423342700000000/16964861923461381:ℝ)],
  ![(830025786900000000/2709608995921:ℝ), (10672309858092700000000/16964861923461381:ℝ), (5432232520750000000000/16964861923461381:ℝ)]]
theorem cell11_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 3 6 b ν := by
 have heq : pairedCleared cell11 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_3_6_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_3_6_g]
theorem cell11_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_3_6 hb hν
def cell11_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(72558023557506359/45748548751800000:ℝ)]]
theorem cell11_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 4 1) := by
 have heq : (-orderedLow cell11 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_4_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_4_1_g]
def cell11_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(39698641160982100768/125510304777169517:ℝ), (286130338949557518100/376530914331508551:ℝ), (168540539123937250000/376530914331508551:ℝ)]]
theorem cell11_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 4 1 ν := by
 have heq : mixedLowHigh cell11 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_4_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_4_1_g]
def cell11_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(761277956/1646089:ℝ), (1715693600/1646089:ℝ), (961000000/1646089:ℝ)]]
theorem cell11_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 1 false ν := by
 have heq : naturalFloor cell11 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_4_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_4_1_g]
def cell11_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(27237493724748/61700353987:ℝ), (556226947779200/555303185883:ℝ), (313310717000000/555303185883:ℝ)]]
theorem cell11_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 1 true ν := by
 have heq : naturalFloor cell11 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_4_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_4_1_g]
def cell11_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(385617956/1646089:ℝ), (990033600/1646089:ℝ), (611000000/1646089:ℝ)]]
theorem cell11_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_4_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_4_1_g]
def cell11_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(91262214300000000/2709608995921:ℝ), (775639148562440000/8128826987763:ℝ), (498142286900000000/8128826987763:ℝ)],
  ![(746140915549760000/8128826987763:ℝ), (36025687176092252600000/152683757311152429:ℝ), (21876304491963500000000/152683757311152429:ℝ)],
  ![(457513397600000000/8128826987763:ℝ), (20918385579213500000000/152683757311152429:ℝ), (12259982603750000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 4 1 b ν := by
 have heq : pairedCleared cell11 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_4_1_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_4_1_g]
theorem cell11_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_4_1 hb hν
def cell11_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(262874928295526171/114371371879500000:ℝ)]]
theorem cell11_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 4 2) := by
 have heq : (-orderedLow cell11 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_4_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_4_2_g]
def cell11_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(248070274673486932808/376530914331508551:ℝ), (565301766052053864400/376530914331508551:ℝ), (320243738693219000000/376530914331508551:ℝ)]]
theorem cell11_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 4 2 ν := by
 have heq : mixedLowHigh cell11 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_4_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_4_2_g]
def cell11_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(3324267736/4938267:ℝ), (7550761600/4938267:ℝ), (1422000000/1646089:ℝ)]]
theorem cell11_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 2 false ν := by
 have heq : naturalFloor cell11 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_4_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_4_2_g]
def cell11_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(3324267736/4938267:ℝ), (7550761600/4938267:ℝ), (1422000000/1646089:ℝ)]]
theorem cell11_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 2 true ν := by
 have heq : naturalFloor cell11 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_4_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_4_2_g]
def cell11_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(3136437736/4938267:ℝ), (2395977200/1646089:ℝ), (4091000000/4938267:ℝ)]]
theorem cell11_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_4_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_4_2_g]
def cell11_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(338222976600000000/2709608995921:ℝ), (775087980374960000/2709608995921:ℝ), (434391524600000000/2709608995921:ℝ)],
  ![(2177298452449760000/8128826987763:ℝ), (30750241174878421040000/50894585770384143:ℝ), (17028430319185400000000/50894585770384143:ℝ)],
  ![(1147788647600000000/8128826987763:ℝ), (16012273149685400000000/50894585770384143:ℝ), (8782682541500000000000/50894585770384143:ℝ)]]
theorem cell11_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 4 2 b ν := by
 have heq : pairedCleared cell11 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_4_2_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_4_2_g]
theorem cell11_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_4_2 hb hν
def cell11_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(1325078322582139453/228742743759000000:ℝ)]]
theorem cell11_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 4 3) := by
 have heq : (-orderedLow cell11 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_4_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_4_3_g]
def cell11_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(522273393876616663312/376530914331508551:ℝ), (1046887647106889310700/376530914331508551:ℝ), (176377541400750250000/125510304777169517:ℝ)]]
theorem cell11_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 4 3 ν := by
 have heq : mixedLowHigh cell11 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_4_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_4_3_g]
def cell11_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(6269401604/4938267:ℝ), (12609142400/4938267:ℝ), (2133000000/1646089:ℝ)]]
theorem cell11_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 3 false ν := by
 have heq : naturalFloor cell11 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_4_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_4_3_g]
def cell11_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(238888444022732/185101061961:ℝ), (1440442594837600/555303185883:ℝ), (730440901000000/555303185883:ℝ)]]
theorem cell11_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 3 true ν := by
 have heq : naturalFloor cell11 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_4_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_4_3_g]
def cell11_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(6269401604/4938267:ℝ), (12609142400/4938267:ℝ), (2133000000/1646089:ℝ)]]
theorem cell11_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_4_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_4_3_g]
def cell11_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(823690272900000000/2709608995921:ℝ), (4872153335687320000/8128826987763:ℝ), (2389951860700000000/8128826987763:ℝ)],
  ![(4990620591349760000/8128826987763:ℝ), (184659511427544273640000/152683757311152429:ℝ), (90516831258148900000000/152683757311152429:ℝ)],
  ![(2504708897600000000/8128826987763:ℝ), (92607383853898900000000/152683757311152429:ℝ), (45366650145250000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 4 3 b ν := by
 have heq : pairedCleared cell11 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_4_3_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_4_3_g]
theorem cell11_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_4_3 hb hν
def cell11_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(8195041361333/1143713718795:ℝ)]]
theorem cell11_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 4 4) := by
 have heq : (-orderedLow cell11 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_4_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_4_4_g]
def cell11_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(231117733212068401472/125510304777169517:ℝ), (1407393909333102067600/376530914331508551:ℝ), (720065204326201000000/376530914331508551:ℝ)]]
theorem cell11_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 4 4 ν := by
 have heq : mixedLowHigh cell11 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_4_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_4_4_g]
def cell11_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(2812271824/1646089:ℝ), (5729934400/1646089:ℝ), (2944000000/1646089:ℝ)]]
theorem cell11_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 4 false ν := by
 have heq : naturalFloor cell11 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_4_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_4_4_g]
def cell11_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(108007360578992/61700353987:ℝ), (1978090462236800/555303185883:ℝ), (1014909068000000/555303185883:ℝ)]]
theorem cell11_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 4 true ν := by
 have heq : naturalFloor cell11 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_4_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_4_4_g]
def cell11_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(2812271824/1646089:ℝ), (5729934400/1646089:ℝ), (2944000000/1646089:ℝ)]]
theorem cell11_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_4_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_4_4_g]
def cell11_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(1070651035200000000/2709608995921:ℝ), (6421778128249760000/8128826987763:ℝ), (3194984147600000000/8128826987763:ℝ)],
  ![(6421778128249760000/8128826987763:ℝ), (240884547776087284160000/152683757311152429:ℝ), (119725817723741600000000/152683757311152429:ℝ)],
  ![(3194984147600000000/8128826987763:ℝ), (119725817723741600000000/152683757311152429:ℝ), (59454715166000000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 4 4 b ν := by
 have heq : pairedCleared cell11 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_4_4_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_4_4_g]
theorem cell11_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_4_4 hb hν
def cell11_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(1728770333067240547/228742743759000000:ℝ)]]
theorem cell11_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 4 5) := by
 have heq : (-orderedLow cell11 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_4_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_4_5_g]
def cell11_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(25415564539735711428301/12551030477716951700:ℝ), (155791246960607745900403/37653091433150855100:ℝ), (802976151700636287175/376530914331508551:ℝ)]]
theorem cell11_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 4 5 ν := by
 have heq : mixedLowHigh cell11 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_4_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_4_5_g]
def cell11_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(2951849780/1646089:ℝ), (6073928000/1646089:ℝ), (3155000000/1646089:ℝ)]]
theorem cell11_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 5 false ν := by
 have heq : naturalFloor cell11 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_4_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_4_5_g]
def cell11_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(112590417153740/61700353987:ℝ), (694285700222000/185101061961:ℝ), (360216470000000/185101061961:ℝ)]]
theorem cell11_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 5 true ν := by
 have heq : naturalFloor cell11 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_4_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_4_5_g]
def cell11_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(2951849780/1646089:ℝ), (6073928000/1646089:ℝ), (3155000000/1646089:ℝ)]]
theorem cell11_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_4_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_4_5_g]
def cell11_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(1161913249500000000/2709608995921:ℝ), (7004967276812200000/8128826987763:ℝ), (3500676434500000000/8128826987763:ℝ)],
  ![(2295500007049920000/2709608995921:ℝ), (9619142414939936840000/5654953974487127:ℝ), (4803504665530900000000/5654953974487127:ℝ)],
  ![(1128639799200000000/2709608995921:ℝ), (14178230374842700000000/16964861923461381:ℝ), (7075745020750000000000/16964861923461381:ℝ)]]
theorem cell11_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 4 5 b ν := by
 have heq : pairedCleared cell11 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_4_5_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_4_5_g]
theorem cell11_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_4_5 hb hν
def cell11_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(393386427069244453/57185685939750000:ℝ)]]
theorem cell11_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 4 6) := by
 have heq : (-orderedLow cell11 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_4_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_4_6_g]
def cell11_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(5435724714220637830899/3137757619429237925:ℝ), (34052263298771392144597/9413272858287713775:ℝ), (718840308188335351300/376530914331508551:ℝ)]]
theorem cell11_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 4 6 ν := by
 have heq : mixedLowHigh cell11 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_4_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_4_6_g]
def cell11_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3091427736/1646089:ℝ), (6417921600/1646089:ℝ), (3366000000/1646089:ℝ)]]
theorem cell11_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 6 false ν := by
 have heq : naturalFloor cell11 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_4_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_4_6_g]
def cell11_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(117173473728488/61700353987:ℝ), (2187623739095200/555303185883:ℝ), (1146389752000000/555303185883:ℝ)]]
theorem cell11_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 4 6 true ν := by
 have heq : naturalFloor cell11 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_4_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_4_6_g]
def cell11_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(3091427736/1646089:ℝ), (6417921600/1646089:ℝ), (3366000000/1646089:ℝ)]]
theorem cell11_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_4_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_4_6_g]
def cell11_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(1014668929800000000/2709608995921:ℝ), (2068663941124880000/2709608995921:ℝ), (1046574573800000000/2709608995921:ℝ)],
  ![(6353957312049760000/8128826987763:ℝ), (242365391076303305200000/152683757311152429:ℝ), (122211303679927000000000/152683757311152429:ℝ)],
  ![(3295109647600000000/8128826987763:ℝ), (125259775188427000000000/152683757311152429:ℝ), (62978157707500000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 4 6 b ν := by
 have heq : pairedCleared cell11 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_4_6_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_4_6_g]
theorem cell11_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_4_6 hb hν
def cell11_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(22623556841567539/7148210742468750:ℝ)]]
theorem cell11_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 5 1) := by
 have heq : (-orderedLow cell11 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_5_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_5_1_g]
def cell11_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(206424621761709942904/376530914331508551:ℝ), (441802118898414658700/376530914331508551:ℝ), (236883620794030750000/376530914331508551:ℝ)]]
theorem cell11_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 5 1 ν := by
 have heq : mixedLowHigh cell11 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_5_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_5_1_g]
def cell11_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(3916093868/4938267:ℝ), (8129340800/4938267:ℝ), (1411000000/1646089:ℝ)]]
theorem cell11_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 1 false ν := by
 have heq : naturalFloor cell11 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_5_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_5_1_g]
def cell11_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(140948250904244/185101061961:ℝ), (97811170218800/61700353987:ℝ), (153225664000000/185101061961:ℝ)]]
theorem cell11_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 1 true ν := by
 have heq : naturalFloor cell11 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_5_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_5_1_g]
def cell11_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(2225623868/4938267:ℝ), (4863870800/4938267:ℝ), (886000000/1646089:ℝ)]]
theorem cell11_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_5_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_5_1_g]
def cell11_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(182524428600000000/2709608995921:ℝ), (413453680487480000/2709608995921:ℝ), (229692512300000000/2709608995921:ℝ)],
  ![(1329330064112200000/8128826987763:ℝ), (18285994867794421040000/50894585770384143:ℝ), (9918186713935400000000/50894585770384143:ℝ)],
  ![(763205684500000000/8128826987763:ℝ), (10295731274935400000000/50894585770384143:ℝ), (5495657541500000000000/50894585770384143:ℝ)]]
theorem cell11_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 5 1 b ν := by
 have heq : pairedCleared cell11 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_5_1_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_5_1_g]
theorem cell11_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_5_1 hb hν
def cell11_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(177382711546736359/45748548751800000:ℝ)]]
theorem cell11_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 5 2) := by
 have heq : (-orderedLow cell11 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_5_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_5_2_g]
def cell11_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(111799657650750191136/125510304777169517:ℝ), (720973546000911005000/376530914331508551:ℝ), (388586820363312500000/376530914331508551:ℝ)]]
theorem cell11_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 5 2 ν := by
 have heq : mixedLowHigh cell11 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_5_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_5_2_g]
def cell11_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1652175912/1646089:ℝ), (3511007200/1646089:ℝ), (1872000000/1646089:ℝ)]]
theorem cell11_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 2 false ν := by
 have heq : naturalFloor cell11 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_5_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_5_2_g]
def cell11_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(61279765759496/61700353987:ℝ), (1173149175348400/555303185883:ℝ), (626073709000000/555303185883:ℝ)]]
theorem cell11_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 2 true ν := by
 have heq : naturalFloor cell11 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_5_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_5_2_g]
def cell11_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1401735912/1646089:ℝ), (9081701600/4938267:ℝ), (4916000000/4938267:ℝ)]]
theorem cell11_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_5_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_5_2_g]
def cell11_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(429485190900000000/2709608995921:ℝ), (2789985834024880000/8128826987763:ℝ), (1494109823800000000/8128826987763:ℝ)],
  ![(2760487601012200000/8128826987763:ℝ), (111083020951926273640000/152683757311152429:ℝ), (58963546607398900000000/152683757311152429:ℝ)],
  ![(1453480934500000000/8128826987763:ℝ), (58005627694648900000000/152683757311152429:ℝ), (30575037645250000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 5 2 b ν := by
 have heq : pairedCleared cell11 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_5_2_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_5_2_g]
theorem cell11_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_5_2 hb hν
def cell11_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(524936648268601171/114371371879500000:ℝ)]]
theorem cell11_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 5 3) := by
 have heq : (-orderedLow cell11 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_5_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_5_3_g]
def cell11_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(464373324142791203912/376530914331508551:ℝ), (1000144973103407351300/376530914331508551:ℝ), (180096673310864750000/125510304777169517:ℝ)]]
theorem cell11_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 5 3 ν := by
 have heq : mixedLowHigh cell11 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_5_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_5_3_g]
def cell11_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(5996961604/4938267:ℝ), (12936702400/4938267:ℝ), (2333000000/1646089:ℝ)]]
theorem cell11_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 3 false ν := by
 have heq : naturalFloor cell11 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_5_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_5_3_g]
def cell11_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(226730343652732/185101061961:ℝ), (1465997818727600/555303185883:ℝ), (792470426000000/555303185883:ℝ)]]
theorem cell11_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 3 true ν := by
 have heq : naturalFloor cell11 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_5_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_5_3_g]
def cell11_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(5996961604/4938267:ℝ), (12936702400/4938267:ℝ), (2333000000/1646089:ℝ)]]
theorem cell11_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_5_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_5_3_g]
def cell11_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(676445953200000000/2709608995921:ℝ), (4339610626587320000/8128826987763:ℝ), (2299142110700000000/8128826987763:ℝ)],
  ![(4191645137912200000/8128826987763:ℝ), (167308057300469284160000/152683757311152429:ℝ), (88172533072991600000000/152683757311152429:ℝ)],
  ![(2143756184500000000/8128826987763:ℝ), (85124061564491600000000/152683757311152429:ℝ), (44663102666000000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 5 3 b ν := by
 have heq : pairedCleared cell11 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_5_3_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_5_3_g]
theorem cell11_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_5_3 hb hν
def cell11_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(1849201762528289453/228742743759000000:ℝ)]]
theorem cell11_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 5 4) := by
 have heq : (-orderedLow cell11 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_5_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_5_4_g]
def cell11_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(738576443345920934416/376530914331508551:ℝ), (1481730854158242797600/376530914331508551:ℝ), (749178905441626000000/376530914331508551:ℝ)]]
theorem cell11_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 5 4 ν := by
 have heq : mixedLowHigh cell11 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_5_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_5_4_g]
def cell11_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(8942095472/4938267:ℝ), (17995083200/4938267:ℝ), (3044000000/1646089:ℝ)]]
theorem cell11_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 4 false ν := by
 have heq : naturalFloor cell11 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_5_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_5_4_g]
def cell11_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(341015260126976/185101061961:ℝ), (685788274135600/185101061961:ℝ), (347734631000000/185101061961:ℝ)]]
theorem cell11_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 4 true ν := by
 have heq : naturalFloor cell11 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_5_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_5_4_g]
def cell11_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(8942095472/4938267:ℝ), (17995083200/4938267:ℝ), (3044000000/1646089:ℝ)]]
theorem cell11_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_5_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_5_4_g]
def cell11_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(1161913249500000000/2709608995921:ℝ), (2295500007049920000/2709608995921:ℝ), (1128639799200000000/2709608995921:ℝ)],
  ![(7004967276812200000/8128826987763:ℝ), (9619142414939936840000/5654953974487127:ℝ), (14178230374842700000000/16964861923461381:ℝ)],
  ![(3500676434500000000/8128826987763:ℝ), (4803504665530900000000/5654953974487127:ℝ), (7075745020750000000000/16964861923461381:ℝ)]]
theorem cell11_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 5 4 b ν := by
 have heq : pairedCleared cell11 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_5_4_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_5_4_g]
theorem cell11_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_5_4 hb hν
def cell11_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(8652526848851/914970975036:ℝ)]]
theorem cell11_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 5 5) := by
 have heq : (-orderedLow cell11 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_5_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_5_5_g]
def cell11_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(303218749701836491840/125510304777169517:ℝ), (1842237116384455554500/376530914331508551:ℝ), (940111485565576250000/376530914331508551:ℝ)]]
theorem cell11_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 5 5 ν := by
 have heq : mixedLowHigh cell11 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_5_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_5_5_g]
def cell11_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(3703169780/1646089:ℝ), (7525248000/1646089:ℝ), (3855000000/1646089:ℝ)]]
theorem cell11_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 5 false ν := by
 have heq : naturalFloor cell11 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_5_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_5_5_g]
def cell11_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(142049632613740/61700353987:ℝ), (2595012689806000/555303185883:ℝ), (1327672060000000/555303185883:ℝ)]]
theorem cell11_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 5 true ν := by
 have heq : naturalFloor cell11 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_5_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_5_5_g]
def cell11_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(3703169780/1646089:ℝ), (7525248000/1646089:ℝ), (3855000000/1646089:ℝ)]]
theorem cell11_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_5_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_5_5_g]
def cell11_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(1408874011800000000/2709608995921:ℝ), (8436124813712200000/8128826987763:ℝ), (4190951684500000000/8128826987763:ℝ)],
  ![(8436124813712200000/8128826987763:ℝ), (315941881551921305200000/152683757311152429:ℝ), (156813059839177000000000/152683757311152429:ℝ)],
  ![(4190951684500000000/8128826987763:ℝ), (156813059839177000000000/152683757311152429:ℝ), (77769770207500000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 5 5 b ν := by
 have heq : pairedCleared cell11 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_5_5_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_5_5_g]
theorem cell11_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_5_5 hb hν
def cell11_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(2252893773013390547/228742743759000000:ℝ)]]
theorem cell11_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 5 6) := by
 have heq : (-orderedLow cell11 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_5_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_5_6_g]
def cell11_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(32625666188712520465101/12551030477716951700:ℝ), (199275567665743094590403/37653091433150855100:ℝ), (1023022432940011537175/376530914331508551:ℝ)]]
theorem cell11_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 5 6 ν := by
 have heq : mixedLowHigh cell11 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_5_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_5_6_g]
def cell11_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(3842747736/1646089:ℝ), (7869241600/1646089:ℝ), (4066000000/1646089:ℝ)]]
theorem cell11_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 6 false ν := by
 have heq : naturalFloor cell11 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_5_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_5_6_g]
def cell11_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(146632689188488/61700353987:ℝ), (2699779328235200/555303185883:ℝ), (1393412402000000/555303185883:ℝ)]]
theorem cell11_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 5 6 true ν := by
 have heq : naturalFloor cell11 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_5_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_5_6_g]
def cell11_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(3842747736/1646089:ℝ), (7869241600/1646089:ℝ), (4066000000/1646089:ℝ)]]
theorem cell11_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_5_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_5_6_g]
def cell11_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(1500136226100000000/2709608995921:ℝ), (3006437987424880000/2709608995921:ℝ), (1498881323800000000/2709608995921:ℝ)],
  ![(8900846706612200000/8128826987763:ℝ), (334774178979212315720000/152683757311152429:ℝ), (166781868084769700000000/152683757311152429:ℝ)],
  ![(4381886934500000000/8128826987763:ℝ), (164691315489019700000000/152683757311152429:ℝ), (81996760228250000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 5 6 b ν := by
 have heq : pairedCleared cell11 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_5_6_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_5_6_g]
theorem cell11_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_5_6 hb hν
def cell11_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(467767294555524661/76247581253000000:ℝ)]]
theorem cell11_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 6 1) := by
 have heq : (-orderedLow cell11 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_6_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_6_1_g]
def cell11_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(23652351354096726253909/18826545716575427550:ℝ), (15730239946257816065403/6275515238858475850:ℝ), (472273493350860473050/376530914331508551:ℝ)]]
theorem cell11_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 6 1 ν := by
 have heq : mixedLowHigh cell11 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_6_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_6_1_g]
def cell11_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(5548353868/4938267:ℝ), (11111600800/4938267:ℝ), (1861000000/1646089:ℝ)]]
theorem cell11_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 1 false ν := by
 have heq : naturalFloor cell11 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_6_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_6_1_g]
def cell11_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(200184020634244/185101061961:ℝ), (1204374116159200/555303185883:ℝ), (606043267000000/555303185883:ℝ)]]
theorem cell11_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 1 true ν := by
 have heq : naturalFloor cell11 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_6_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_6_1_g]
def cell11_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(3294393868/4938267:ℝ), (6757640800/4938267:ℝ), (1161000000/1646089:ℝ)]]
theorem cell11_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_6_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_6_1_g]
def cell11_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(512293176900000000/2709608995921:ℝ), (3087247536362440000/8128826987763:ℝ), (1546657786900000000/8128826987763:ℝ)],
  ![(969927938224880000/2709608995921:ℝ), (109874033585040273640000/152683757311152429:ℝ), (55084946326648900000000/152683757311152429:ℝ)],
  ![(450214323800000000/2709608995921:ℝ), (51078555905398900000000/152683757311152429:ℝ), (25644500145250000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 6 1 b ν := by
 have heq : pairedCleared cell11 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_6_1_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_6_1_g]
theorem cell11_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_6_1 hb hν
def cell11_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(26001609559923151/4765473828312500:ℝ)]]
theorem cell11_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 6 2) := by
 have heq : (-orderedLow cell11 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_6_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_6_2_g]
def cell11_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(422727671231014214008/376530914331508551:ℝ), (292215108649922715200/125510304777169517:ℝ), (456929902033406000000/376530914331508551:ℝ)]]
theorem cell11_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 6 2 ν := by
 have heq : mixedLowHigh cell11 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_6_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_6_2_g]
def cell11_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(6588787736/4938267:ℝ), (13515281600/4938267:ℝ), (2322000000/1646089:ℝ)]]
theorem cell11_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 2 false ν := by
 have heq : naturalFloor cell11 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_6_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_6_2_g]
def cell11_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(243075067008488/185101061961:ℝ), (1497222759538400/555303185883:ℝ), (772439984000000/555303185883:ℝ)]]
theorem cell11_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 2 true ν := by
 have heq : naturalFloor cell11 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_6_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_6_2_g]
def cell11_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(5273977736/4938267:ℝ), (10975471600/4938267:ℝ), (5741000000/4938267:ℝ)]]
theorem cell11_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_6_2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_6_2_g]
def cell11_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(520747405200000000/2709608995921:ℝ), (3254707726924880000/8128826987763:ℝ), (1685045073800000000/8128826987763:ℝ)],
  ![(1114558916524880000/2709608995921:ℝ), (129915318379217284160000/152683757311152429:ℝ), (66841802257241600000000/152683757311152429:ℝ)],
  ![(586391073800000000/2709608995921:ℝ), (67974435940241600000000/152683757311152429:ℝ), (34802027666000000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 6 2 b ν := by
 have heq : pairedCleared cell11 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_6_2_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_6_2_g]
theorem cell11_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_6_2 hb hν
def cell11_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(94069133178655453/15249516250600000:ℝ)]]
theorem cell11_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 6 3) := by
 have heq : (-orderedLow cell11 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_6_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_6_3_g]
def cell11_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(183900674140518281504/125510304777169517:ℝ), (385272251017421497300/125510304777169517:ℝ), (202877700534229250000/125510304777169517:ℝ)]]
theorem cell11_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 6 3 ν := by
 have heq : mixedLowHigh cell11 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_6_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_6_3_g]
def cell11_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2543073868/1646089:ℝ), (5306320800/1646089:ℝ), (2783000000/1646089:ℝ)]]
theorem cell11_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 3 false ν := by
 have heq : naturalFloor cell11 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_6_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_6_3_g]
def cell11_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2543073868/1646089:ℝ), (5306320800/1646089:ℝ), (2783000000/1646089:ℝ)]]
theorem cell11_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 3 true ν := by
 have heq : naturalFloor cell11 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_6_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_6_3_g]
def cell11_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2417853868/1646089:ℝ), (15193302400/4938267:ℝ), (7999000000/4938267:ℝ)]]
theorem cell11_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_6_3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_6_3_g]
def cell11_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(767708167500000000/2709608995921:ℝ), (1601444173162440000/2709608995921:ℝ), (830025786900000000/2709608995921:ℝ)],
  ![(1591611428824880000/2709608995921:ℝ), (20682261636417810520000/16964861923461381:ℝ), (10672309858092700000000/16964861923461381:ℝ)],
  ![(816482823800000000/2709608995921:ℝ), (10565874423342700000000/16964861923461381:ℝ), (5432232520750000000000/16964861923461381:ℝ)]]
theorem cell11_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 6 3 b ν := by
 have heq : pairedCleared cell11 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_6_3_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_6_3_g]
theorem cell11_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_6_3 hb hν
def cell11_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(262332789413892057/38123790626500000:ℝ)]]
theorem cell11_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 6 4) := by
 have heq : (-orderedLow cell11 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_6_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_6_4_g]
def cell11_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(680676373612095475016/376530914331508551:ℝ), (478329393384920279400/125510304777169517:ℝ), (760336301171969500000/376530914331508551:ℝ)]]
theorem cell11_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 6 4 ν := by
 have heq : mixedLowHigh cell11 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_6_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_6_4_g]
def cell11_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(8669655472/4938267:ℝ), (18322643200/4938267:ℝ), (3244000000/1646089:ℝ)]]
theorem cell11_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 4 false ν := by
 have heq : naturalFloor cell11 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_6_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_6_4_g]
def cell11_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(328857159756976/185101061961:ℝ), (2082920046296800/555303185883:ℝ), (1105233418000000/555303185883:ℝ)]]
theorem cell11_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 4 true ν := by
 have heq : naturalFloor cell11 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_6_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_6_4_g]
def cell11_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(8669655472/4938267:ℝ), (18322643200/4938267:ℝ), (3244000000/1646089:ℝ)]]
theorem cell11_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_6_4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_6_4_g]
def cell11_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(1014668929800000000/2709608995921:ℝ), (6353957312049760000/8128826987763:ℝ), (3295109647600000000/8128826987763:ℝ)],
  ![(2068663941124880000/2709608995921:ℝ), (242365391076303305200000/152683757311152429:ℝ), (125259775188427000000000/152683757311152429:ℝ)],
  ![(1046574573800000000/2709608995921:ℝ), (122211303679927000000000/152683757311152429:ℝ), (62978157707500000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 6 4 b ν := by
 have heq : pairedCleared cell11 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_6_4_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_6_4_g]
theorem cell11_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_6_4 hb hν
def cell11_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(791108400824813151/76247581253000000:ℝ)]]
theorem cell11_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 6 5) := by
 have heq : (-orderedLow cell11 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_6_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_6_5_g]
def cell11_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(954879492815225205520/376530914331508551:ℝ), (638858020403198761500/125510304777169517:ℝ), (969225186681001250000/376530914331508551:ℝ)]]
theorem cell11_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 6 5 ν := by
 have heq : mixedLowHigh cell11 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_6_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_6_5_g]
def cell11_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(11614789340/4938267:ℝ), (23381024000/4938267:ℝ), (3955000000/1646089:ℝ)]]
theorem cell11_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 5 false ν := by
 have heq : naturalFloor cell11 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_6_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_6_5_g]
def cell11_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(443142076231220/185101061961:ℝ), (2674287049976000/555303185883:ℝ), (1355966885000000/555303185883:ℝ)]]
theorem cell11_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 5 true ν := by
 have heq : naturalFloor cell11 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_6_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_6_5_g]
def cell11_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(11614789340/4938267:ℝ), (23381024000/4938267:ℝ), (3955000000/1646089:ℝ)]]
theorem cell11_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_6_5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_6_5_g]
def cell11_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(1500136226100000000/2709608995921:ℝ), (8900846706612200000/8128826987763:ℝ), (4381886934500000000/8128826987763:ℝ)],
  ![(3006437987424880000/2709608995921:ℝ), (334774178979212315720000/152683757311152429:ℝ), (164691315489019700000000/152683757311152429:ℝ)],
  ![(1498881323800000000/2709608995921:ℝ), (166781868084769700000000/152683757311152429:ℝ), (81996760228250000000000/152683757311152429:ℝ)]]
theorem cell11_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 6 5 b ν := by
 have heq : pairedCleared cell11 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_6_5_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_6_5_g]
theorem cell11_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_6_5 hb hν
def cell11_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(8957517173863/762475812530:ℝ)]]
theorem cell11_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell11 6 6) := by
 have heq : (-orderedLow cell11 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell11_ordered_6_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordered_6_6_g]
def cell11_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(375319766191604582208/125510304777169517:ℝ), (759026774478603013800/125510304777169517:ℝ), (386719255601650500000/125510304777169517:ℝ)]]
theorem cell11_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell11 6 6 ν := by
 have heq : mixedLowHigh cell11 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_mixed_6_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_mixed_6_6_g]
def cell11_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(4594067736/1646089:ℝ), (9320561600/1646089:ℝ), (4766000000/1646089:ℝ)]]
theorem cell11_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 6 false ν := by
 have heq : naturalFloor cell11 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor0_6_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor0_6_6_g]
def cell11_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(176091904648488/61700353987:ℝ), (1070644972458400/185101061961:ℝ), (546811684000000/185101061961:ℝ)]]
theorem cell11_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell11 6 6 true ν := by
 have heq : naturalFloor cell11 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_floor1_6_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_floor1_6_6_g]
def cell11_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(4594067736/1646089:ℝ), (9320561600/1646089:ℝ), (4766000000/1646089:ℝ)]]
theorem cell11_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell11_complement_floor_6_6_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement_floor_6_6_g]
def cell11_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(1747096988400000000/2709608995921:ℝ), (3483490499724880000/2709608995921:ℝ), (1728973073800000000/2709608995921:ℝ)],
  ![(3483490499724880000/2709608995921:ℝ), (130333071775918442080000/50894585770384143:ℝ), (64633433984870800000000/50894585770384143:ℝ)],
  ![(1728973073800000000/2709608995921:ℝ), (64633433984870800000000/50894585770384143:ℝ), (32028275083000000000000/50894585770384143:ℝ)]]
theorem cell11_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell11 6 6 b ν := by
 have heq : pairedCleared cell11 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell11_paired_cleared_6_6_g (6217/10000:ℝ) (3/4:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_cleared_6_6_g]
theorem cell11_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) : 0 ≤ pairedGap cell11 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell11_paired_cleared_6_6 hb hν
def cell11_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(147585442531994453/228742743759000000:ℝ)]]
theorem cell11_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell11.q/K)+1+17/50*(cell11.q/cell11.priorL)+17/25*(cell11.q/cell11.priorL)*cell11.priorB) := by
 have heq : ((2-17/50-17/25)*(cell11.q/K)+1+17/50*(cell11.q/cell11.priorL)+17/25*(cell11.q/cell11.priorL)*cell11.priorB) = Record12518109.Bernstein.bsum 0 0 (147585442531994453/228742743759000000:ℝ) cell11_increment0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_increment0_g]
def cell11_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(1018028416803/2034191000000:ℝ)]]
theorem cell11_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell11.q/cell11.priorL)*(1-cell11.priorB)) := by
 have heq : (1+17/25*(cell11.q/cell11.priorL)*(1-cell11.priorB)) = Record12518109.Bernstein.bsum 0 0 (1018028416803/2034191000000:ℝ) cell11_increment1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_increment1_g]
def cell11_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(4071180750409/8136764000000:ℝ)]]
theorem cell11_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell11.q/cell11.priorL)*(1-cell11.priorB)) := by
 have heq : (1+omega*(cell11.q/cell11.priorL)*(1-cell11.priorB)) = Record12518109.Bernstein.bsum 0 0 (4071180750409/8136764000000:ℝ) cell11_increment2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_increment2_g]
def cell11_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(154899556/1646089:ℝ), (918630400/4938267:ℝ), (473684800/4938267:ℝ)]]
theorem cell11_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (71768/46875:ℝ) cell11_high_increment_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_high_increment_g]
def cell11_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(11830194270566/2111932187:ℝ), (131908849297502/2111932187:ℝ), (240734946188302/2111932187:ℝ), (112977305729434/2111932187:ℝ)]]
theorem cell11_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (5915097135283/500000000000:ℝ) cell11_three_gate0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_three_gate0_g]
def cell11_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(69788978/1646089:ℝ), (204415644/1646089:ℝ), (141211022/1646089:ℝ)]]
theorem cell11_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (34894489/50000000:ℝ) cell11_three_gate1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_three_gate1_g]
def cell11_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(49235847605432/555303185883:ℝ), (97659784574600/555303185883:ℝ), (16881716570900/185101061961:ℝ)]]
theorem cell11_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell11.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell11.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (488298922873/337347000000:ℝ) cell11_three_gate2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_three_gate2_g]
def cell11_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(643609/1349388:ℝ)]]
theorem cell11_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (1-cell11.q/K/3) := by
 have heq : (1-cell11.q/K/3) = Record12518109.Bernstein.bsum 0 0 (643609/1349388:ℝ) cell11_paired_margin0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_margin0_g]
def cell11_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(92046833/1126980000:ℝ)]]
theorem cell11_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (gamma cell11-13/50) := by
 have heq : (gamma cell11-13/50) = Record12518109.Bernstein.bsum 0 0 (92046833/1126980000:ℝ) cell11_paired_margin1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_margin1_g]
def cell11_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(44707/450792:ℝ)]]
theorem cell11_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (cell11.q-gamma cell11) := by
 have heq : (cell11.q-gamma cell11) = Record12518109.Bernstein.bsum 0 0 (44707/450792:ℝ) cell11_paired_margin2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_margin2_g]
def cell11_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(2415422869/7888860000:ℝ)]]
theorem cell11_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < (min (cell11.q+rho cell11.q) (3/4+rho (3/4))-gamma cell11) := by
 have heq : (min (cell11.q+rho cell11.q) (3/4+rho (3/4))-gamma cell11) = Record12518109.Bernstein.bsum 0 0 (2415422869/7888860000:ℝ) cell11_paired_margin3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_paired_margin3_g]
theorem cell11_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (6217/10000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell11 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell11_paired_1_1 hb hν
 · exact cell11_paired_1_2 hb hν
 · exact cell11_paired_1_3 hb hν
 · exact cell11_paired_1_4 hb hν
 · exact cell11_paired_1_5 hb hν
 · exact cell11_paired_1_6 hb hν
 · exact cell11_paired_2_1 hb hν
 · exact cell11_paired_2_2 hb hν
 · exact cell11_paired_2_3 hb hν
 · exact cell11_paired_2_4 hb hν
 · exact cell11_paired_2_5 hb hν
 · exact cell11_paired_2_6 hb hν
 · exact cell11_paired_3_1 hb hν
 · exact cell11_paired_3_2 hb hν
 · exact cell11_paired_3_3 hb hν
 · exact cell11_paired_3_4 hb hν
 · exact cell11_paired_3_5 hb hν
 · exact cell11_paired_3_6 hb hν
 · exact cell11_paired_4_1 hb hν
 · exact cell11_paired_4_2 hb hν
 · exact cell11_paired_4_3 hb hν
 · exact cell11_paired_4_4 hb hν
 · exact cell11_paired_4_5 hb hν
 · exact cell11_paired_4_6 hb hν
 · exact cell11_paired_5_1 hb hν
 · exact cell11_paired_5_2 hb hν
 · exact cell11_paired_5_3 hb hν
 · exact cell11_paired_5_4 hb hν
 · exact cell11_paired_5_5 hb hν
 · exact cell11_paired_5_6 hb hν
 · exact cell11_paired_6_1 hb hν
 · exact cell11_paired_6_2 hb hν
 · exact cell11_paired_6_3 hb hν
 · exact cell11_paired_6_4 hb hν
 · exact cell11_paired_6_5 hb hν
 · exact cell11_paired_6_6 hb hν
end
end Record12518109Admission
