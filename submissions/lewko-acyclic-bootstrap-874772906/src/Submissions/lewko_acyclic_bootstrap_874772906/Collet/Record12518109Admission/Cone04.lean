/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell04
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell4_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(272468513869/914970975036:ℝ)]]
theorem cell4_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 1 1) := by
 have heq : (-orderedLow cell4 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_1_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_1_1_g]
def cell4_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(616540700118503872/3998499408488573:ℝ), (4209048764050358740/11995498225465719:ℝ), (2407408656596710000/11995498225465719:ℝ)]]
theorem cell4_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 1 1 ν := by
 have heq : mixedLowHigh cell4 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_1_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_1_1_g]
def cell4_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(5865124/52441:ℝ), (14095360/52441:ℝ), (8440000/52441:ℝ)]]
theorem cell4_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 1 false ν := by
 have heq : naturalFloor cell4 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_1_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_1_1_g]
def cell4_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(738519978676/5896938009:ℝ), (5214430359920/17690814027:ℝ), (3069633680000/17690814027:ℝ)]]
theorem cell4_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 1 true ν := by
 have heq : naturalFloor cell4 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_1_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_1_1_g]
def cell4_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(5865124/52441:ℝ), (14095360/52441:ℝ), (8440000/52441:ℝ)]]
theorem cell4_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_1_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_1_1_g]
def cell4_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(80954104000000/2750058481:ℝ), (547234615736000/8250175443:ℝ), (299679044000000/8250175443:ℝ)],
  ![(547234615736000/8250175443:ℝ), (4508430328863088000/30764904226947:ℝ), (2433864872152000000/30764904226947:ℝ)],
  ![(299679044000000/8250175443:ℝ), (2433864872152000000/30764904226947:ℝ), (1299935308000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 1 1 b ν := by
 have heq : pairedCleared cell4 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_1_1_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_1_1_g]
theorem cell4_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_1_1 hb hν
def cell4_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(31629064646350061/45748548751800000:ℝ)]]
theorem cell4_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 1 2) := by
 have heq : (-orderedLow cell4 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_1_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_1_2_g]
def cell4_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(155396654762412751869/399849940848857300:ℝ), (1028429119701583320907/1199549822546571900:ℝ), (5718355539947176405/11995498225465719:ℝ)]]
theorem cell4_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 1 2 ν := by
 have heq : mixedLowHigh cell4 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_1_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_1_2_g]
def cell4_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(11730248/52441:ℝ), (28190720/52441:ℝ), (16880000/52441:ℝ)]]
theorem cell4_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 2 false ν := by
 have heq : naturalFloor cell4 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_1_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_1_2_g]
def cell4_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(11730248/52441:ℝ), (28190720/52441:ℝ), (16880000/52441:ℝ)]]
theorem cell4_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 2 true ν := by
 have heq : naturalFloor cell4 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_1_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_1_2_g]
def cell4_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(11730248/52441:ℝ), (28190720/52441:ℝ), (16880000/52441:ℝ)]]
theorem cell4_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_1_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_1_2_g]
def cell4_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(217529972000000/2750058481:ℝ), (1417952523472000/8250175443:ℝ), (755976088000000/8250175443:ℝ)],
  ![(416642739912000/2750058481:ℝ), (1126741520431848000/3418322691883:ℝ), (601315133692000000/3418322691883:ℝ)],
  ![(197548348000000/2750058481:ℝ), (1606400383076000000/10254968075649:ℝ), (858791654000000000/10254968075649:ℝ)]]
theorem cell4_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 1 2 b ν := by
 have heq : pairedCleared cell4 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_1_2_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_1_2_g]
theorem cell4_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_1_2 hb hν
def cell4_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(237784643509439/11437137187950000:ℝ)]]
theorem cell4_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 1 3) := by
 have heq : (-orderedLow cell4 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_1_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_1_3_g]
def cell4_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(3251849319852574931/99962485212214325:ℝ), (65666319931664618593/299887455636642975:ℝ), (2380376857589864380/11995498225465719:ℝ)]]
theorem cell4_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 1 3 ν := by
 have heq : mixedLowHigh cell4 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_1_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_1_3_g]
def cell4_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(17595372/52441:ℝ), (42286080/52441:ℝ), (25320000/52441:ℝ)]]
theorem cell4_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 3 false ν := by
 have heq : naturalFloor cell4 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_1_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_1_3_g]
def cell4_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(1899589336028/5896938009:ℝ), (13805679279760/17690814027:ℝ), (8319201040000/17690814027:ℝ)]]
theorem cell4_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 3 true ν := by
 have heq : naturalFloor cell4 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_1_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_1_3_g]
def cell4_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(17595372/52441:ℝ), (42286080/52441:ℝ), (25320000/52441:ℝ)]]
theorem cell4_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_1_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_1_3_g]
def cell4_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (333730584000/12008989:ℝ), (313236000000/12008989:ℝ)],
  ![(1933730584000/36026967:ℝ), (21216553566944000/134344559943:ℝ), (13561206176000000/134344559943:ℝ)],
  ![(1913236000000/36026967:ℝ), (17334954176000000/134344559943:ℝ), (9985304000000000/134344559943:ℝ)]]
theorem cell4_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 1 3 b ν := by
 have heq : pairedCleared cell4 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_1_3_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_1_3_g]
theorem cell4_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_1_3 hb hν
def cell4_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(33596313127513817/45748548751800000:ℝ)]]
theorem cell4_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 1 4) := by
 have heq : (-orderedLow cell4 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_1_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_1_4_g]
def cell4_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(106749982029972664393/399849940848857300:ℝ), (870189523023205921279/1199549822546571900:ℝ), (5691323740940330785/11995498225465719:ℝ)]]
theorem cell4_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 1 4 ν := by
 have heq : mixedLowHigh cell4 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_1_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_1_4_g]
def cell4_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(23460496/52441:ℝ), (56381440/52441:ℝ), (33760000/52441:ℝ)]]
theorem cell4_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 4 false ν := by
 have heq : naturalFloor cell4 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_1_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_1_4_g]
def cell4_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(2480124014704/5896938009:ℝ), (18101303739680/17690814027:ℝ), (10943984720000/17690814027:ℝ)]]
theorem cell4_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 4 true ν := by
 have heq : naturalFloor cell4 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_1_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_1_4_g]
def cell4_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(23460496/52441:ℝ), (56381440/52441:ℝ), (33760000/52441:ℝ)]]
theorem cell4_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_1_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_1_4_g]
def cell4_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(136575868000000/2750058481:ℝ), (1099990818944000/8250175443:ℝ), (671490176000000/8250175443:ℝ)],
  ![(1145517907736000/8250175443:ℝ), (10490834121853720000/30764904226947:ℝ), (6083487545380000000/30764904226947:ℝ)],
  ![(731097044000000/8250175443:ℝ), (6355040783380000000/30764904226947:ℝ), (3563074270000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 1 4 b ν := by
 have heq : pairedCleared cell4 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_1_4_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_1_4_g]
theorem cell4_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_1_4 hb hν
def cell4_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(33120743840494939/22874274375900000:ℝ)]]
theorem cell4_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 1 5) := by
 have heq : (-orderedLow cell4 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_1_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_1_5_g]
def cell4_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(100246283390267514531/199924970424428650:ℝ), (738856883159876684093/599774911273285950:ℝ), (9002270624290797190/11995498225465719:ℝ)]]
theorem cell4_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 1 5 ν := by
 have heq : mixedLowHigh cell4 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_1_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_1_5_g]
def cell4_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(29325620/52441:ℝ), (70476800/52441:ℝ), (42200000/52441:ℝ)]]
theorem cell4_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 5 false ν := by
 have heq : naturalFloor cell4 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_1_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_1_5_g]
def cell4_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(1020219564460/1965646003:ℝ), (7465642733200/5896938009:ℝ), (4522922800000/5896938009:ℝ)]]
theorem cell4_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 5 true ν := by
 have heq : naturalFloor cell4 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_1_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_1_5_g]
def cell4_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(29325620/52441:ℝ), (70476800/52441:ℝ), (42200000/52441:ℝ)]]
theorem cell4_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_1_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_1_5_g]
def cell4_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(273151736000000/2750058481:ℝ), (1970708726680000/8250175443:ℝ), (1127787220000000/8250175443:ℝ)],
  ![(616070503912000/2750058481:ℝ), (5374359158959088000/10254968075649:ℝ), (3020486292152000000/10254968075649:ℝ)],
  ![(341354348000000/2750058481:ℝ), (2913459020152000000/10254968075649:ℝ), (1613171308000000000/10254968075649:ℝ)]]
theorem cell4_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 1 5 b ν := by
 have heq : pairedCleared cell4 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_1_5_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_1_5_g]
theorem cell4_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_1_5 hb hν
def cell4_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(225532863486042671/45748548751800000:ℝ)]]
theorem cell4_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 1 6) := by
 have heq : (-orderedLow cell4 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_1_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_1_6_g]
def cell4_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(475246909425719393731/399849940848857300:ℝ), (2857016027059166815093/1199549822546571900:ℝ), (14600644945231263595/11995498225465719:ℝ)]]
theorem cell4_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 1 6 ν := by
 have heq : mixedLowHigh cell4 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_1_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_1_6_g]
def cell4_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(58930744/52441:ℝ), (118312160/52441:ℝ), (60640000/52441:ℝ)]]
theorem cell4_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 6 false ν := by
 have heq : naturalFloor cell4 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_1_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_1_6_g]
def cell4_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(6310732632056/5896938009:ℝ), (38074640439520/17690814027:ℝ), (19567022080000/17690814027:ℝ)]]
theorem cell4_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 1 6 true ν := by
 have heq : naturalFloor cell4 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_1_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_1_6_g]
def cell4_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(58930744/52441:ℝ), (118312160/52441:ℝ), (60640000/52441:ℝ)]]
theorem cell4_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_1_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_1_6_g]
def cell4_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(763833444000000/2750058481:ℝ), (1450408051472000/2750058481:ℝ), (677188088000000/2750058481:ℝ)],
  ![(4610302635736000/8250175443:ℝ), (32669647103980808000/30764904226947:ℝ), (15274263127532000000/30764904226947:ℝ)],
  ![(2314109044000000/8250175443:ℝ), (16410004657532000000/30764904226947:ℝ), (7682133578000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 1 6 b ν := by
 have heq : pairedCleared cell4 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_1_6_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_1_6_g]
theorem cell4_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_1_6 hb hν
def cell4_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(55904732160835939/45748548751800000:ℝ)]]
theorem cell4_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 2 1) := by
 have heq : (-orderedLow cell4 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_2_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_2_1_g]
def cell4_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(3595144272508905616/11995498225465719:ℝ), (7124658893254752740/11995498225465719:ℝ), (3577496613647710000/11995498225465719:ℝ)]]
theorem cell4_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 2 1 ν := by
 have heq : mixedLowHigh cell4 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_2_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_2_1_g]
def cell4_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(36923372/157323:ℝ), (73614080/157323:ℝ), (12440000/52441:ℝ)]]
theorem cell4_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 1 false ν := by
 have heq : naturalFloor cell4 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_2_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_2_1_g]
def cell4_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(36923372/157323:ℝ), (73614080/157323:ℝ), (12440000/52441:ℝ)]]
theorem cell4_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 1 true ν := by
 have heq : naturalFloor cell4 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_2_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_2_1_g]
def cell4_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(36923372/157323:ℝ), (73614080/157323:ℝ), (12440000/52441:ℝ)]]
theorem cell4_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_2_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_2_1_g]
def cell4_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(217529972000000/2750058481:ℝ), (416642739912000/2750058481:ℝ), (197548348000000/2750058481:ℝ)],
  ![(1417952523472000/8250175443:ℝ), (1126741520431848000/3418322691883:ℝ), (1606400383076000000/10254968075649:ℝ)],
  ![(755976088000000/8250175443:ℝ), (601315133692000000/3418322691883:ℝ), (858791654000000000/10254968075649:ℝ)]]
theorem cell4_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 2 1 b ν := by
 have heq : pairedCleared cell4 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_2_1_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_2_1_g]
theorem cell4_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_2_1 hb hν
def cell4_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(1187439488905/457485487518:ℝ)]]
theorem cell4_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 2 2) := by
 have heq : (-orderedLow cell4 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_2_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_2_2_g]
def cell4_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(3507699244176503744/3998499408488573:ℝ), (21646747885171205480/11995498225465719:ℝ), (11219614138445420000/11995498225465719:ℝ)]]
theorem cell4_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 2 2 ν := by
 have heq : mixedLowHigh cell4 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_2_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_2_2_g]
def cell4_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(41562248/52441:ℝ), (86022720/52441:ℝ), (44880000/52441:ℝ)]]
theorem cell4_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 2 false ν := by
 have heq : naturalFloor cell4 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_2_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_2_2_g]
def cell4_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(4831618525352/5896938009:ℝ), (29938312423840/17690814027:ℝ), (15584983360000/17690814027:ℝ)]]
theorem cell4_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 2 true ν := by
 have heq : naturalFloor cell4 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_2_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_2_2_g]
def cell4_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(41562248/52441:ℝ), (86022720/52441:ℝ), (44880000/52441:ℝ)]]
theorem cell4_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_2_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_2_2_g]
def cell4_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(606882320000000/2750058481:ℝ), (3682335567472000/8250175443:ℝ), (1852302088000000/8250175443:ℝ)],
  ![(3682335567472000/8250175443:ℝ), (27724546400670176000/30764904226947:ℝ), (13925261920304000000/30764904226947:ℝ)],
  ![(1852302088000000/8250175443:ℝ), (13925261920304000000/30764904226947:ℝ), (6985174616000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 2 2 b ν := by
 have heq : pairedCleared cell4 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_2_2_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_2_2_g]
theorem cell4_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_2_2 hb hν
def cell4_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(136749587843400061/45748548751800000:ℝ)]]
theorem cell4_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 2 3) := by
 have heq : (-orderedLow cell4 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_2_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_2_3_g]
def cell4_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(444512509168212739069/399849940848857300:ℝ), (2772199031813667994907/1199549822546571900:ℝ), (14530561021795886405/11995498225465719:ℝ)]]
theorem cell4_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 2 3 ν := by
 have heq : mixedLowHigh cell4 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_2_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_2_3_g]
def cell4_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(47427372/52441:ℝ), (100118080/52441:ℝ), (53320000/52441:ℝ)]]
theorem cell4_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 3 false ν := by
 have heq : naturalFloor cell4 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_2_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_2_3_g]
def cell4_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(5412153204028/5896938009:ℝ), (34233936883760/17690814027:ℝ), (18209767040000/17690814027:ℝ)]]
theorem cell4_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 3 true ν := by
 have heq : naturalFloor cell4 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_2_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_2_3_g]
def cell4_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(47427372/52441:ℝ), (100118080/52441:ℝ), (53320000/52441:ℝ)]]
theorem cell4_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_2_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_2_3_g]
def cell4_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(743458188000000/2750058481:ℝ), (1517684491736000/2750058481:ℝ), (769533044000000/2750058481:ℝ)],
  ![(4385029171472000/8250175443:ℝ), (33356789755693720000/30764904226947:ℝ), (16903233251380000000/30764904226947:ℝ)],
  ![(2145268088000000/8250175443:ℝ), (16310598197380000000/30764904226947:ℝ), (8261614270000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 2 3 b ν := by
 have heq : pairedCleared cell4 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_2_3_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_2_3_g]
theorem cell4_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_2_3 hb hν
def cell4_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(26517915442771939/11437137187950000:ℝ)]]
theorem cell4_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 2 4) := by
 have heq : (-orderedLow cell4 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_2_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_2_4_g]
def cell4_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(75530812921302571731/99962485212214325:ℝ), (501608797959685787093/299887455636642975:ℝ), (11192582339438574380/11995498225465719:ℝ)]]
theorem cell4_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 2 4 ν := by
 have heq : mixedLowHigh cell4 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_2_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_2_4_g]
def cell4_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(53292496/52441:ℝ), (114213440/52441:ℝ), (61760000/52441:ℝ)]]
theorem cell4_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 4 false ν := by
 have heq : naturalFloor cell4 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_2_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_2_4_g]
def cell4_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(53292496/52441:ℝ), (114213440/52441:ℝ), (61760000/52441:ℝ)]]
theorem cell4_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 4 true ν := by
 have heq : naturalFloor cell4 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_2_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_2_4_g]
def cell4_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(53292496/52441:ℝ), (114213440/52441:ℝ), (61760000/52441:ℝ)]]
theorem cell4_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_2_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_2_4_g]
def cell4_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(525928216000000/2750058481:ℝ), (3364373862944000/8250175443:ℝ), (1767816176000000/8250175443:ℝ)],
  ![(1192641751824000/2750058481:ℝ), (3119411870959696000/3418322691883:ℝ), (1621879251384000000/3418322691883:ℝ)],
  ![(663584696000000/2750058481:ℝ), (5153700518152000000/10254968075649:ℝ), (2657291308000000000/10254968075649:ℝ)]]
theorem cell4_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 2 4 b ν := by
 have heq : pairedCleared cell4 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_2_4_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_2_4_g]
theorem cell4_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_2_4 hb hν
def cell4_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(138716836324563817/45748548751800000:ℝ)]]
theorem cell4_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 2 5) := by
 have heq : (-orderedLow cell4 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_2_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_2_5_g]
def cell4_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(395865836435772651593/399849940848857300:ℝ), (2613959435135290595279/1199549822546571900:ℝ), (14503529222789040785/11995498225465719:ℝ)]]
theorem cell4_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 2 5 ν := by
 have heq : mixedLowHigh cell4 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_2_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_2_5_g]
def cell4_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(59157620/52441:ℝ), (128308800/52441:ℝ), (70200000/52441:ℝ)]]
theorem cell4_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 5 false ν := by
 have heq : naturalFloor cell4 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_2_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_2_5_g]
def cell4_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(6573222561380/5896938009:ℝ), (42825185803600/17690814027:ℝ), (23459334400000/17690814027:ℝ)]]
theorem cell4_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 5 true ν := by
 have heq : naturalFloor cell4 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_2_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_2_5_g]
def cell4_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(59157620/52441:ℝ), (128308800/52441:ℝ), (70200000/52441:ℝ)]]
theorem cell4_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_2_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_2_5_g]
def cell4_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(662504084000000/2750058481:ℝ), (4235091770680000/8250175443:ℝ), (2224113220000000/8250175443:ℝ)],
  ![(4280618859472000/8250175443:ℝ), (33706950193660808000/30764904226947:ℝ), (17574884593532000000/30764904226947:ℝ)],
  ![(2283720088000000/8250175443:ℝ), (17846437831532000000/30764904226947:ℝ), (9248313578000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 2 5 b ν := by
 have heq : pairedCleared cell4 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_2_5_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_2_5_g]
theorem cell4_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_2_5 hb hν
def cell4_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(85681005439019939/22874274375900000:ℝ)]]
theorem cell4_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 2 6) := by
 have heq : (-orderedLow cell4 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_2_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_2_6_g]
def cell4_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(244804210593167508131/199924970424428650:ℝ), (1610741839215919021093/599774911273285950:ℝ), (17814476106139507190/11995498225465719:ℝ)]]
theorem cell4_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 2 6 ν := by
 have heq : mixedLowHigh cell4 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_2_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_2_6_g]
def cell4_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(65022744/52441:ℝ), (142404160/52441:ℝ), (78640000/52441:ℝ)]]
theorem cell4_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 6 false ν := by
 have heq : naturalFloor cell4 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_2_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_2_6_g]
def cell4_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(7153757240056/5896938009:ℝ), (47120810263520/17690814027:ℝ), (26084118080000/17690814027:ℝ)]]
theorem cell4_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 2 6 true ν := by
 have heq : naturalFloor cell4 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_2_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_2_6_g]
def cell4_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(65022744/52441:ℝ), (142404160/52441:ℝ), (78640000/52441:ℝ)]]
theorem cell4_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_2_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_2_6_g]
def cell4_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(799079952000000/2750058481:ℝ), (1701936559472000/2750058481:ℝ), (893470088000000/2750058481:ℝ)],
  ![(4983312463472000/8250175443:ℝ), (39339193548684352000/30764904226947:ℝ), (20552855924608000000/30764904226947:ℝ)],
  ![(2576686088000000/8250175443:ℝ), (20231774108608000000/30764904226947:ℝ), (10524753232000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 2 6 b ν := by
 have heq : pairedCleared cell4 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_2_6_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_2_6_g]
theorem cell4_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_2_6 hb hν
def cell4_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(288979925472191/7624758125300000:ℝ)]]
theorem cell4_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 3 1) := by
 have heq : (-orderedLow cell4 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_3_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_3_1_g]
def cell4_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(6908986127157944/52382088320811:ℝ), (8098265189974900/17460696106937:ℝ), (17595337796050000/52382088320811:ℝ)]]
theorem cell4_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 3 1 ν := by
 have heq : mixedLowHigh cell4 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_3_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_3_1_g]
def cell4_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(29779372/157323:ℝ), (90470080/157323:ℝ), (20440000/52441:ℝ)]]
theorem cell4_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 1 false ν := by
 have heq : naturalFloor cell4 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_3_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_3_1_g]
def cell4_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(345742516892/1965646003:ℝ), (9713867075920/17690814027:ℝ), (6672947680000/17690814027:ℝ)]]
theorem cell4_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 1 true ν := by
 have heq : naturalFloor cell4 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_3_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_3_1_g]
def cell4_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(7405372/157323:ℝ), (47096080/157323:ℝ), (13440000/52441:ℝ)]]
theorem cell4_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_3_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_3_1_g]
def cell4_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (1933730584000/36026967:ℝ), (1913236000000/36026967:ℝ)],
  ![(333730584000/12008989:ℝ), (21216553566944000/134344559943:ℝ), (17334954176000000/134344559943:ℝ)],
  ![(313236000000/12008989:ℝ), (13561206176000000/134344559943:ℝ), (9985304000000000/134344559943:ℝ)]]
theorem cell4_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 3 1 b ν := by
 have heq : pairedCleared cell4 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_3_1_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_3_1_g]
theorem cell4_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_3_1 hb hν
def cell4_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(53675085119295313/15249516250600000:ℝ)]]
theorem cell4_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 3 2) := by
 have heq : (-orderedLow cell4 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_3_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_3_2_g]
def cell4_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(12268619904682905232/11995498225465719:ℝ), (8187452671458533160/3998499408488573:ℝ), (12389702095496420000/11995498225465719:ℝ)]]
theorem cell4_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 3 2 ν := by
 have heq : mixedLowHigh cell4 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_3_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_3_2_g]
def cell4_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(144014744/157323:ℝ), (289396160/157323:ℝ), (48880000/52441:ℝ)]]
theorem cell4_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 2 false ν := by
 have heq : naturalFloor cell4 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_3_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_3_2_g]
def cell4_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(1825699099784/1965646003:ℝ), (33001711745840/17690814027:ℝ), (16711946360000/17690814027:ℝ)]]
theorem cell4_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 2 true ν := by
 have heq : naturalFloor cell4 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_3_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_3_2_g]
def cell4_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(144014744/157323:ℝ), (289396160/157323:ℝ), (48880000/52441:ℝ)]]
theorem cell4_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_3_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_3_2_g]
def cell4_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(743458188000000/2750058481:ℝ), (4385029171472000/8250175443:ℝ), (2145268088000000/8250175443:ℝ)],
  ![(1517684491736000/2750058481:ℝ), (33356789755693720000/30764904226947:ℝ), (16310598197380000000/30764904226947:ℝ)],
  ![(769533044000000/2750058481:ℝ), (16903233251380000000/30764904226947:ℝ), (8261614270000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 3 2 b ν := by
 have heq : pairedCleared cell4 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_3_2_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_3_2_g]
theorem cell4_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_3_2 hb hν
def cell4_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(1492429813917/304990325012:ℝ)]]
theorem cell4_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 3 3) := by
 have heq : (-orderedLow cell4 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_3_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_3_3_g]
def cell4_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(6398857788234503616/3998499408488573:ℝ), (13028149002097350740/3998499408488573:ℝ), (6677273206764710000/3998499408488573:ℝ)]]
theorem cell4_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 3 3 ν := by
 have heq : mixedLowHigh cell4 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_3_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_3_3_g]
def cell4_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(77259372/52441:ℝ), (157950080/52441:ℝ), (81320000/52441:ℝ)]]
theorem cell4_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 3 false ν := by
 have heq : naturalFloor cell4 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_3_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_3_3_g]
def cell4_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(2974905690676/1965646003:ℝ), (18220731495920/5896938009:ℝ), (9366777680000/5896938009:ℝ)]]
theorem cell4_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 3 true ν := by
 have heq : naturalFloor cell4 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_3_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_3_3_g]
def cell4_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(77259372/52441:ℝ), (157950080/52441:ℝ), (81320000/52441:ℝ)]]
theorem cell4_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_3_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_3_3_g]
def cell4_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(1132810536000000/2750058481:ℝ), (2272478839736000/2750058481:ℝ), (1134975044000000/2750058481:ℝ)],
  ![(2272478839736000/2750058481:ℝ), (16980220824159088000/10254968075649:ℝ), (8472219656152000000/10254968075649:ℝ)],
  ![(1134975044000000/2750058481:ℝ), (8472219656152000000/10254968075649:ℝ), (4223471308000000000/10254968075649:ℝ)]]
theorem cell4_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 3 3 b ν := by
 have heq : pairedCleared cell4 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_3_3_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_3_3_g]
theorem cell4_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_3_3 hb hν
def cell4_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(80623370346816687/15249516250600000:ℝ)]]
theorem cell4_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 3 4) := by
 have heq : (-orderedLow cell4 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_3_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_3_4_g]
def cell4_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(733628363574012726269/399849940848857300:ℝ), (1505322981308584222969/399849940848857300:ℝ), (7780922167881532135/3998499408488573:ℝ)]]
theorem cell4_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 3 4 ν := by
 have heq : mixedLowHigh cell4 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_3_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_3_4_g]
def cell4_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(83124496/52441:ℝ), (172045440/52441:ℝ), (89760000/52441:ℝ)]]
theorem cell4_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 4 false ν := by
 have heq : naturalFloor cell4 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_3_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_3_4_g]
def cell4_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(9505251750704/5896938009:ℝ), (58957818947680/17690814027:ℝ), (30725116720000/17690814027:ℝ)]]
theorem cell4_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 4 true ν := by
 have heq : naturalFloor cell4 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_3_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_3_4_g]
def cell4_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(83124496/52441:ℝ), (172045440/52441:ℝ), (89760000/52441:ℝ)]]
theorem cell4_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_3_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_3_4_g]
def cell4_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(1269386404000000/2750058481:ℝ), (7688154426944000/8250175443:ℝ), (3861222176000000/8250175443:ℝ)],
  ![(7520130123208000/8250175443:ℝ), (56572905827500808000/30764904226947:ℝ), (28394630299532000000/30764904226947:ℝ)],
  ![(3697891132000000/8250175443:ℝ), (27801995245532000000/30764904226947:ℝ), (13946853578000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 3 4 b ν := by
 have heq : pairedCleared cell4 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_3_4_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_3_4_g]
theorem cell4_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_3_4 hb hν
def cell4_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(17599348747344813/3812379062650000:ℝ)]]
theorem cell4_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 3 5) := by
 have heq : (-orderedLow cell4 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_3_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_3_5_g]
def cell4_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(147809776522752568531/99962485212214325:ℝ), (312517091995902318531/99962485212214325:ℝ), (6668262607095761460/3998499408488573:ℝ)]]
theorem cell4_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 3 5 ν := by
 have heq : mixedLowHigh cell4 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_3_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_3_5_g]
def cell4_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(88989620/52441:ℝ), (186140800/52441:ℝ), (98200000/52441:ℝ)]]
theorem cell4_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 5 false ν := by
 have heq : naturalFloor cell4 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_3_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_3_5_g]
def cell4_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(10085786429380/5896938009:ℝ), (63253443407600/17690814027:ℝ), (33349900400000/17690814027:ℝ)]]
theorem cell4_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 5 true ν := by
 have heq : naturalFloor cell4 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_3_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_3_5_g]
def cell4_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(88989620/52441:ℝ), (186140800/52441:ℝ), (98200000/52441:ℝ)]]
theorem cell4_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_3_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_3_5_g]
def cell4_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(1051856432000000/2750058481:ℝ), (6499474814680000/8250175443:ℝ), (3320439220000000/8250175443:ℝ)],
  ![(6713026207208000/8250175443:ℝ), (51290822910444352000/30764904226947:ℝ), (26088310310608000000/30764904226947:ℝ)],
  ![(3543377132000000/8250175443:ℝ), (26952498602608000000/30764904226947:ℝ), (13657113232000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 3 5 b ν := by
 have heq : pairedCleared cell4 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_3_5_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_3_5_g]
theorem cell4_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_3_5 hb hν
def cell4_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(81279119840537939/15249516250600000:ℝ)]]
theorem cell4_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 3 6) := by
 have heq : (-orderedLow cell4 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_3_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_3_6_g]
def cell4_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(684981690841572638793/399849940848857300:ℝ), (1452576449082458423093/399849940848857300:ℝ), (7771911568212583595/3998499408488573:ℝ)]]
theorem cell4_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 3 6 ν := by
 have heq : mixedLowHigh cell4 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_3_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_3_6_g]
def cell4_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(94854744/52441:ℝ), (200236160/52441:ℝ), (106640000/52441:ℝ)]]
theorem cell4_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 6 false ν := by
 have heq : naturalFloor cell4 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_3_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_3_6_g]
def cell4_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(94854744/52441:ℝ), (200236160/52441:ℝ), (106640000/52441:ℝ)]]
theorem cell4_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 3 6 true ν := by
 have heq : naturalFloor cell4 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_3_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_3_6_g]
def cell4_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(94854744/52441:ℝ), (200236160/52441:ℝ), (106640000/52441:ℝ)]]
theorem cell4_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_3_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_3_6_g]
def cell4_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(1188432300000000/2750058481:ℝ), (2456730907472000/2750058481:ℝ), (1258912088000000/2750058481:ℝ)],
  ![(2471906603736000/2750058481:ℝ), (6324785140607544000/3418322691883:ℝ), (3229586849076000000/3418322691883:ℝ)],
  ![(1278781044000000/2750058481:ℝ), (3259759431076000000/3418322691883:ℝ), (1659283654000000000/3418322691883:ℝ)]]
theorem cell4_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 3 6 b ν := by
 have heq : pairedCleared cell4 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_3_6_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_3_6_g]
theorem cell4_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_3_6 hb hν
def cell4_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(14841845639281417/9149709750360000:ℝ)]]
theorem cell4_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 4 1) := by
 have heq : (-orderedLow cell4 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_4_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_4_1_g]
def cell4_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(1666508036856030912/3998499408488573:ℝ), (11720137652199419860/11995498225465719:ℝ), (6768595534533190000/11995498225465719:ℝ)]]
theorem cell4_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 4 1 ν := by
 have heq : mixedLowHigh cell4 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_4_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_4_1_g]
def cell4_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(31285124/52441:ℝ), (69515360/52441:ℝ), (38440000/52441:ℝ)]]
theorem cell4_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 1 false ν := by
 have heq : naturalFloor cell4 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_4_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_4_1_g]
def cell4_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(3359995608676/5896938009:ℝ), (22531992249920/17690814027:ℝ), (12522768680000/17690814027:ℝ)]]
theorem cell4_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 1 true ν := by
 have heq : naturalFloor cell4 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_4_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_4_1_g]
def cell4_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(16369124/52441:ℝ), (40599360/52441:ℝ), (24440000/52441:ℝ)]]
theorem cell4_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_4_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_4_1_g]
def cell4_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(136575868000000/2750058481:ℝ), (1145517907736000/8250175443:ℝ), (731097044000000/8250175443:ℝ)],
  ![(1099990818944000/8250175443:ℝ), (10490834121853720000/30764904226947:ℝ), (6355040783380000000/30764904226947:ℝ)],
  ![(671490176000000/8250175443:ℝ), (6083487545380000000/30764904226947:ℝ), (3563074270000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 4 1 b ν := by
 have heq : pairedCleared cell4 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_4_1_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_4_1_g]
theorem cell4_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_4_1 hb hν
def cell4_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(53427201374941573/22874274375900000:ℝ)]]
theorem cell4_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 4 2) := by
 have heq : (-orderedLow cell4 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_4_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_4_2_g]
def cell4_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(10255633455293168792/11995498225465719:ℝ), (23001207306633603040/11995498225465719:ℝ), (12841537837144160000/11995498225465719:ℝ)]]
theorem cell4_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 4 2 ν := by
 have heq : mixedLowHigh cell4 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_4_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_4_2_g]
def cell4_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(136870744/157323:ℝ), (306252160/157323:ℝ), (56880000/52441:ℝ)]]
theorem cell4_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 2 false ν := by
 have heq : naturalFloor cell4 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_4_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_4_2_g]
def cell4_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(136870744/157323:ℝ), (306252160/157323:ℝ), (56880000/52441:ℝ)]]
theorem cell4_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 2 true ν := by
 have heq : naturalFloor cell4 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_4_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_4_2_g]
def cell4_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(129412744/157323:ℝ), (97264720/52441:ℝ), (163640000/157323:ℝ)]]
theorem cell4_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_4_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_4_2_g]
def cell4_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(525928216000000/2750058481:ℝ), (1192641751824000/2750058481:ℝ), (663584696000000/2750058481:ℝ)],
  ![(3364373862944000/8250175443:ℝ), (3119411870959696000/3418322691883:ℝ), (5153700518152000000/10254968075649:ℝ)],
  ![(1767816176000000/8250175443:ℝ), (1621879251384000000/3418322691883:ℝ), (2657291308000000000/10254968075649:ℝ)]]
theorem cell4_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 4 2 b ν := by
 have heq : pairedCleared cell4 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_4_2_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_4_2_g]
theorem cell4_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_4_2 hb hν
def cell4_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(266145778554935939/45748548751800000:ℝ)]]
theorem cell4_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 4 3) := by
 have heq : (-orderedLow cell4 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_4_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_4_3_g]
def cell4_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(20942095536856904848/11995498225465719:ℝ), (42000057135496446220/11995498225465719:ℝ), (7067302525781710000/3998499408488573:ℝ)]]
theorem cell4_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 4 3 ν := by
 have heq : mixedLowHigh cell4 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_4_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_4_3_g]
def cell4_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(251106116/157323:ℝ), (505178240/157323:ℝ), (85320000/52441:ℝ)]]
theorem cell4_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 3 false ν := by
 have heq : naturalFloor cell4 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_4_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_4_3_g]
def cell4_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(9570195846028/5896938009:ℝ), (57725593809760/17690814027:ℝ), (29227296040000/17690814027:ℝ)]]
theorem cell4_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 3 true ν := by
 have heq : naturalFloor cell4 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_4_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_4_3_g]
def cell4_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(251106116/157323:ℝ), (505178240/157323:ℝ), (85320000/52441:ℝ)]]
theorem cell4_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_4_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_4_3_g]
def cell4_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(1269386404000000/2750058481:ℝ), (7520130123208000/8250175443:ℝ), (3697891132000000/8250175443:ℝ)],
  ![(7688154426944000/8250175443:ℝ), (56572905827500808000/30764904226947:ℝ), (27801995245532000000/30764904226947:ℝ)],
  ![(3861222176000000/8250175443:ℝ), (28394630299532000000/30764904226947:ℝ), (13946853578000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 4 3 b ν := by
 have heq : pairedCleared cell4 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_4_3_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_4_3_g]
theorem cell4_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_4_3 hb hν
def cell4_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(1644924976423/228742743759:ℝ)]]
theorem cell4_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 4 4) := by
 have heq : (-orderedLow cell4 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_4_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_4_4_g]
def cell4_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(9290016332292503488/3998499408488573:ℝ), (56522146127412898960/11995498225465719:ℝ), (28844025102142840000/11995498225465719:ℝ)]]
theorem cell4_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 4 4 ν := by
 have heq : mixedLowHigh cell4 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_4_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_4_4_g]
def cell4_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(112956496/52441:ℝ), (229877440/52441:ℝ), (117760000/52441:ℝ)]]
theorem cell4_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 4 false ν := by
 have heq : naturalFloor cell4 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_4_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_4_4_g]
def cell4_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(13017815618704/5896938009:ℝ), (79386076551680/17690814027:ℝ), (40615682720000/17690814027:ℝ)]]
theorem cell4_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 4 true ν := by
 have heq : naturalFloor cell4 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_4_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_4_4_g]
def cell4_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(112956496/52441:ℝ), (229877440/52441:ℝ), (117760000/52441:ℝ)]]
theorem cell4_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_4_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_4_4_g]
def cell4_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(1658738752000000/2750058481:ℝ), (9952537470944000/8250175443:ℝ), (4957548176000000/8250175443:ℝ)],
  ![(9952537470944000/8250175443:ℝ), (74156778544284352000/30764904226947:ℝ), (36908056016608000000/30764904226947:ℝ)],
  ![(4957548176000000/8250175443:ℝ), (36908056016608000000/30764904226947:ℝ), (18355653232000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 4 4 b ν := by
 have heq : pairedCleared cell4 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_4_4_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_4_4_g]
theorem cell4_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_4_4 hb hν
def cell4_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(346990634237500061/45748548751800000:ℝ)]]
theorem cell4_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 4 5) := by
 have heq : (-orderedLow cell4 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_4_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_4_5_g]
def cell4_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(1022744217979812713469/399849940848857300:ℝ), (6259738856037837342907/1199549822546571900:ℝ), (32154971985493306405/11995498225465719:ℝ)]]
theorem cell4_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 4 5 ν := by
 have heq : mixedLowHigh cell4 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_4_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_4_5_g]
def cell4_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(118821620/52441:ℝ), (243972800/52441:ℝ), (126200000/52441:ℝ)]]
theorem cell4_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 5 false ν := by
 have heq : naturalFloor cell4 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_4_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_4_5_g]
def cell4_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(4532783432460/1965646003:ℝ), (27893900337200/5896938009:ℝ), (14413488800000/5896938009:ℝ)]]
theorem cell4_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 5 true ν := by
 have heq : naturalFloor cell4 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_4_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_4_5_g]
def cell4_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(118821620/52441:ℝ), (243972800/52441:ℝ), (126200000/52441:ℝ)]]
theorem cell4_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_4_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_4_5_g]
def cell4_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(1795314620000000/2750058481:ℝ), (10823255378680000/8250175443:ℝ), (5413845220000000/8250175443:ℝ)],
  ![(3551743691648000/2750058481:ℝ), (26596340633102632000/10254968075649:ℝ), (13295342449228000000/10254968075649:ℝ)],
  ![(1750171392000000/2750058481:ℝ), (4365932477076000000/3418322691883:ℝ), (2181343654000000000/3418322691883:ℝ)]]
theorem cell4_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 4 5 b ν := by
 have heq : pairedCleared cell4 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_4_5_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_4_5_g]
theorem cell4_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_4_5 hb hν
def cell4_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(79078177041296939/11437137187950000:ℝ)]]
theorem cell4_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 4 6) := by
 have heq : (-orderedLow cell4 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_4_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_4_6_g]
def cell4_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(220088740124202565331/99962485212214325:ℝ), (1373493754015728124093/299887455636642975:ℝ), (28816993303135994380/11995498225465719:ℝ)]]
theorem cell4_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 4 6 ν := by
 have heq : mixedLowHigh cell4 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_4_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_4_6_g]
def cell4_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(124686744/52441:ℝ), (258068160/52441:ℝ), (134640000/52441:ℝ)]]
theorem cell4_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 6 false ν := by
 have heq : naturalFloor cell4 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_4_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_4_6_g]
def cell4_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(14178884976056/5896938009:ℝ), (87977325471520/17690814027:ℝ), (45865250080000/17690814027:ℝ)]]
theorem cell4_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 4 6 true ν := by
 have heq : naturalFloor cell4 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_4_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_4_6_g]
def cell4_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(124686744/52441:ℝ), (258068160/52441:ℝ), (134640000/52441:ℝ)]]
theorem cell4_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_4_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_4_6_g]
def cell4_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(1577784648000000/2750058481:ℝ), (3211525255472000/2750058481:ℝ), (1624354088000000/2750058481:ℝ)],
  ![(9848127158944000/8250175443:ℝ), (74506938982251440000/30764904226947:ℝ), (37579707358760000000/30764904226947:ℝ)],
  ![(5096000176000000/8250175443:ℝ), (38443895650760000000/30764904226947:ℝ), (19342352540000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 4 6 b ν := by
 have heq : pairedCleared cell4 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_4_6_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_4_6_g]
theorem cell4_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_4_6 hb hν
def cell4_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(4583893026249407/1429642148493750:ℝ)]]
theorem cell4_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 5 1) := by
 have heq : (-orderedLow cell4 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_5_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_5_1_g]
def cell4_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(8416890398017016296/11995498225465719:ℝ), (17876767118886083420/11995498225465719:ℝ), (9507858713770930000/11995498225465719:ℝ)]]
theorem cell4_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 5 1 ν := by
 have heq : mixedLowHigh cell4 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_5_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_5_1_g]
def cell4_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(157931372/157323:ℝ), (326622080/157323:ℝ), (56440000/52441:ℝ)]]
theorem cell4_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 1 false ν := by
 have heq : naturalFloor cell4 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_5_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_5_1_g]
def cell4_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(5682763666676/5896938009:ℝ), (3927790824880/1965646003:ℝ), (6124196560000/5896938009:ℝ)]]
theorem cell4_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 1 true ν := by
 have heq : naturalFloor cell4 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_5_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_5_1_g]
def cell4_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(90809372/157323:ℝ), (196500080/157323:ℝ), (35440000/52441:ℝ)]]
theorem cell4_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_5_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_5_1_g]
def cell4_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(273151736000000/2750058481:ℝ), (616070503912000/2750058481:ℝ), (341354348000000/2750058481:ℝ)],
  ![(1970708726680000/8250175443:ℝ), (5374359158959088000/10254968075649:ℝ), (2913459020152000000/10254968075649:ℝ)],
  ![(1127787220000000/8250175443:ℝ), (3020486292152000000/10254968075649:ℝ), (1613171308000000000/10254968075649:ℝ)]]
theorem cell4_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 5 1 b ν := by
 have heq : pairedCleared cell4 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_5_1_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_5_1_g]
theorem cell4_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_5_1 hb hν
def cell4_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(35865950278691417/9149709750360000:ℝ)]]
theorem cell4_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 5 2) := by
 have heq : (-orderedLow cell4 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_5_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_5_2_g]
def cell4_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(4557666580914030784/3998499408488573:ℝ), (29157836773320266600/11995498225465719:ℝ), (15580801016381900000/11995498225465719:ℝ)]]
theorem cell4_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 5 2 ν := by
 have heq : mixedLowHigh cell4 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_5_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_5_2_g]
def cell4_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(66982248/52441:ℝ), (141442720/52441:ℝ), (74880000/52441:ℝ)]]
theorem cell4_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 2 false ν := by
 have heq : naturalFloor cell4 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_5_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_5_2_g]
def cell4_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(7453094155352/5896938009:ℝ), (47255874313840/17690814027:ℝ), (25038118360000/17690814027:ℝ)]]
theorem cell4_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 2 true ν := by
 have heq : naturalFloor cell4 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_5_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_5_2_g]
def cell4_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(57038248/52441:ℝ), (366496160/157323:ℝ), (196640000/157323:ℝ)]]
theorem cell4_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_5_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_5_2_g]
def cell4_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(662504084000000/2750058481:ℝ), (4280618859472000/8250175443:ℝ), (2283720088000000/8250175443:ℝ)],
  ![(4235091770680000/8250175443:ℝ), (33706950193660808000/30764904226947:ℝ), (17846437831532000000/30764904226947:ℝ)],
  ![(2224113220000000/8250175443:ℝ), (17574884593532000000/30764904226947:ℝ), (9248313578000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 5 2 b ν := by
 have heq : pairedCleared cell4 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_5_2_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_5_2_g]
theorem cell4_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_5_2 hb hν
def cell4_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(105987462973466573/22874274375900000:ℝ)]]
theorem cell4_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 5 3) := by
 have heq : (-orderedLow cell4 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_5_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_5_3_g]
def cell4_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(18929109087467168408/11995498225465719:ℝ), (40438906427754449780/11995498225465719:ℝ), (7217914439664290000/3998499408488573:ℝ)]]
theorem cell4_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 5 3 ν := by
 have heq : mixedLowHigh cell4 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_5_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_5_3_g]
def cell4_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(243962116/157323:ℝ), (522034240/157323:ℝ), (93320000/52441:ℝ)]]
theorem cell4_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 3 false ν := by
 have heq : naturalFloor cell4 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_5_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_5_3_g]
def cell4_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(9223424644028/5896938009:ℝ), (59161631203760/17690814027:ℝ), (31703647040000/17690814027:ℝ)]]
theorem cell4_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 3 true ν := by
 have heq : naturalFloor cell4 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_5_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_5_3_g]
def cell4_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(243962116/157323:ℝ), (522034240/157323:ℝ), (93320000/52441:ℝ)]]
theorem cell4_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_5_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_5_3_g]
def cell4_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(1051856432000000/2750058481:ℝ), (6713026207208000/8250175443:ℝ), (3543377132000000/8250175443:ℝ)],
  ![(6499474814680000/8250175443:ℝ), (51290822910444352000/30764904226947:ℝ), (26952498602608000000/30764904226947:ℝ)],
  ![(3320439220000000/8250175443:ℝ), (26088310310608000000/30764904226947:ℝ), (13657113232000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 5 3 b ν := by
 have heq : pairedCleared cell4 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_5_3_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_5_3_g]
theorem cell4_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_5_3 hb hν
def cell4_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(371266301751985939/45748548751800000:ℝ)]]
theorem cell4_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 5 4) := by
 have heq : (-orderedLow cell4 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_5_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_5_4_g]
def cell4_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(29615571169030904464/11995498225465719:ℝ), (59437756256617292960/11995498225465719:ℝ), (30014113059193840000/11995498225465719:ℝ)]]
theorem cell4_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 5 4 ν := by
 have heq : mixedLowHigh cell4 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_5_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_5_4_g]
def cell4_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(358197488/157323:ℝ), (720960320/157323:ℝ), (121760000/52441:ℝ)]]
theorem cell4_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 4 false ν := by
 have heq : naturalFloor cell4 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_5_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_5_4_g]
def cell4_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(13663294392704/5896938009:ℝ), (27483158624560/5896938009:ℝ), (13914215240000/5896938009:ℝ)]]
theorem cell4_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 4 true ν := by
 have heq : naturalFloor cell4 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_5_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_5_4_g]
def cell4_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(358197488/157323:ℝ), (720960320/157323:ℝ), (121760000/52441:ℝ)]]
theorem cell4_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_5_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_5_4_g]
def cell4_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(1795314620000000/2750058481:ℝ), (3551743691648000/2750058481:ℝ), (1750171392000000/2750058481:ℝ)],
  ![(10823255378680000/8250175443:ℝ), (26596340633102632000/10254968075649:ℝ), (4365932477076000000/3418322691883:ℝ)],
  ![(5413845220000000/8250175443:ℝ), (13295342449228000000/10254968075649:ℝ), (2181343654000000000/3418322691883:ℝ)]]
theorem cell4_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 5 4 b ν := by
 have heq : pairedCleared cell4 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_5_4_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_5_4_g]
theorem cell4_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_5_4 hb hν
def cell4_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(8682110369633/914970975036:ℝ)]]
theorem cell4_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 5 5) := by
 have heq : (-orderedLow cell4 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_5_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_5_5_g]
def cell4_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(12181174876350503360/3998499408488573:ℝ), (73959845248533745700/11995498225465719:ℝ), (37656230583991550000/11995498225465719:ℝ)]]
theorem cell4_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 5 5 ν := by
 have heq : mixedLowHigh cell4 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_5_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_5_5_g]
def cell4_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(148653620/52441:ℝ), (301804800/52441:ℝ), (154200000/52441:ℝ)]]
theorem cell4_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 5 false ν := by
 have heq : naturalFloor cell4 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_5_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_5_5_g]
def cell4_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(17110914165380/5896938009:ℝ), (104109958615600/17690814027:ℝ), (53131032400000/17690814027:ℝ)]]
theorem cell4_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 5 true ν := by
 have heq : naturalFloor cell4 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_5_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_5_5_g]
def cell4_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(148653620/52441:ℝ), (301804800/52441:ℝ), (154200000/52441:ℝ)]]
theorem cell4_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_5_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_5_5_g]
def cell4_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(2184666968000000/2750058481:ℝ), (13087638422680000/8250175443:ℝ), (6510171220000000/8250175443:ℝ)],
  ![(13087638422680000/8250175443:ℝ), (97372894616091440000/30764904226947:ℝ), (48399453064760000000/30764904226947:ℝ)],
  ![(6510171220000000/8250175443:ℝ), (48399453064760000000/30764904226947:ℝ), (24040892540000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 5 5 b ν := by
 have heq : pairedCleared cell4 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_5_5_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_5_5_g]
theorem cell4_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_5_5 hb hν
def cell4_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(452111157434550061/45748548751800000:ℝ)]]
theorem cell4_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 5 6) := by
 have heq : (-orderedLow cell4 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_5_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_5_6_g]
def cell4_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(1311860072385612700669/399849940848857300:ℝ), (8003508768149922016907/1199549822546571900:ℝ), (40967177467342016405/11995498225465719:ℝ)]]
theorem cell4_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 5 6 ν := by
 have heq : mixedLowHigh cell4 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_5_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_5_6_g]
def cell4_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(154518744/52441:ℝ), (315900160/52441:ℝ), (162640000/52441:ℝ)]]
theorem cell4_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 6 false ν := by
 have heq : naturalFloor cell4 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_5_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_5_6_g]
def cell4_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(17691448844056/5896938009:ℝ), (108405583075520/17690814027:ℝ), (55755816080000/17690814027:ℝ)]]
theorem cell4_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 5 6 true ν := by
 have heq : naturalFloor cell4 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_5_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_5_6_g]
def cell4_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(154518744/52441:ℝ), (315900160/52441:ℝ), (162640000/52441:ℝ)]]
theorem cell4_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_5_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_5_6_g]
def cell4_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(2321242836000000/2750058481:ℝ), (4652785443472000/2750058481:ℝ), (2322156088000000/2750058481:ℝ)],
  ![(13790332026680000/8250175443:ℝ), (9364103451919544000/2796809475177:ℝ), (4670674945076000000/2796809475177:ℝ)],
  ![(6803137220000000/8250175443:ℝ), (4616799031076000000/2796809475177:ℝ), (2301575654000000000/2796809475177:ℝ)]]
theorem cell4_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 5 6 b ν := by
 have heq : pairedCleared cell4 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_5_6_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_5_6_g]
theorem cell4_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_5_6 hb hν
def cell4_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(94161008703114443/15249516250600000:ℝ)]]
theorem cell4_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 6 1) := by
 have heq : (-orderedLow cell4 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_6_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_6_1_g]
def cell4_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(945910597623644218021/599774911273285950:ℝ), (629437956971457831907/199924970424428650:ℝ), (18896047458716448430/11995498225465719:ℝ)]]
theorem cell4_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 6 1 ν := by
 have heq : mixedLowHigh cell4 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_6_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_6_1_g]
def cell4_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(222007372/157323:ℝ), (444698080/157323:ℝ), (74440000/52441:ℝ)]]
theorem cell4_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 1 false ν := by
 have heq : naturalFloor cell4 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_6_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_6_1_g]
def cell4_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(2668510574892/1965646003:ℝ), (48168242597920/17690814027:ℝ), (24222410680000/17690814027:ℝ)]]
theorem cell4_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 1 true ν := by
 have heq : naturalFloor cell4 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_6_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_6_1_g]
def cell4_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(132511372/157323:ℝ), (271202080/157323:ℝ), (46440000/52441:ℝ)]]
theorem cell4_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_6_1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_6_1_g]
def cell4_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(763833444000000/2750058481:ℝ), (4610302635736000/8250175443:ℝ), (2314109044000000/8250175443:ℝ)],
  ![(1450408051472000/2750058481:ℝ), (32669647103980808000/30764904226947:ℝ), (16410004657532000000/30764904226947:ℝ)],
  ![(677188088000000/2750058481:ℝ), (15274263127532000000/30764904226947:ℝ), (7682133578000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 6 1 b ν := by
 have heq : pairedCleared cell4 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_6_1_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_6_1_g]
theorem cell4_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_6_1 hb hν
def cell4_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(5245939584104813/953094765662500:ℝ)]]
theorem cell4_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 6 2) := by
 have heq : (-orderedLow cell4 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_6_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_6_2_g]
def cell4_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(17090366030191015912/11995498225465719:ℝ), (11771488746668976720/3998499408488573:ℝ), (18320064195619640000/11995498225465719:ℝ)]]
theorem cell4_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 6 2 ν := by
 have heq : mixedLowHigh cell4 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_6_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_6_2_g]
def cell4_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(265022744/157323:ℝ), (542404160/157323:ℝ), (92880000/52441:ℝ)]]
theorem cell4_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 2 false ν := by
 have heq : naturalFloor cell4 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_6_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_6_2_g]
def cell4_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(3258620737784/1965646003:ℝ), (60073999487840/17690814027:ℝ), (30887939360000/17690814027:ℝ)]]
theorem cell4_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 2 true ν := by
 have heq : naturalFloor cell4 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_6_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_6_2_g]
def cell4_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(212816744/157323:ℝ), (441198160/157323:ℝ), (229640000/157323:ℝ)]]
theorem cell4_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_6_2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_6_2_g]
def cell4_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(799079952000000/2750058481:ℝ), (4983312463472000/8250175443:ℝ), (2576686088000000/8250175443:ℝ)],
  ![(1701936559472000/2750058481:ℝ), (39339193548684352000/30764904226947:ℝ), (20231774108608000000/30764904226947:ℝ)],
  ![(893470088000000/2750058481:ℝ), (20552855924608000000/30764904226947:ℝ), (10524753232000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 6 2 b ν := by
 have heq : pairedCleared cell4 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_6_2_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_6_2_g]
theorem cell4_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_6_2 hb hν
def cell4_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(18963351639367139/3049903250120000:ℝ)]]
theorem cell4_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 6 3) := by
 have heq : (-orderedLow cell4 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_6_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_6_3_g]
def cell4_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(7448825124972030656/3998499408488573:ℝ), (15531845298147037780/3998499408488573:ℝ), (8131002166076870000/3998499408488573:ℝ)]]
theorem cell4_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 6 3 ν := by
 have heq : mixedLowHigh cell4 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_6_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_6_3_g]
def cell4_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(102679372/52441:ℝ), (213370080/52441:ℝ), (111320000/52441:ℝ)]]
theorem cell4_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 3 false ν := by
 have heq : naturalFloor cell4 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_6_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_6_3_g]
def cell4_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(102679372/52441:ℝ), (213370080/52441:ℝ), (111320000/52441:ℝ)]]
theorem cell4_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 3 true ν := by
 have heq : naturalFloor cell4 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_6_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_6_3_g]
def cell4_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(97707372/52441:ℝ), (611194240/157323:ℝ), (319960000/157323:ℝ)]]
theorem cell4_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_6_3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_6_3_g]
def cell4_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(1188432300000000/2750058481:ℝ), (2471906603736000/2750058481:ℝ), (1278781044000000/2750058481:ℝ)],
  ![(2456730907472000/2750058481:ℝ), (6324785140607544000/3418322691883:ℝ), (3259759431076000000/3418322691883:ℝ)],
  ![(1258912088000000/2750058481:ℝ), (3229586849076000000/3418322691883:ℝ), (1659283654000000000/3418322691883:ℝ)]]
theorem cell4_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 6 3 b ν := by
 have heq : pairedCleared cell4 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_6_3_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_6_3_g]
theorem cell4_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_6_3 hb hν
def cell4_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(52849241523997191/7624758125300000:ℝ)]]
theorem cell4_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 6 4) := by
 have heq : (-orderedLow cell4 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_6_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_6_4_g]
def cell4_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(27602584719641168024/11995498225465719:ℝ), (19292201849625098840/3998499408488573:ℝ), (30465948800841580000/11995498225465719:ℝ)]]
theorem cell4_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 6 4 ν := by
 have heq : mixedLowHigh cell4 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_6_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_6_4_g]
def cell4_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(351053488/157323:ℝ), (737816320/157323:ℝ), (129760000/52441:ℝ)]]
theorem cell4_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 4 false ν := by
 have heq : naturalFloor cell4 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_6_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_6_4_g]
def cell4_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(4438841063568/1965646003:ℝ), (83885513267680/17690814027:ℝ), (44218996720000/17690814027:ℝ)]]
theorem cell4_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 4 true ν := by
 have heq : naturalFloor cell4 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_6_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_6_4_g]
def cell4_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(351053488/157323:ℝ), (737816320/157323:ℝ), (129760000/52441:ℝ)]]
theorem cell4_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_6_4_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_6_4_g]
def cell4_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(1577784648000000/2750058481:ℝ), (9848127158944000/8250175443:ℝ), (5096000176000000/8250175443:ℝ)],
  ![(3211525255472000/2750058481:ℝ), (74506938982251440000/30764904226947:ℝ), (38443895650760000000/30764904226947:ℝ)],
  ![(1624354088000000/2750058481:ℝ), (37579707358760000000/30764904226947:ℝ), (19342352540000000000/30764904226947:ℝ)]]
theorem cell4_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 6 4 b ν := by
 have heq : pairedCleared cell4 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_6_4_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_6_4_g]
theorem cell4_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_6_4 hb hν
def cell4_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(158795608316345313/15249516250600000:ℝ)]]
theorem cell4_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 6 5) := by
 have heq : (-orderedLow cell4 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_6_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_6_5_g]
def cell4_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(38289046801204904080/11995498225465719:ℝ), (25625151792579379900/3998499408488573:ℝ), (38826318541042550000/11995498225465719:ℝ)]]
theorem cell4_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 6 5 ν := by
 have heq : mixedLowHigh cell4 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_6_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_6_5_g]
def cell4_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(465288860/157323:ℝ), (936742400/157323:ℝ), (158200000/52441:ℝ)]]
theorem cell4_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 5 false ν := by
 have heq : naturalFloor cell4 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_6_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_6_5_g]
def cell4_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(5918797646460/1965646003:ℝ), (107173357937600/17690814027:ℝ), (54257995400000/17690814027:ℝ)]]
theorem cell4_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 5 true ν := by
 have heq : naturalFloor cell4 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_6_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_6_5_g]
def cell4_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(465288860/157323:ℝ), (936742400/157323:ℝ), (158200000/52441:ℝ)]]
theorem cell4_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_6_5_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_6_5_g]
def cell4_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(2321242836000000/2750058481:ℝ), (13790332026680000/8250175443:ℝ), (6803137220000000/8250175443:ℝ)],
  ![(4652785443472000/2750058481:ℝ), (9364103451919544000/2796809475177:ℝ), (4616799031076000000/2796809475177:ℝ)],
  ![(2322156088000000/2750058481:ℝ), (4670674945076000000/2796809475177:ℝ), (2301575654000000000/2796809475177:ℝ)]]
theorem cell4_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 6 5 b ν := by
 have heq : pairedCleared cell4 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_6_5_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_6_5_g]
theorem cell4_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_6_5 hb hν
def cell4_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(1797420138929/152495162506:ℝ)]]
theorem cell4_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell4 6 6) := by
 have heq : (-orderedLow cell4 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell4_ordered_6_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_ordered_6_6_g]
def cell4_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(15072333420408503232/3998499408488573:ℝ), (30465848123218197480/3998499408488573:ℝ), (15489478688613420000/3998499408488573:ℝ)]]
theorem cell4_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell4 6 6 ν := by
 have heq : mixedLowHigh cell4 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_mixed_6_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_mixed_6_6_g]
def cell4_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(184350744/52441:ℝ), (373732160/52441:ℝ), (190640000/52441:ℝ)]]
theorem cell4_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 6 false ν := by
 have heq : naturalFloor cell4 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor0_6_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor0_6_6_g]
def cell4_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(7068004237352/1965646003:ℝ), (42944613559840/5896938009:ℝ), (21882127360000/5896938009:ℝ)]]
theorem cell4_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell4 6 6 true ν := by
 have heq : naturalFloor cell4 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_floor1_6_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_floor1_6_6_g]
def cell4_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(184350744/52441:ℝ), (373732160/52441:ℝ), (190640000/52441:ℝ)]]
theorem cell4_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell4_complement_floor_6_6_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_complement_floor_6_6_g]
def cell4_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(2710595184000000/2750058481:ℝ), (5407579791472000/2750058481:ℝ), (2687598088000000/2750058481:ℝ)],
  ![(5407579791472000/2750058481:ℝ), (40196336895966176000/10254968075649:ℝ), (19963616704304000000/10254968075649:ℝ)],
  ![(2687598088000000/2750058481:ℝ), (19963616704304000000/10254968075649:ℝ), (9908710616000000000/10254968075649:ℝ)]]
theorem cell4_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell4 6 6 b ν := by
 have heq : pairedCleared cell4 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell4_paired_cleared_6_6_g (1271/2000:ℝ) (3/4:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_cleared_6_6_g]
theorem cell4_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) : 0 ≤ pairedGap cell4 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell4_paired_cleared_6_6 hb hν
def cell4_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(29664540388336939/45748548751800000:ℝ)]]
theorem cell4_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell4.q/K)+1+17/50*(cell4.q/cell4.priorL)+17/25*(cell4.q/cell4.priorL)*cell4.priorB) := by
 have heq : ((2-17/50-17/25)*(cell4.q/K)+1+17/50*(cell4.q/cell4.priorL)+17/25*(cell4.q/cell4.priorL)*cell4.priorB) = Record12518109.Bernstein.bsum 0 0 (29664540388336939/45748548751800000:ℝ) cell4_increment0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_increment0_g]
def cell4_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(203609824989/406838200000:ℝ)]]
theorem cell4_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell4.q/cell4.priorL)*(1-cell4.priorB)) := by
 have heq : (1+17/25*(cell4.q/cell4.priorL)*(1-cell4.priorB)) = Record12518109.Bernstein.bsum 0 0 (203609824989/406838200000:ℝ) cell4_increment1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_increment1_g]
def cell4_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(814248574967/1627352800000:ℝ)]]
theorem cell4_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell4.q/cell4.priorL)*(1-cell4.priorB)) := by
 have heq : (1+omega*(cell4.q/cell4.priorL)*(1-cell4.priorB)) = Record12518109.Bernstein.bsum 0 0 (814248574967/1627352800000:ℝ) cell4_increment2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_increment2_g]
def cell4_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(6173284/52441:ℝ), (36807040/157323:ℝ), (18916480/157323:ℝ)]]
theorem cell4_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (57511/37500:ℝ) cell4_high_increment_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_high_increment_g]
def cell4_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(136660679482/12008989:ℝ), (1115515716514/12008989:ℝ), (1884319041554/12008989:ℝ), (861799320518/12008989:ℝ)]]
theorem cell4_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (68330339741/4000000000:ℝ) cell4_three_gate0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_three_gate0_g]
def cell4_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(2932562/52441:ℝ), (8230236/52441:ℝ), (5507438/52441:ℝ)]]
theorem cell4_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (1466281/2000000:ℝ) cell4_three_gate1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_three_gate1_g]
def cell4_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(1960411625048/17690814027:ℝ), (3909213365960/17690814027:ℝ), (224396110780/1965646003:ℝ)]]
theorem cell4_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell4.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell4.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (97730334149/67469400000:ℝ) cell4_three_gate2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_three_gate2_g]
def cell4_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(642919/1349388:ℝ)]]
theorem cell4_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (1-cell4.q/K/3) := by
 have heq : (1-cell4.q/K/3) = Record12518109.Bernstein.bsum 0 0 (642919/1349388:ℝ) cell4_paired_margin0_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_margin0_g]
def cell4_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(4330937/44748000:ℝ)]]
theorem cell4_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (gamma cell4-13/50) := by
 have heq : (gamma cell4-13/50) = Record12518109.Bernstein.bsum 0 0 (4330937/44748000:ℝ) cell4_paired_margin1_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_margin1_g]
def cell4_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(8141/89496:ℝ)]]
theorem cell4_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (cell4.q-gamma cell4) := by
 have heq : (cell4.q-gamma cell4) = Record12518109.Bernstein.bsum 0 0 (8141/89496:ℝ) cell4_paired_margin2_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_margin2_g]
def cell4_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(91174261/313236000:ℝ)]]
theorem cell4_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4:ℝ)) : 0 < (min (cell4.q+rho cell4.q) (3/4+rho (3/4))-gamma cell4) := by
 have heq : (min (cell4.q+rho cell4.q) (3/4+rho (3/4))-gamma cell4) = Record12518109.Bernstein.bsum 0 0 (91174261/313236000:ℝ) cell4_paired_margin3_g (3/80:ℝ) (39/1000:ℝ) (1271/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell4, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell4_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell4_paired_margin3_g]
theorem cell4_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (1271/2000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1271/2000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell4 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell4_paired_1_1 hb hν
 · exact cell4_paired_1_2 hb hν
 · exact cell4_paired_1_3 hb hν
 · exact cell4_paired_1_4 hb hν
 · exact cell4_paired_1_5 hb hν
 · exact cell4_paired_1_6 hb hν
 · exact cell4_paired_2_1 hb hν
 · exact cell4_paired_2_2 hb hν
 · exact cell4_paired_2_3 hb hν
 · exact cell4_paired_2_4 hb hν
 · exact cell4_paired_2_5 hb hν
 · exact cell4_paired_2_6 hb hν
 · exact cell4_paired_3_1 hb hν
 · exact cell4_paired_3_2 hb hν
 · exact cell4_paired_3_3 hb hν
 · exact cell4_paired_3_4 hb hν
 · exact cell4_paired_3_5 hb hν
 · exact cell4_paired_3_6 hb hν
 · exact cell4_paired_4_1 hb hν
 · exact cell4_paired_4_2 hb hν
 · exact cell4_paired_4_3 hb hν
 · exact cell4_paired_4_4 hb hν
 · exact cell4_paired_4_5 hb hν
 · exact cell4_paired_4_6 hb hν
 · exact cell4_paired_5_1 hb hν
 · exact cell4_paired_5_2 hb hν
 · exact cell4_paired_5_3 hb hν
 · exact cell4_paired_5_4 hb hν
 · exact cell4_paired_5_5 hb hν
 · exact cell4_paired_5_6 hb hν
 · exact cell4_paired_6_1 hb hν
 · exact cell4_paired_6_2 hb hν
 · exact cell4_paired_6_3 hb hν
 · exact cell4_paired_6_4 hb hν
 · exact cell4_paired_6_5 hb hν
 · exact cell4_paired_6_6 hb hν
end
end Record12518109Admission
