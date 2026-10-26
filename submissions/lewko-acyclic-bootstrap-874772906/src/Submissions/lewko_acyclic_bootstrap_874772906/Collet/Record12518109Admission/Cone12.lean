/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell12
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell12_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(111259762941/381237906265:ℝ)]]
theorem cell12_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 1 1) := by
 have heq : (-orderedLow cell12 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_1_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_1_1_g]
def cell12_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(232219386099251672/1927615101657093:ℝ), (536732852994467050/1927615101657093:ℝ), (312223927301843750/1927615101657093:ℝ)]]
theorem cell12_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 1 1 ν := by
 have heq : mixedLowHigh cell12 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_1_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_1_1_g]
def cell12_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(2189599/25281:ℝ), (5385350/25281:ℝ), (3296875/25281:ℝ)]]
theorem cell12_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 1 false ν := by
 have heq : naturalFloor cell12 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_1_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_1_1_g]
def cell12_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(92221351817/947607723:ℝ), (221468624050/947607723:ℝ), (133037703125/947607723:ℝ)]]
theorem cell12_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 1 true ν := by
 have heq : naturalFloor cell12 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_1_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_1_1_g]
def cell12_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(2189599/25281:ℝ), (5385350/25281:ℝ), (3296875/25281:ℝ)]]
theorem cell12_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_1_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_1_1_g]
def cell12_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(502297656250/23671443:ℝ), (10194140871250/213042987:ℝ), (5574592187500/213042987:ℝ)],
  ![(10194140871250/213042987:ℝ), (105671647128490000/999810737991:ℝ), (6325999208593750/111090081999:ℝ)],
  ![(5574592187500/213042987:ℝ), (6325999208593750/111090081999:ℝ), (30339876464843750/999810737991:ℝ)]]
theorem cell12_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 1 1 b ν := by
 have heq : pairedCleared cell12 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_1_1_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_1_1_g]
theorem cell12_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_1_1 hb hν
def cell12_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(13044927678505829/19061895313250000:ℝ)]]
theorem cell12_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 1 2) := by
 have heq : (-orderedLow cell12 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_1_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_1_2_g]
def cell12_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(237070023683396304091/771046040662837200:ℝ), (132124892580708153029/192761510165709300:ℝ), (11903916598589560225/30841841626513488:ℝ)]]
theorem cell12_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 1 2 ν := by
 have heq : mixedLowHigh cell12 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_1_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_1_2_g]
def cell12_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(4379198/25281:ℝ), (10770700/25281:ℝ), (6593750/25281:ℝ)]]
theorem cell12_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 2 false ν := by
 have heq : naturalFloor cell12 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_1_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_1_2_g]
def cell12_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(4379198/25281:ℝ), (10770700/25281:ℝ), (6593750/25281:ℝ)]]
theorem cell12_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 2 true ν := by
 have heq : naturalFloor cell12 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_1_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_1_2_g]
def cell12_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(4379198/25281:ℝ), (10770700/25281:ℝ), (6593750/25281:ℝ)]]
theorem cell12_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_1_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_1_2_g]
def cell12_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(35727295703125/639128961:ℝ), (77788331165000/639128961:ℝ), (41467816796875/639128961:ℝ)],
  ![(22745076808750/213042987:ℝ), (77571570639245000/333270245997:ℝ), (124178964169531250/999810737991:ℝ)],
  ![(32211325390625/639128961:ℝ), (330393844168750000/2999432213973:ℝ), (176630762451171875/2999432213973:ℝ)]]
theorem cell12_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 1 2 b ν := by
 have heq : pairedCleared cell12 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_1_2_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_1_2_g]
theorem cell12_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_1_2 hb hν
def cell12_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(30432812992921/4765473828312500:ℝ)]]
theorem cell12_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 1 3) := by
 have heq : (-orderedLow cell12 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_1_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_1_3_g]
def cell12_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(674100671472677953/64253836721903100:ℝ), (2526365516962295657/16063459180475775:ℝ), (408096297481573675/2570153468876124:ℝ)]]
theorem cell12_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 1 3 ν := by
 have heq : mixedLowHigh cell12 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_1_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_1_3_g]
def cell12_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(2189599/8427:ℝ), (5385350/8427:ℝ), (3296875/8427:ℝ)]]
theorem cell12_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 3 false ν := by
 have heq : naturalFloor cell12 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_1_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_1_3_g]
def cell12_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(236069605451/947607723:ℝ), (585967672150/947607723:ℝ), (361269359375/947607723:ℝ)]]
theorem cell12_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 3 true ν := by
 have heq : naturalFloor cell12 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_1_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_1_3_g]
def cell12_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(2189599/8427:ℝ), (5385350/8427:ℝ), (3296875/8427:ℝ)]]
theorem cell12_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_1_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_1_3_g]
def cell12_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (27530311250/1339893:ℝ), (25664843750/1339893:ℝ)],
  ![(473215933750/12059037:ℝ), (6537925848980000/56593060641:ℝ), (4164878938281250/56593060641:ℝ)],
  ![(467619531250/12059037:ℝ), (5324379914843750/56593060641:ℝ), (3056388671875000/56593060641:ℝ)]]
theorem cell12_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 1 3 b ν := by
 have heq : pairedCleared cell12 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_1_3_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_1_3_g]
theorem cell12_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_1_3 hb hν
def cell12_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(13703477283667513/19061895313250000:ℝ)]]
theorem cell12_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 1 4) := by
 have heq : (-orderedLow cell12 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_1_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_1_4_g]
def cell12_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(152271477301367770727/771046040662837200:ℝ), (108767993484808995913/192761510165709300:ℝ), (11805489331538944325/30841841626513488:ℝ)]]
theorem cell12_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 1 4 ν := by
 have heq : mixedLowHigh cell12 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_1_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_1_4_g]
def cell12_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(8758396/25281:ℝ), (21541400/25281:ℝ), (13187500/25281:ℝ)]]
theorem cell12_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 4 false ν := by
 have heq : naturalFloor cell12 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_1_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_1_4_g]
def cell12_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(307993732268/947607723:ℝ), (768217196200/947607723:ℝ), (475385187500/947607723:ℝ)]]
theorem cell12_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 4 true ν := by
 have heq : naturalFloor cell12 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_1_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_1_4_g]
def cell12_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(8758396/25281:ℝ), (21541400/25281:ℝ), (13187500/25281:ℝ)]]
theorem cell12_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_1_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_1_4_g]
def cell12_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(22165258984375/639128961:ℝ), (60337867017500/639128961:ℝ), (36986170703125/639128961:ℝ)],
  ![(62733252301250/639128961:ℝ), (727639264363675000/2999432213973:ℝ), (422473497605468750/2999432213973:ℝ)],
  ![(40271383984375/639128961:ℝ), (441784001023437500/2999432213973:ℝ), (247599732666015625/2999432213973:ℝ)]]
theorem cell12_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 1 4 b ν := by
 have heq : pairedCleared cell12 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_1_4_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_1_4_g]
theorem cell12_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_1_4 hb hν
def cell12_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(13642611657681671/9530947656625000:ℝ)]]
theorem cell12_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 1 5) := by
 have heq : (-orderedLow cell12 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_1_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_1_5_g]
def cell12_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(148226873272531703009/385523020331418600:ℝ), (93609800383035221971/96380755082854650:ℝ), (9356911546649502275/15420920813256744:ℝ)]]
theorem cell12_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 1 5 ν := by
 have heq : mixedLowHigh cell12 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_1_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_1_5_g]
def cell12_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(10947995/25281:ℝ), (26926750/25281:ℝ), (16484375/25281:ℝ)]]
theorem cell12_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 5 false ν := by
 have heq : naturalFloor cell12 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_1_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_1_5_g]
def cell12_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(379917859085/947607723:ℝ), (950466720250/947607723:ℝ), (589501015625/947607723:ℝ)]]
theorem cell12_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 5 true ν := by
 have heq : naturalFloor cell12 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_1_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_1_5_g]
def cell12_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(10947995/25281:ℝ), (26926750/25281:ℝ), (16484375/25281:ℝ)]]
theorem cell12_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_1_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_1_5_g]
def cell12_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(44330517968750/639128961:ℝ), (107543775568750/639128961:ℝ), (61730210937500/639128961:ℝ)],
  ![(100386060113750/639128961:ℝ), (1108768458731410000/2999432213973:ℝ), (624208411482031250/2999432213973:ℝ)],
  ![(18586310937500/213042987:ℝ), (22273180242968750/111090081999:ℝ), (111070288574218750/999810737991:ℝ)]]
theorem cell12_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 1 5 b ν := by
 have heq : pairedCleared cell12 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_1_5_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_1_5_g]
theorem cell12_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_1_5 hb hν
def cell12_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(93876854263519119/19061895313250000:ℝ)]]
theorem cell12_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 1 6) := by
 have heq : (-orderedLow cell12 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_1_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_1_6_g]
def cell12_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(741623342784976541309/771046040662837200:ℝ), (370702251223339391971/192761510165709300:ℝ), (30387630683371564775/30841841626513488:ℝ)]]
theorem cell12_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 1 6 ν := by
 have heq : mixedLowHigh cell12 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_1_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_1_6_g]
def cell12_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(23006344/25281:ℝ), (46087100/25281:ℝ), (23687500/25281:ℝ)]]
theorem cell12_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 6 false ν := by
 have heq : naturalFloor cell12 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_1_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_1_6_g]
def cell12_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(273917447384/315869241:ℝ), (549681523100/315869241:ℝ), (94448312500/105289747:ℝ)]]
theorem cell12_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 1 6 true ν := by
 have heq : naturalFloor cell12 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_1_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_1_6_g]
def cell12_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(23006344/25281:ℝ), (46087100/25281:ℝ), (23687500/25281:ℝ)]]
theorem cell12_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_1_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_1_6_g]
def cell12_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(124388331640625/639128961:ℝ), (235557277870000/639128961:ℝ), (109389290234375/639128961:ℝ)],
  ![(83300383058750/213042987:ℝ), (740886971074715000/999810737991:ℝ), (114859655508593750/333270245997:ℝ)],
  ![(125216208203125/639128961:ℝ), (1114500954753125000/2999432213973:ℝ), (519075294677734375/2999432213973:ℝ)]]
theorem cell12_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 1 6 b ν := by
 have heq : pairedCleared cell12 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_1_6_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_1_6_g]
theorem cell12_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_1_6 hb hν
def cell12_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(23087169982159171/19061895313250000:ℝ)]]
theorem cell12_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 2 1) := by
 have heq : (-orderedLow cell12 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_2_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_2_1_g]
def cell12_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(51899936504647408/214179455739677:ℝ), (923304253749542050/1927615101657093:ℝ), (463915285614343750/1927615101657093:ℝ)]]
theorem cell12_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 2 1 ν := by
 have heq : mixedLowHigh cell12 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_2_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_2_1_g]
def cell12_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(1604033/8427:ℝ), (9570350/25281:ℝ), (4859375/25281:ℝ)]]
theorem cell12_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 1 false ν := by
 have heq : naturalFloor cell12 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_2_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_2_1_g]
def cell12_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(1604033/8427:ℝ), (9570350/25281:ℝ), (4859375/25281:ℝ)]]
theorem cell12_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 1 true ν := by
 have heq : naturalFloor cell12 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_2_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_2_1_g]
def cell12_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(1604033/8427:ℝ), (9570350/25281:ℝ), (4859375/25281:ℝ)]]
theorem cell12_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_2_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_2_1_g]
def cell12_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(35727295703125/639128961:ℝ), (22745076808750/213042987:ℝ), (32211325390625/639128961:ℝ)],
  ![(77788331165000/639128961:ℝ), (77571570639245000/333270245997:ℝ), (330393844168750000/2999432213973:ℝ)],
  ![(41467816796875/639128961:ℝ), (124178964169531250/999810737991:ℝ), (176630762451171875/2999432213973:ℝ)]]
theorem cell12_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 2 1 b ν := by
 have heq : pairedCleared cell12 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_2_1_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_2_1_g]
theorem cell12_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_2_1 hb hν
def cell12_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(984995338412/381237906265:ℝ)]]
theorem cell12_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 2 2) := by
 have heq : (-orderedLow cell12 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_2_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_2_2_g]
def cell12_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(453004506416441948/642538367219031:ℝ), (933999457664814700/642538367219031:ℝ), (486135258186125000/642538367219031:ℝ)]]
theorem cell12_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 2 2 ν := by
 have heq : mixedLowHigh cell12 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_2_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_2_2_g]
def cell12_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(5370566/8427:ℝ), (11146900/8427:ℝ), (5843750/8427:ℝ)]]
theorem cell12_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 2 false ν := by
 have heq : naturalFloor cell12 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_2_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_2_2_g]
def cell12_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(624212001134/947607723:ℝ), (1292676858100/947607723:ℝ), (676045718750/947607723:ℝ)]]
theorem cell12_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 2 true ν := by
 have heq : naturalFloor cell12 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_2_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_2_2_g]
def cell12_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(5370566/8427:ℝ), (11146900/8427:ℝ), (5843750/8427:ℝ)]]
theorem cell12_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_2_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_2_2_g]
def cell12_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(95949851562500/639128961:ℝ), (194152732727500/639128961:ℝ), (97609662500000/639128961:ℝ)],
  ![(194152732727500/639128961:ℝ), (1839964046620940000/2999432213973:ℝ), (923425965076562500/2999432213973:ℝ)],
  ![(97609662500000/639128961:ℝ), (923425965076562500/2999432213973:ℝ), (462748487304687500/2999432213973:ℝ)]]
theorem cell12_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 2 2 b ν := by
 have heq : pairedCleared cell12 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_2_2_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_2_2_g]
theorem cell12_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_2_2 hb hν
def cell12_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(56731706452055829/19061895313250000:ℝ)]]
theorem cell12_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 2 3) := by
 have heq : (-orderedLow cell12 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_2_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_2_3_g]
def cell12_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(687787676943425972891/771046040662837200:ℝ), (358651444580705858029/192761510165709300:ℝ), (30242826154694060225/30841841626513488:ℝ)]]
theorem cell12_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 2 3 ν := by
 have heq : mixedLowHigh cell12 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_2_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_2_3_g]
def cell12_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(18301297/25281:ℝ), (38826050/25281:ℝ), (20828125/25281:ℝ)]]
theorem cell12_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 3 false ν := by
 have heq : naturalFloor cell12 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_2_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_2_3_g]
def cell12_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(696136127951/947607723:ℝ), (1474926382150/947607723:ℝ), (790161546875/947607723:ℝ)]]
theorem cell12_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 3 true ν := by
 have heq : naturalFloor cell12 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_2_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_2_3_g]
def cell12_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(18301297/25281:ℝ), (38826050/25281:ℝ), (20828125/25281:ℝ)]]
theorem cell12_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_2_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_2_3_g]
def cell12_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(13123901171875/71014329:ℝ), (8939208936250/23671443:ℝ), (13594855859375/71014329:ℝ)],
  ![(231805540540000/639128961:ℝ), (2221093240988675000/2999432213973:ℝ), (1125160878953125000/2999432213973:ℝ)],
  ![(113097211328125/639128961:ℝ), (1083017830613281250/2999432213973:ℝ), (548359620361328125/2999432213973:ℝ)]]
theorem cell12_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 2 3 b ν := by
 have heq : pairedCleared cell12 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_2_3_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_2_3_g]
theorem cell12_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_2_3 hb hν
def cell12_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(10952127506380421/4765473828312500:ℝ)]]
theorem cell12_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 2 4) := by
 have heq : (-orderedLow cell12 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_2_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_2_4_g]
def cell12_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(114701715329425451059/192761510165709300:ℝ), (64210734550886313221/48190377541427325:ℝ), (5809016281470846025/7710460406628372:ℝ)]]
theorem cell12_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 2 4 ν := by
 have heq : mixedLowHigh cell12 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_2_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_2_4_g]
def cell12_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(20490896/25281:ℝ), (44211400/25281:ℝ), (24125000/25281:ℝ)]]
theorem cell12_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 4 false ν := by
 have heq : naturalFloor cell12 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_2_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_2_4_g]
def cell12_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(20490896/25281:ℝ), (44211400/25281:ℝ), (24125000/25281:ℝ)]]
theorem cell12_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 4 true ν := by
 have heq : naturalFloor cell12 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_2_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_2_4_g]
def cell12_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(20490896/25281:ℝ), (44211400/25281:ℝ), (24125000/25281:ℝ)]]
theorem cell12_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_2_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_2_4_g]
def cell12_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(82387814843750/639128961:ℝ), (176702268580000/639128961:ℝ), (93128016406250/639128961:ℝ)],
  ![(62883584867500/213042987:ℝ), (623153058410470000/999810737991:ℝ), (108151396685937500/333270245997:ℝ)],
  ![(105669721093750/639128961:ℝ), (1034816121931250000/2999432213973:ℝ), (533717457519531250/2999432213973:ℝ)]]
theorem cell12_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 2 4 b ν := by
 have heq : pairedCleared cell12 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_2_4_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_2_4_g]
theorem cell12_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_2_4 hb hν
def cell12_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(57390256057217513/19061895313250000:ℝ)]]
theorem cell12_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 2 5) := by
 have heq : (-orderedLow cell12 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_2_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_2_5_g]
def cell12_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(66998792284599715503/85671782295870800:ℝ), (37254949498311855657/21417945573967700:ℝ), (3349377654182604925/3426871291834832:ℝ)]]
theorem cell12_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 2 5 ν := by
 have heq : mixedLowHigh cell12 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_2_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_2_5_g]
def cell12_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(2520055/2809:ℝ), (5510750/2809:ℝ), (3046875/2809:ℝ)]]
theorem cell12_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 5 false ν := by
 have heq : naturalFloor cell12 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_2_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_2_5_g]
def cell12_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(839984381585/947607723:ℝ), (1839425430250/947607723:ℝ), (1018393203125/947607723:ℝ)]]
theorem cell12_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 5 true ν := by
 have heq : naturalFloor cell12 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_2_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_2_5_g]
def cell12_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(2520055/2809:ℝ), (5510750/2809:ℝ), (3046875/2809:ℝ)]]
theorem cell12_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_2_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_2_5_g]
def cell12_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(11617008203125/71014329:ℝ), (74636059043750/213042987:ℝ), (39290685546875/213042987:ℝ)],
  ![(75434520805000/213042987:ℝ), (250065374399905000/333270245997:ℝ), (391699161350000000/999810737991:ℝ)],
  ![(40385756640625/213042987:ℝ), (398135995822656250/999810737991:ℝ), (7646031982421875/37030027333:ℝ)]]
theorem cell12_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 2 5 b ν := by
 have heq : pairedCleared cell12 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_2_5_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_2_5_g]
theorem cell12_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_2_5 hb hν
def cell12_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(35486001044456671/9530947656625000:ℝ)]]
theorem cell12_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 2 6) := by
 have heq : (-orderedLow cell12 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_2_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_2_6_g]
def cell12_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(373585699902546537409/385523020331418600:ℝ), (206873076383034074471/96380755082854650:ℝ), (18526366324701752275/15420920813256744:ℝ)]]
theorem cell12_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 2 6 ν := by
 have heq : mixedLowHigh cell12 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_2_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_2_6_g]
def cell12_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(24870094/25281:ℝ), (54982100/25281:ℝ), (30718750/25281:ℝ)]]
theorem cell12_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 6 false ν := by
 have heq : naturalFloor cell12 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_2_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_2_6_g]
def cell12_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(911908508402/947607723:ℝ), (2021674954300/947607723:ℝ), (1132509031250/947607723:ℝ)]]
theorem cell12_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 2 6 true ν := by
 have heq : naturalFloor cell12 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_2_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_2_6_g]
def cell12_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(24870094/25281:ℝ), (54982100/25281:ℝ), (30718750/25281:ℝ)]]
theorem cell12_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_2_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_2_6_g]
def cell12_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(126718332812500/639128961:ℝ), (271114085682500/639128961:ℝ), (142616096875000/639128961:ℝ)],
  ![(87985456742500/213042987:ℝ), (877239187988960000/999810737991:ℝ), (458944132642187500/999810737991:ℝ)],
  ![(136644818750000/639128961:ℝ), (1353999853004687500/2999432213973:ℝ), (704939723632812500/2999432213973:ℝ)]]
theorem cell12_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 2 6 b ν := by
 have heq : pairedCleared cell12 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_2_6_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_2_6_g]
theorem cell12_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_2_6 hb hν
def cell12_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(91158903776697/9530947656625000:ℝ)]]
theorem cell12_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 3 1) := by
 have heq : (-orderedLow cell12 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_3_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_3_1_g]
def cell12_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(112454644347539623/1285076734438062:ℝ), (683055726160892000/1927615101657093:ℝ), (1044168440092421875/3855230203314186:ℝ)]]
theorem cell12_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 3 1 ν := by
 have heq : mixedLowHigh cell12 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_3_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_3_1_g]
def cell12_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(1144033/8427:ℝ), (11315350/25281:ℝ), (7984375/25281:ℝ)]]
theorem cell12_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 1 false ν := by
 have heq : naturalFloor cell12 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_3_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_3_1_g]
def cell12_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(118496754317/947607723:ℝ), (404523714050/947607723:ℝ), (96605796875/315869241:ℝ)]]
theorem cell12_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 1 true ν := by
 have heq : naturalFloor cell12 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_3_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_3_1_g]
def cell12_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(498974/25281:ℝ), (5647850/25281:ℝ), (1750000/8427:ℝ)]]
theorem cell12_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_3_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_3_1_g]
def cell12_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (473215933750/12059037:ℝ), (467619531250/12059037:ℝ)],
  ![(27530311250/1339893:ℝ), (6537925848980000/56593060641:ℝ), (5324379914843750/56593060641:ℝ)],
  ![(25664843750/1339893:ℝ), (4164878938281250/56593060641:ℝ), (3056388671875000/56593060641:ℝ)]]
theorem cell12_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 3 1 b ν := by
 have heq : pairedCleared cell12 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_3_1_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_3_1_g]
theorem cell12_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_3_1 hb hν
def cell12_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(66773948755709171/19061895313250000:ℝ)]]
theorem cell12_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 3 2) := by
 have heq : (-orderedLow cell12 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_3_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_3_2_g]
def cell12_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(1593893561691900844/1927615101657093:ℝ), (1062856591249839700/642538367219031:ℝ), (1610097132870875000/1927615101657093:ℝ)]]
theorem cell12_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 3 2 ν := by
 have heq : mixedLowHigh cell12 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_3_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_3_2_g]
def cell12_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(18734198/25281:ℝ), (12541900/8427:ℝ), (19093750/25281:ℝ)]]
theorem cell12_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 2 false ν := by
 have heq : naturalFloor cell12 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_3_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_3_2_g]
def cell12_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(79151395126/105289747:ℝ), (1429933663100/947607723:ℝ), (725151968750/947607723:ℝ)]]
theorem cell12_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 2 true ν := by
 have heq : naturalFloor cell12 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_3_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_3_2_g]
def cell12_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(18734198/25281:ℝ), (12541900/8427:ℝ), (19093750/25281:ℝ)]]
theorem cell12_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_3_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_3_2_g]
def cell12_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(13123901171875/71014329:ℝ), (231805540540000/639128961:ℝ), (113097211328125/639128961:ℝ)],
  ![(8939208936250/23671443:ℝ), (2221093240988675000/2999432213973:ℝ), (1083017830613281250/2999432213973:ℝ)],
  ![(13594855859375/71014329:ℝ), (1125160878953125000/2999432213973:ℝ), (548359620361328125/2999432213973:ℝ)]]
theorem cell12_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 3 2 b ν := by
 have heq : pairedCleared cell12 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_3_2_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_3_2_g]
theorem cell12_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_3_2 hb hν
def cell12_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(1858730913883/381237906265:ℝ)]]
theorem cell12_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 3 3) := by
 have heq : (-orderedLow cell12 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_3_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_3_3_g]
def cell12_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(2485807652399400016/1927615101657093:ℝ), (5067263892994421150/1927615101657093:ℝ), (2604587621814906250/1927615101657093:ℝ)]]
theorem cell12_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 3 3 ν := by
 have heq : mixedLowHigh cell12 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_3_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_3_3_g]
def cell12_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(30033797/25281:ℝ), (61496050/25281:ℝ), (31765625/25281:ℝ)]]
theorem cell12_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 3 false ν := by
 have heq : naturalFloor cell12 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_3_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_3_3_g]
def cell12_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1156202650451/947607723:ℝ), (2363885092150/947607723:ℝ), (1219053734375/947607723:ℝ)]]
theorem cell12_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 3 true ν := by
 have heq : naturalFloor cell12 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_3_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_3_3_g]
def cell12_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(30033797/25281:ℝ), (61496050/25281:ℝ), (31765625/25281:ℝ)]]
theorem cell12_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_3_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_3_3_g]
def cell12_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(178337666406250/639128961:ℝ), (357723042841250/639128961:ℝ), (178495548437500/639128961:ℝ)],
  ![(357723042841250/639128961:ℝ), (3362913151856410000/2999432213973:ℝ), (1676049951521093750/2999432213973:ℝ)],
  ![(178495548437500/639128961:ℝ), (1676049951521093750/2999432213973:ℝ), (834477345214843750/2999432213973:ℝ)]]
theorem cell12_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 3 3 b ν := by
 have heq : pairedCleared cell12 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_3_3_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_3_3_g]
theorem cell12_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_3_3 hb hν
def cell12_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(100418485225605829/19061895313250000:ℝ)]]
theorem cell12_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 3 4) := by
 have heq : (-orderedLow cell12 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_3_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_3_4_g]
def cell12_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(379501776734485213897/257015346887612400:ℝ), (195059332193567854343/64253836721903100:ℝ), (16193911903599520075/10280613875504496:ℝ)]]
theorem cell12_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 3 4 ν := by
 have heq : mixedLowHigh cell12 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_3_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_3_4_g]
def cell12_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(10741132/8427:ℝ), (22293800/8427:ℝ), (11687500/8427:ℝ)]]
theorem cell12_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 4 false ν := by
 have heq : naturalFloor cell12 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_3_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_3_4_g]
def cell12_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(1228126777268/947607723:ℝ), (2546134616200/947607723:ℝ), (1333169562500/947607723:ℝ)]]
theorem cell12_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 4 true ν := by
 have heq : naturalFloor cell12 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_3_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_3_4_g]
def cell12_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(10741132/8427:ℝ), (22293800/8427:ℝ), (11687500/8427:ℝ)]]
theorem cell12_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_3_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_3_4_g]
def cell12_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(200502925390625/639128961:ℝ), (404928951392500/639128961:ℝ), (203239588671875/639128961:ℝ)],
  ![(395375850653750/639128961:ℝ), (3744042346224145000/2999432213973:ℝ), (1877784865397656250/2999432213973:ℝ)],
  ![(64661032421875/213042987:ℝ), (203960201895312500/333270245997:ℝ), (306696159423828125/999810737991:ℝ)]]
theorem cell12_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 3 4 b ν := by
 have heq : pairedCleared cell12 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_3_4_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_3_4_g]
theorem cell12_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_3_4 hb hν
def cell12_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(21873822199767921/4765473828312500:ℝ)]]
theorem cell12_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 3 5) := by
 have heq : (-orderedLow cell12 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_3_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_3_5_g]
def cell12_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(227381128644432868259/192761510165709300:ℝ), (120842372550885739471/48190377541427325:ℝ), (10393743670496971025/7710460406628372:ℝ)]]
theorem cell12_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 3 5 ν := by
 have heq : mixedLowHigh cell12 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_3_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_3_5_g]
def cell12_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(34412995/25281:ℝ), (72266750/25281:ℝ), (38359375/25281:ℝ)]]
theorem cell12_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 5 false ν := by
 have heq : naturalFloor cell12 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_3_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_3_5_g]
def cell12_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(1300050904085/947607723:ℝ), (2728384140250/947607723:ℝ), (1447285390625/947607723:ℝ)]]
theorem cell12_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 5 true ν := by
 have heq : naturalFloor cell12 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_3_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_3_5_g]
def cell12_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(34412995/25281:ℝ), (72266750/25281:ℝ), (38359375/25281:ℝ)]]
theorem cell12_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_3_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_3_5_g]
def cell12_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(164775629687500/639128961:ℝ), (340272578693750/639128961:ℝ), (174013902343750/639128961:ℝ)],
  ![(352221064716250/639128961:ℝ), (3392408280466880000/2999432213973:ℝ), (1725986556617968750/2999432213973:ℝ)],
  ![(20728400781250/71014329:ℝ), (595813369458593750/999810737991:ℝ), (301815438476562500/999810737991:ℝ)]]
theorem cell12_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 3 5 b ν := by
 have heq : pairedCleared cell12 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_3_5_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_3_5_g]
theorem cell12_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_3_5 hb hν
def cell12_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(101077034830767513/19061895313250000:ℝ)]]
theorem cell12_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 3 6) := by
 have heq : (-orderedLow cell12 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_3_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_3_6_g]
def cell12_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(1053706783821427108327/771046040662837200:ℝ), (561821097484804405913/192761510165709300:ℝ), (48483308443747944325/30841841626513488:ℝ)]]
theorem cell12_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 3 6 ν := by
 have heq : mixedLowHigh cell12 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_3_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_3_6_g]
def cell12_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(36602594/25281:ℝ), (77652100/25281:ℝ), (41656250/25281:ℝ)]]
theorem cell12_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 6 false ν := by
 have heq : naturalFloor cell12 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_3_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_3_6_g]
def cell12_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(36602594/25281:ℝ), (77652100/25281:ℝ), (41656250/25281:ℝ)]]
theorem cell12_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 3 6 true ν := by
 have heq : naturalFloor cell12 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_3_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_3_6_g]
def cell12_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(36602594/25281:ℝ), (77652100/25281:ℝ), (41656250/25281:ℝ)]]
theorem cell12_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_3_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_3_6_g]
def cell12_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(186940888671875/639128961:ℝ), (387478487245000/639128961:ℝ), (198757942578125/639128961:ℝ)],
  ![(389873872528750/639128961:ℝ), (3773537474834615000/2999432213973:ℝ), (1927721470494531250/2999432213973:ℝ)],
  ![(202043155859375/639128961:ℝ), (1947031973912500000/2999432213973:ℝ), (991057448486328125/2999432213973:ℝ)]]
theorem cell12_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 3 6 b ν := by
 have heq : pairedCleared cell12 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_3_6_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_3_6_g]
theorem cell12_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_3_6 hb hν
def cell12_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(6057470109881513/3812379062650000:ℝ)]]
theorem cell12_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 4 1) := by
 have heq : (-orderedLow cell12 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_4_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_4_1_g]
def cell12_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(622732821991335947/1927615101657093:ℝ), (1493117630332316950/1927615101657093:ℝ), (878095268747609375/1927615101657093:ℝ)]]
theorem cell12_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 4 1 ν := by
 have heq : mixedLowHigh cell12 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_4_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_4_1_g]
def cell12_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(11920849/25281:ℝ), (26835350/25281:ℝ), (15015625/25281:ℝ)]]
theorem cell12_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 1 false ν := by
 have heq : naturalFloor cell12 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_4_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_4_1_g]
def cell12_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(426531958067/947607723:ℝ), (966650324050/947607723:ℝ), (543908796875/947607723:ℝ)]]
theorem cell12_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 1 true ν := by
 have heq : naturalFloor cell12 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_4_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_4_1_g]
def cell12_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(6054599/25281:ℝ), (15500350/25281:ℝ), (9546875/25281:ℝ)]]
theorem cell12_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_4_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_4_1_g]
def cell12_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(22165258984375/639128961:ℝ), (62733252301250/639128961:ℝ), (40271383984375/639128961:ℝ)],
  ![(60337867017500/639128961:ℝ), (727639264363675000/2999432213973:ℝ), (441784001023437500/2999432213973:ℝ)],
  ![(36986170703125/639128961:ℝ), (422473497605468750/2999432213973:ℝ), (247599732666015625/2999432213973:ℝ)]]
theorem cell12_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 4 1 b ν := by
 have heq : pairedCleared cell12 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_4_1_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_4_1_g]
theorem cell12_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_4_1 hb hν
def cell12_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(21934548290551697/9530947656625000:ℝ)]]
theorem cell12_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 4 2) := by
 have heq : (-orderedLow cell12 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_4_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_4_2_g]
def cell12_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(2590952199342767213/3855230203314186:ℝ), (2948321246160869050/1927615101657093:ℝ), (1112177378201828125/1285076734438062:ℝ)]]
theorem cell12_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 4 2 ν := by
 have heq : mixedLowHigh cell12 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_4_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_4_2_g]
def cell12_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(17354198/25281:ℝ), (39370700/25281:ℝ), (2468750/2809:ℝ)]]
theorem cell12_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 2 false ν := by
 have heq : naturalFloor cell12 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_4_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_4_2_g]
def cell12_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(17354198/25281:ℝ), (39370700/25281:ℝ), (2468750/2809:ℝ)]]
theorem cell12_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 2 true ν := by
 have heq : naturalFloor cell12 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_4_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_4_2_g]
def cell12_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(49129469/75843:ℝ), (112444600/75843:ℝ), (63921875/75843:ℝ)]]
theorem cell12_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_4_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_4_2_g]
def cell12_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(82387814843750/639128961:ℝ), (62883584867500/213042987:ℝ), (105669721093750/639128961:ℝ)],
  ![(176702268580000/639128961:ℝ), (623153058410470000/999810737991:ℝ), (1034816121931250000/2999432213973:ℝ)],
  ![(93128016406250/639128961:ℝ), (108151396685937500/333270245997:ℝ), (533717457519531250/2999432213973:ℝ)]]
theorem cell12_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 4 2 b ν := by
 have heq : pairedCleared cell12 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_4_2_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_4_2_g]
theorem cell12_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_4_2 hb hν
def cell12_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(110460727529259171/19061895313250000:ℝ)]]
theorem cell12_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 4 3) := by
 have heq : (-orderedLow cell12 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_4_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_4_3_g]
def cell12_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(2720687694841975016/1927615101657093:ℝ), (5453835293749496150/1927615101657093:ℝ), (306253220014156250/214179455739677:ℝ)]]
theorem cell12_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 4 3 ν := by
 have heq : mixedLowHigh cell12 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_4_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_4_3_g]
def cell12_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(32656297/25281:ℝ), (65681050/25281:ℝ), (3703125/2809:ℝ)]]
theorem cell12_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 3 false ν := by
 have heq : naturalFloor cell12 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_4_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_4_3_g]
def cell12_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(7826120789/5959797:ℝ), (47191356550/17879391:ℝ), (23927546875/17879391:ℝ)]]
theorem cell12_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 3 true ν := by
 have heq : naturalFloor cell12 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_4_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_4_3_g]
def cell12_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(32656297/25281:ℝ), (65681050/25281:ℝ), (3703125/2809:ℝ)]]
theorem cell12_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_4_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_4_3_g]
def cell12_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(200502925390625/639128961:ℝ), (395375850653750/639128961:ℝ), (64661032421875/213042987:ℝ)],
  ![(404928951392500/639128961:ℝ), (3744042346224145000/2999432213973:ℝ), (203960201895312500/333270245997:ℝ)],
  ![(203239588671875/639128961:ℝ), (1877784865397656250/2999432213973:ℝ), (306696159423828125/999810737991:ℝ)]]
theorem cell12_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 4 3 b ν := by
 have heq : pairedCleared cell12 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_4_3_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_4_3_g]
theorem cell12_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_4_3 hb hν
def cell12_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(2732466489354/381237906265:ℝ)]]
theorem cell12_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 4 4) := by
 have heq : (-orderedLow cell12 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_4_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_4_4_g]
def cell12_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(3612601785549474188/1927615101657093:ℝ), (7332529412994398200/1927615101657093:ℝ), (3750769469071437500/1927615101657093:ℝ)]]
theorem cell12_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 4 4 ν := by
 have heq : mixedLowHigh cell12 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_4_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_4_4_g]
def cell12_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(43955896/25281:ℝ), (89551400/25281:ℝ), (46000000/25281:ℝ)]]
theorem cell12_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 4 false ν := by
 have heq : naturalFloor cell12 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_4_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_4_4_g]
def cell12_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(1688193299768/947607723:ℝ), (3435093326200/947607723:ℝ), (1762061750000/947607723:ℝ)]]
theorem cell12_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 4 true ν := by
 have heq : naturalFloor cell12 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_4_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_4_4_g]
def cell12_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(43955896/25281:ℝ), (89551400/25281:ℝ), (46000000/25281:ℝ)]]
theorem cell12_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_4_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_4_4_g]
def cell12_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(86908493750000/213042987:ℝ), (173764450985000/213042987:ℝ), (28820159375000/71014329:ℝ)],
  ![(173764450985000/213042987:ℝ), (542873584121320000/333270245997:ℝ), (809557979321875000/999810737991:ℝ)],
  ![(28820159375000/71014329:ℝ), (809557979321875000/999810737991:ℝ), (402068734375000000/999810737991:ℝ)]]
theorem cell12_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 4 4 b ν := by
 have heq : pairedCleared cell12 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_4_4_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_4_4_g]
theorem cell12_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_4_4 hb hν
def cell12_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(144105263999155829/19061895313250000:ℝ)]]
theorem cell12_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 4 5) := by
 have heq : (-orderedLow cell12 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_4_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_4_5_g]
def cell12_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(1589222983463485310491/771046040662837200:ℝ), (811704548580701268029/192761510165709300:ℝ), (66920645266903060225/30841841626513488:ℝ)]]
theorem cell12_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 4 5 ν := by
 have heq : mixedLowHigh cell12 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_4_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_4_5_g]
def cell12_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(46145495/25281:ℝ), (94936750/25281:ℝ), (49296875/25281:ℝ)]]
theorem cell12_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 5 false ν := by
 have heq : naturalFloor cell12 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_4_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_4_5_g]
def cell12_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(1760117426585/947607723:ℝ), (3617342850250/947607723:ℝ), (1876177578125/947607723:ℝ)]]
theorem cell12_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 5 true ν := by
 have heq : naturalFloor cell12 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_4_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_4_5_g]
def cell12_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(46145495/25281:ℝ), (94936750/25281:ℝ), (49296875/25281:ℝ)]]
theorem cell12_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_4_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_4_5_g]
def cell12_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(282890740234375/639128961:ℝ), (568499261506250/639128961:ℝ), (284125474609375/639128961:ℝ)],
  ![(186315386922500/213042987:ℝ), (1755663817153205000/999810737991:ℝ), (292267650204687500/333270245997:ℝ)],
  ![(274868983203125/639128961:ℝ), (2588265803502343750/2999432213973:ℝ), (1291817336181640625/2999432213973:ℝ)]]
theorem cell12_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 4 5 b ν := by
 have heq : pairedCleared cell12 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_4_5_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_4_5_g]
theorem cell12_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_4_5 hb hν
def cell12_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(32795516893155421/4765473828312500:ℝ)]]
theorem cell12_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 4 6) := by
 have heq : (-orderedLow cell12 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_4_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_4_6_g]
def cell12_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(113353513986480095153/64253836721903100:ℝ), (59158003516961721907/16063459180475775:ℝ), (4992823686507698675/2570153468876124:ℝ)]]
theorem cell12_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 4 6 ν := by
 have heq : mixedLowHigh cell12 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_4_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_4_6_g]
def cell12_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(5370566/2809:ℝ), (11146900/2809:ℝ), (5843750/2809:ℝ)]]
theorem cell12_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 6 false ν := by
 have heq : naturalFloor cell12 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_4_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_4_6_g]
def cell12_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(1832041553402/947607723:ℝ), (3799592374300/947607723:ℝ), (1990293406250/947607723:ℝ)]]
theorem cell12_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 4 6 true ν := by
 have heq : naturalFloor cell12 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_4_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_4_6_g]
def cell12_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(5370566/2809:ℝ), (11146900/2809:ℝ), (5843750/2809:ℝ)]]
theorem cell12_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_4_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_4_6_g]
def cell12_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(82387814843750/213042987:ℝ), (167947629602500/213042987:ℝ), (84966596093750/213042987:ℝ)],
  ![(515791374830000/639128961:ℝ), (4915357385702350000/2999432213973:ℝ), (2478610543062500000/2999432213973:ℝ)],
  ![(267441492968750/639128961:ℝ), (2540064094820312500/2999432213973:ℝ), (1277175173339843750/2999432213973:ℝ)]]
theorem cell12_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 4 6 b ν := by
 have heq : pairedCleared cell12 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_4_6_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_4_6_g]
theorem cell12_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_4_6 hb hν
def cell12_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(7549047911407717/2382736914156250:ℝ)]]
theorem cell12_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 5 1) := by
 have heq : (-orderedLow cell12 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_5_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_5_1_g]
def cell12_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(2153567354922724919/3855230203314186:ℝ), (767726511501247300/642538367219031:ℝ), (2468212634898015625/3855230203314186:ℝ)]]
theorem cell12_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 5 1 ν := by
 have heq : mixedLowHigh cell12 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_5_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_5_1_g]
def cell12_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(20409599/25281:ℝ), (4706150/2809:ℝ), (22046875/25281:ℝ)]]
theorem cell12_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 1 false ν := by
 have heq : naturalFloor cell12 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_5_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_5_1_g]
def cell12_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(734567161817/947607723:ℝ), (509592311350/315869241:ℝ), (798000203125/947607723:ℝ)]]
theorem cell12_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 1 true ν := by
 have heq : naturalFloor cell12 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_5_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_5_1_g]
def cell12_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(11610224/25281:ℝ), (8450950/8427:ℝ), (13843750/25281:ℝ)]]
theorem cell12_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_5_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_5_1_g]
def cell12_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(44330517968750/639128961:ℝ), (100386060113750/639128961:ℝ), (18586310937500/213042987:ℝ)],
  ![(107543775568750/639128961:ℝ), (1108768458731410000/2999432213973:ℝ), (22273180242968750/111090081999:ℝ)],
  ![(61730210937500/639128961:ℝ), (624208411482031250/2999432213973:ℝ), (111070288574218750/999810737991:ℝ)]]
theorem cell12_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 5 1 b ν := by
 have heq : pairedCleared cell12 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_5_1_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_5_1_g]
theorem cell12_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_5_1 hb hν
def cell12_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(14794825864591513/3812379062650000:ℝ)]]
theorem cell12_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 5 2) := by
 have heq : (-orderedLow cell12 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_5_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_5_2_g]
def cell12_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(583175651713803373/642538367219031:ℝ), (1252794383444098000/642538367219031:ℝ), (224919679556015625/214179455739677:ℝ)]]
theorem cell12_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 5 2 ν := by
 have heq : mixedLowHigh cell12 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_5_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_5_2_g]
def cell12_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(8614316/8427:ℝ), (18296900/8427:ℝ), (3250000/2809:ℝ)]]
theorem cell12_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 2 false ν := by
 have heq : naturalFloor cell12 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_5_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_5_2_g]
def cell12_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(958522607384/947607723:ℝ), (2037858558100/947607723:ℝ), (1086916812500/947607723:ℝ)]]
theorem cell12_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 2 true ν := by
 have heq : naturalFloor cell12 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_5_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_5_2_g]
def cell12_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(65796344/75843:ℝ), (142002100/75843:ℝ), (76812500/75843:ℝ)]]
theorem cell12_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_5_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_5_2_g]
def cell12_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(11617008203125/71014329:ℝ), (75434520805000/213042987:ℝ), (40385756640625/213042987:ℝ)],
  ![(74636059043750/213042987:ℝ), (250065374399905000/333270245997:ℝ), (398135995822656250/999810737991:ℝ)],
  ![(39290685546875/213042987:ℝ), (391699161350000000/999810737991:ℝ), (7646031982421875/37030027333:ℝ)]]
theorem cell12_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 5 2 b ν := by
 have heq : pairedCleared cell12 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_5_2_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_5_2_g]
theorem cell12_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_5_2 hb hν
def cell12_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(43777937677326697/9530947656625000:ℝ)]]
theorem cell12_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 5 3) := by
 have heq : (-orderedLow cell12 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_5_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_5_3_g]
def cell12_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(4844540465642915557/3855230203314186:ℝ), (1737862255386948700/642538367219031:ℝ), (5628895829118546875/3855230203314186:ℝ)]]
theorem cell12_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 5 3 ν := by
 have heq : mixedLowHigh cell12 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_5_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_5_3_g]
def cell12_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(31276297/25281:ℝ), (22475350/8427:ℝ), (36453125/25281:ℝ)]]
theorem cell12_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 3 false ν := by
 have heq : naturalFloor cell12 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_5_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_5_3_g]
def cell12_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(1182478052951/947607723:ℝ), (2546940182150/947607723:ℝ), (458611140625/315869241:ℝ)]]
theorem cell12_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 3 true ν := by
 have heq : naturalFloor cell12 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_5_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_5_3_g]
def cell12_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(31276297/25281:ℝ), (22475350/8427:ℝ), (36453125/25281:ℝ)]]
theorem cell12_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_5_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_5_3_g]
def cell12_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(164775629687500/639128961:ℝ), (352221064716250/639128961:ℝ), (20728400781250/71014329:ℝ)],
  ![(340272578693750/639128961:ℝ), (3392408280466880000/2999432213973:ℝ), (595813369458593750/999810737991:ℝ)],
  ![(174013902343750/639128961:ℝ), (1725986556617968750/2999432213973:ℝ), (301815438476562500/999810737991:ℝ)]]
theorem cell12_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 5 3 b ν := by
 have heq : pairedCleared cell12 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_5_3_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_5_3_g]
theorem cell12_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_5_3 hb hν
def cell12_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(154147506302809171/19061895313250000:ℝ)]]
theorem cell12_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 5 4) := by
 have heq : (-orderedLow cell12 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_5_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_5_4_g]
def cell12_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(1282493942664016396/642538367219031:ℝ), (7719100813749473200/1927615101657093:ℝ), (3902460827383937500/1927615101657093:ℝ)]]
theorem cell12_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 5 4 ν := by
 have heq : mixedLowHigh cell12 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_5_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_5_4_g]
def cell12_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(15526132/8427:ℝ), (93736400/25281:ℝ), (47562500/25281:ℝ)]]
theorem cell12_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 4 false ν := by
 have heq : naturalFloor cell12 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_5_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_5_4_g]
def cell12_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(592114618256/315869241:ℝ), (3572350131200/947607723:ℝ), (1811168000000/947607723:ℝ)]]
theorem cell12_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 4 true ν := by
 have heq : naturalFloor cell12 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_5_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_5_4_g]
def cell12_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(15526132/8427:ℝ), (93736400/25281:ℝ), (47562500/25281:ℝ)]]
theorem cell12_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_5_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_5_4_g]
def cell12_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(282890740234375/639128961:ℝ), (186315386922500/213042987:ℝ), (274868983203125/639128961:ℝ)],
  ![(568499261506250/639128961:ℝ), (1755663817153205000/999810737991:ℝ), (2588265803502343750/2999432213973:ℝ)],
  ![(284125474609375/639128961:ℝ), (292267650204687500/333270245997:ℝ), (1291817336181640625/2999432213973:ℝ)]]
theorem cell12_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 5 4 b ν := by
 have heq : pairedCleared cell12 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_5_4_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_5_4_g]
theorem cell12_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_5_4 hb hν
def cell12_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(721240412965/76247581253:ℝ)]]
theorem cell12_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 5 5) := by
 have heq : (-orderedLow cell12 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_5_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_5_5_g]
def cell12_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(526599546522172040/214179455739677:ℝ), (1066421659221597250/214179455739677:ℝ), (544105701814218750/214179455739677:ℝ)]]
theorem cell12_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 5 5 ν := by
 have heq : mixedLowHigh cell12 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_5_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_5_5_g]
def cell12_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(19292665/8427:ℝ), (39202250/8427:ℝ), (20078125/8427:ℝ)]]
theorem cell12_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 5 false ν := by
 have heq : naturalFloor cell12 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_5_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_5_5_g]
def cell12_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(2220183949085/947607723:ℝ), (4506301560250/947607723:ℝ), (2305069765625/947607723:ℝ)]]
theorem cell12_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 5 true ν := by
 have heq : naturalFloor cell12 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_5_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_5_5_g]
def cell12_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(19292665/8427:ℝ), (39202250/8427:ℝ), (20078125/8427:ℝ)]]
theorem cell12_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_5_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_5_5_g]
def cell12_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(343113296093750/639128961:ℝ), (684863663068750/639128961:ℝ), (340267320312500/639128961:ℝ)],
  ![(684863663068750/639128961:ℝ), (6408811362327350000/2999432213973:ℝ), (3181297924410156250/2999432213973:ℝ)],
  ![(340267320312500/639128961:ℝ), (3181297924410156250/2999432213973:ℝ), (1577935061035156250/2999432213973:ℝ)]]
theorem cell12_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 5 5 b ν := by
 have heq : pairedCleared cell12 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_5_5_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_5_5_g]
theorem cell12_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_5_5 hb hν
def cell12_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(187792042772705829/19061895313250000:ℝ)]]
theorem cell12_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 5 6) := by
 have heq : (-orderedLow cell12 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_5_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_5_6_g]
def cell12_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(2039940636723514979291/771046040662837200:ℝ), (1038231100580698973029/192761510165709300:ℝ), (85259554823007560225/30841841626513488:ℝ)]]
theorem cell12_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 5 6 ν := by
 have heq : mixedLowHigh cell12 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_5_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_5_6_g]
def cell12_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(60067594/25281:ℝ), (122992100/25281:ℝ), (63531250/25281:ℝ)]]
theorem cell12_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 6 false ν := by
 have heq : naturalFloor cell12 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_5_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_5_6_g]
def cell12_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(2292108075902/947607723:ℝ), (4688551084300/947607723:ℝ), (2419185593750/947607723:ℝ)]]
theorem cell12_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 5 6 true ν := by
 have heq : naturalFloor cell12 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_5_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_5_6_g]
def cell12_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(60067594/25281:ℝ), (122992100/25281:ℝ), (63531250/25281:ℝ)]]
theorem cell12_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_5_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_5_6_g]
def cell12_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(121759518359375/213042987:ℝ), (244023190540000/213042987:ℝ), (121670453515625/213042987:ℝ)],
  ![(722516470881250/639128961:ℝ), (6789940556695085000/2999432213973:ℝ), (3383032838286718750/2999432213973:ℝ)],
  ![(355754869140625/639128961:ℝ), (3340889789946875000/2999432213973:ℝ), (1663546194091796875/2999432213973:ℝ)]]
theorem cell12_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 5 6 b ν := by
 have heq : pairedCleared cell12 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_5_6_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_5_6_g]
theorem cell12_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_5_6 hb hν
def cell12_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(117002358491345881/19061895313250000:ℝ)]]
theorem cell12_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 6 1) := by
 have heq : (-orderedLow cell12 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_6_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_6_1_g]
def cell12_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(164249483006995898791/128507673443806200:ℝ), (245792128762969369087/96380755082854650:ℝ), (19678486324488618175/15420920813256744:ℝ)]]
theorem cell12_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 6 1 ν := by
 have heq : mixedLowHigh cell12 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_6_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_6_1_g]
def cell12_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(9632783/8427:ℝ), (57875350/25281:ℝ), (29078125/25281:ℝ)]]
theorem cell12_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 1 false ν := by
 have heq : naturalFloor cell12 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_6_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_6_1_g]
def cell12_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(1042602365567/947607723:ℝ), (2090903544050/947607723:ℝ), (350697203125/315869241:ℝ)]]
theorem cell12_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 1 true ν := by
 have heq : naturalFloor cell12 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_6_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_6_1_g]
def cell12_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(17165849/25281:ℝ), (35205350/25281:ℝ), (2015625/2809:ℝ)]]
theorem cell12_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_6_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_6_1_g]
def cell12_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(124388331640625/639128961:ℝ), (83300383058750/213042987:ℝ), (125216208203125/639128961:ℝ)],
  ![(235557277870000/639128961:ℝ), (740886971074715000/999810737991:ℝ), (1114500954753125000/2999432213973:ℝ)],
  ![(109389290234375/639128961:ℝ), (114859655508593750/333270245997:ℝ), (519075294677734375/2999432213973:ℝ)]]
theorem cell12_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 6 1 b ν := by
 have heq : pairedCleared cell12 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_6_1_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_6_1_g]
theorem cell12_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_6_1 hb hν
def cell12_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(13009895258101467/2382736914156250:ℝ)]]
theorem cell12_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 6 2) := by
 have heq : (-orderedLow cell12 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_6_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_6_2_g]
def cell12_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(4407155621222873263/3855230203314186:ℝ), (4568445054503718950/1927615101657093:ℝ), (1586858776470359375/1285076734438062:ℝ)]]
theorem cell12_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 6 2 ν := by
 have heq : mixedLowHigh cell12 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_6_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_6_2_g]
def cell12_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(34331698/25281:ℝ), (70410700/25281:ℝ), (4031250/2809:ℝ)]]
theorem cell12_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 2 false ν := by
 have heq : naturalFloor cell12 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_6_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_6_2_g]
def cell12_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(1266557811134/947607723:ℝ), (288887240900/105289747:ℝ), (1341008218750/947607723:ℝ)]]
theorem cell12_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 2 true ν := by
 have heq : naturalFloor cell12 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_6_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_6_2_g]
def cell12_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(82463219/75843:ℝ), (171559600/75843:ℝ), (89703125/75843:ℝ)]]
theorem cell12_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_6_2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_6_2_g]
def cell12_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(126718332812500/639128961:ℝ), (87985456742500/213042987:ℝ), (136644818750000/639128961:ℝ)],
  ![(271114085682500/639128961:ℝ), (877239187988960000/999810737991:ℝ), (1353999853004687500/2999432213973:ℝ)],
  ![(142616096875000/639128961:ℝ), (458944132642187500/999810737991:ℝ), (704939723632812500/2999432213973:ℝ)]]
theorem cell12_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 6 2 b ν := by
 have heq : pairedCleared cell12 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_6_2_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_6_2_g]
theorem cell12_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_6_2 hb hν
def cell12_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(23532181619301513/3812379062650000:ℝ)]]
theorem cell12_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 6 3) := by
 have heq : (-orderedLow cell12 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_6_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_6_3_g]
def cell12_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2876321088291484291/1927615101657093:ℝ), (6023648670332271050/1927615101657093:ℝ), (3170458963260671875/1927615101657093:ℝ)]]
theorem cell12_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 6 3 ν := by
 have heq : mixedLowHigh cell12 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_6_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_6_3_g]
def cell12_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(39765047/25281:ℝ), (82946050/25281:ℝ), (43484375/25281:ℝ)]]
theorem cell12_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 3 false ν := by
 have heq : naturalFloor cell12 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_6_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_6_3_g]
def cell12_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(39765047/25281:ℝ), (82946050/25281:ℝ), (43484375/25281:ℝ)]]
theorem cell12_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 3 true ν := by
 have heq : naturalFloor cell12 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_6_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_6_3_g]
def cell12_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(113428891/75843:ℝ), (237503150/75843:ℝ), (124984375/75843:ℝ)]]
theorem cell12_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_6_3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_6_3_g]
def cell12_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(186940888671875/639128961:ℝ), (389873872528750/639128961:ℝ), (202043155859375/639128961:ℝ)],
  ![(387478487245000/639128961:ℝ), (3773537474834615000/2999432213973:ℝ), (1947031973912500000/2999432213973:ℝ)],
  ![(198757942578125/639128961:ℝ), (1927721470494531250/2999432213973:ℝ), (991057448486328125/2999432213973:ℝ)]]
theorem cell12_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 6 3 b ν := by
 have heq : pairedCleared cell12 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_6_3_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_6_3_g]
theorem cell12_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_6_3 hb hν
def cell12_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(65621327064101697/9530947656625000:ℝ)]]
theorem cell12_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 6 4) := by
 have heq : (-orderedLow cell12 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_6_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_6_4_g]
def cell12_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(788680970215895989/428358911479354:ℝ), (7478852286160823150/1927615101657093:ℝ), (7921259523631609375/3855230203314186:ℝ)]]
theorem cell12_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 6 4 ν := by
 have heq : mixedLowHigh cell12 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_6_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_6_4_g]
def cell12_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(5022044/2809:ℝ), (95481400/25281:ℝ), (50687500/25281:ℝ)]]
theorem cell12_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 4 false ν := by
 have heq : naturalFloor cell12 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_6_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_6_4_g]
def cell12_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(1714468702268/947607723:ℝ), (3618148416200/947607723:ℝ), (639613812500/315869241:ℝ)]]
theorem cell12_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 4 true ν := by
 have heq : naturalFloor cell12 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_6_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_6_4_g]
def cell12_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(5022044/2809:ℝ), (95481400/25281:ℝ), (50687500/25281:ℝ)]]
theorem cell12_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_6_4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_6_4_g]
def cell12_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(82387814843750/213042987:ℝ), (515791374830000/639128961:ℝ), (267441492968750/639128961:ℝ)],
  ![(167947629602500/213042987:ℝ), (4915357385702350000/2999432213973:ℝ), (2540064094820312500/2999432213973:ℝ)],
  ![(84966596093750/213042987:ℝ), (2478610543062500000/2999432213973:ℝ), (1277175173339843750/2999432213973:ℝ)]]
theorem cell12_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 6 4 b ν := by
 have heq : pairedCleared cell12 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_6_4_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_6_4_g]
theorem cell12_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_6_4 hb hν
def cell12_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(197834285076359171/19061895313250000:ℝ)]]
theorem cell12_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 6 5) := by
 have heq : (-orderedLow cell12 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_6_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_6_5_g]
def cell12_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(4974275961142123360/1927615101657093:ℝ), (1109374037083272250/214179455739677:ℝ), (5048642674640468750/1927615101657093:ℝ)]]
theorem cell12_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 6 5 ν := by
 have heq : mixedLowHigh cell12 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_6_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_6_5_g]
def cell12_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(60500495/25281:ℝ), (40597250/8427:ℝ), (61796875/25281:ℝ)]]
theorem cell12_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 5 false ν := by
 have heq : naturalFloor cell12 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_6_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_6_5_g]
def cell12_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(256481611565/105289747:ℝ), (4643558365250/947607723:ℝ), (2354176015625/947607723:ℝ)]]
theorem cell12_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 5 true ν := by
 have heq : naturalFloor cell12 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_6_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_6_5_g]
def cell12_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(60500495/25281:ℝ), (40597250/8427:ℝ), (61796875/25281:ℝ)]]
theorem cell12_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_6_5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_6_5_g]
def cell12_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(121759518359375/213042987:ℝ), (722516470881250/639128961:ℝ), (355754869140625/639128961:ℝ)],
  ![(244023190540000/213042987:ℝ), (6789940556695085000/2999432213973:ℝ), (3340889789946875000/2999432213973:ℝ)],
  ![(121670453515625/213042987:ℝ), (3383032838286718750/2999432213973:ℝ), (1663546194091796875/2999432213973:ℝ)]]
theorem cell12_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 6 5 b ν := by
 have heq : pairedCleared cell12 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_6_5_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_6_5_g]
theorem cell12_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_6_5 hb hν
def cell12_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(4479937640296/381237906265:ℝ)]]
theorem cell12_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell12 6 6) := by
 have heq : (-orderedLow cell12 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell12_ordered_6_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordered_6_6_g]
def cell12_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(5866190051849622532/1927615101657093:ℝ), (11863060452994352300/1927615101657093:ℝ), (6043133163584500000/1927615101657093:ℝ)]]
theorem cell12_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell12 6 6 ν := by
 have heq : mixedLowHigh cell12 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_mixed_6_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_mixed_6_6_g]
def cell12_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(71800094/25281:ℝ), (145662100/25281:ℝ), (74468750/25281:ℝ)]]
theorem cell12_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 6 false ν := by
 have heq : naturalFloor cell12 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor0_6_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor0_6_6_g]
def cell12_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(2752174598402/947607723:ℝ), (5577509794300/947607723:ℝ), (2848077781250/947607723:ℝ)]]
theorem cell12_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell12 6 6 true ν := by
 have heq : naturalFloor cell12 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_floor1_6_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_floor1_6_6_g]
def cell12_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(71800094/25281:ℝ), (145662100/25281:ℝ), (74468750/25281:ℝ)]]
theorem cell12_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell12_complement_floor_6_6_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement_floor_6_6_g]
def cell12_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(425501110937500/639128961:ℝ), (848433973182500/639128961:ℝ), (421153206250000/639128961:ℝ)],
  ![(848433973182500/639128961:ℝ), (7931760467562820000/2999432213973:ℝ), (3933921910854687500/2999432213973:ℝ)],
  ![(421153206250000/639128961:ℝ), (3933921910854687500/2999432213973:ℝ), (1949663918945312500/2999432213973:ℝ)]]
theorem cell12_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell12 6 6 b ν := by
 have heq : pairedCleared cell12 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell12_paired_cleared_6_6_g (1557/2500:ℝ) (3/4:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_cleared_6_6_g]
theorem cell12_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell12 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell12_paired_cleared_6_6 hb hν
def cell12_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(12303684132199171/19061895313250000:ℝ)]]
theorem cell12_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell12.q/K)+1+17/50*(cell12.q/cell12.priorL)+17/25*(cell12.q/cell12.priorL)*cell12.priorB) := by
 have heq : ((2-17/50-17/25)*(cell12.q/K)+1+17/50*(cell12.q/cell12.priorL)+17/25*(cell12.q/cell12.priorL)*cell12.priorB) = Record12518109.Bernstein.bsum 0 0 (12303684132199171/19061895313250000:ℝ) cell12_increment0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_increment0_g]
def cell12_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(254507516863/508547750000:ℝ)]]
theorem cell12_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell12.q/cell12.priorL)*(1-cell12.priorB)) := by
 have heq : (1+17/25*(cell12.q/cell12.priorL)*(1-cell12.priorB)) = Record12518109.Bernstein.bsum 0 0 (254507516863/508547750000:ℝ) cell12_increment1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_increment1_g]
def cell12_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(1017796425589/2034191000000:ℝ)]]
theorem cell12_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell12.q/cell12.priorL)*(1-cell12.priorB)) := by
 have heq : (1+omega*(cell12.q/cell12.priorL)*(1-cell12.priorB)) = Record12518109.Bernstein.bsum 0 0 (1017796425589/2034191000000:ℝ) cell12_increment2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_increment2_g]
def cell12_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(4839023/50562:ℝ), (4785175/25281:ℝ), (548175/5618:ℝ)]]
theorem cell12_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (191407/125000:ℝ) cell12_high_increment_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_high_increment_g]
def cell12_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(31885355171/5359572:ℝ), (345137491037/5359572:ℝ), (625873715737/5359572:ℝ), (293134176079/5359572:ℝ)]]
theorem cell12_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (95656065513/7812500000:ℝ) cell12_three_gate0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_three_gate0_g]
def cell12_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(2189599/50562:ℝ), (3195751/25281:ℝ), (4404151/50562:ℝ)]]
theorem cell12_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (2189599/3125000:ℝ) cell12_three_gate1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_three_gate1_g]
def cell12_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(170888649109/1895215446:ℝ), (56519313175/315869241:ℝ), (175808091725/1895215446:ℝ)]]
theorem cell12_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell12.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell12.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (6782317581/4685375000:ℝ) cell12_three_gate2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_three_gate2_g]
def cell12_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(35753/74966:ℝ)]]
theorem cell12_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (1-cell12.q/K/3) := by
 have heq : (1-cell12.q/K/3) = Record12518109.Bernstein.bsum 0 0 (35753/74966:ℝ) cell12_paired_margin0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_margin0_g]
def cell12_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(486169/5866250:ℝ)]]
theorem cell12_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (gamma cell12-13/50) := by
 have heq : (gamma cell12-13/50) = Record12518109.Bernstein.bsum 0 0 (486169/5866250:ℝ) cell12_paired_margin1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_margin1_g]
def cell12_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(3699/37544:ℝ)]]
theorem cell12_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (cell12.q-gamma cell12) := by
 have heq : (cell12.q-gamma cell12) = Record12518109.Bernstein.bsum 0 0 (3699/37544:ℝ) cell12_paired_margin2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_margin2_g]
def cell12_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(50094743/164255000:ℝ)]]
theorem cell12_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < (min (cell12.q+rho cell12.q) (3/4+rho (3/4))-gamma cell12) := by
 have heq : (min (cell12.q+rho cell12.q) (3/4+rho (3/4))-gamma cell12) = Record12518109.Bernstein.bsum 0 0 (50094743/164255000:ℝ) cell12_paired_margin3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_paired_margin3_g]
theorem cell12_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (1557/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell12 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell12_paired_1_1 hb hν
 · exact cell12_paired_1_2 hb hν
 · exact cell12_paired_1_3 hb hν
 · exact cell12_paired_1_4 hb hν
 · exact cell12_paired_1_5 hb hν
 · exact cell12_paired_1_6 hb hν
 · exact cell12_paired_2_1 hb hν
 · exact cell12_paired_2_2 hb hν
 · exact cell12_paired_2_3 hb hν
 · exact cell12_paired_2_4 hb hν
 · exact cell12_paired_2_5 hb hν
 · exact cell12_paired_2_6 hb hν
 · exact cell12_paired_3_1 hb hν
 · exact cell12_paired_3_2 hb hν
 · exact cell12_paired_3_3 hb hν
 · exact cell12_paired_3_4 hb hν
 · exact cell12_paired_3_5 hb hν
 · exact cell12_paired_3_6 hb hν
 · exact cell12_paired_4_1 hb hν
 · exact cell12_paired_4_2 hb hν
 · exact cell12_paired_4_3 hb hν
 · exact cell12_paired_4_4 hb hν
 · exact cell12_paired_4_5 hb hν
 · exact cell12_paired_4_6 hb hν
 · exact cell12_paired_5_1 hb hν
 · exact cell12_paired_5_2 hb hν
 · exact cell12_paired_5_3 hb hν
 · exact cell12_paired_5_4 hb hν
 · exact cell12_paired_5_5 hb hν
 · exact cell12_paired_5_6 hb hν
 · exact cell12_paired_6_1 hb hν
 · exact cell12_paired_6_2 hb hν
 · exact cell12_paired_6_3 hb hν
 · exact cell12_paired_6_4 hb hν
 · exact cell12_paired_6_5 hb hν
 · exact cell12_paired_6_6 hb hν
end
end Record12518109Admission
