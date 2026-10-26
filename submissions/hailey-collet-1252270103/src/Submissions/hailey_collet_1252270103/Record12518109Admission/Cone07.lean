/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Cell07
import Submissions.hailey_collet_1252270103.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell7_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(113403496331/381237906265:ℝ)]]
theorem cell7_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 1 1) := by
 have heq : (-orderedLow cell7 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_1_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_1_1_g]
def cell7_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(417287732332607/2744912925108:ℝ), (1900797694248725/5489825850216:ℝ), (1088181532984375/5489825850216:ℝ)]]
theorem cell7_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 1 1 ν := by
 have heq : mixedLowHigh cell7 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_1_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_1_1_g]
def cell7_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/20736:ℝ), (2749675/10368:ℝ), (3296875/20736:ℝ)]]
theorem cell7_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 1 false ν := by
 have heq : naturalFloor cell7 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_1_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_1_1_g]
def cell7_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(287827168631/2331742464:ℝ), (339080091575/1165871232:ℝ), (399659984375/2331742464:ℝ)]]
theorem cell7_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 1 true ν := by
 have heq : naturalFloor cell7 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_1_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_1_1_g]
def cell7_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/20736:ℝ), (2749675/10368:ℝ), (3296875/20736:ℝ)]]
theorem cell7_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_1_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_1_1_g]
def cell7_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(6209440234375/214990848:ℝ), (6996144589375/107495424:ℝ), (7661983984375/214990848:ℝ)],
  ![(6996144589375/107495424:ℝ), (36037240873380625/250625581056:ℝ), (38905270772265625/501251162112:ℝ)],
  ![(7661983984375/214990848:ℝ), (38905270772265625/501251162112:ℝ), (41553926025390625/1002502324224:ℝ)]]
theorem cell7_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 1 1 b ν := by
 have heq : pairedCleared cell7 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_1_1_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_1_1_g]
theorem cell7_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_1_1 hb hν
def cell7_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(13171399417850739/19061895313250000:ℝ)]]
theorem cell7_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 1 2) := by
 have heq : (-orderedLow cell7 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_1_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_1_2_g]
def cell7_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(242487932425742693471/632427937944883200:ℝ), (267623339222599788623/316213968972441600:ℝ), (11912726780920637975/25297117517795328:ℝ)]]
theorem cell7_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 1 2 ν := by
 have heq : mixedLowHigh cell7 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_1_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_1_2_g]
def cell7_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/10368:ℝ), (2749675/5184:ℝ), (3296875/10368:ℝ)]]
theorem cell7_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 2 false ν := by
 have heq : naturalFloor cell7 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_1_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_1_2_g]
def cell7_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/10368:ℝ), (2749675/5184:ℝ), (3296875/10368:ℝ)]]
theorem cell7_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 2 true ν := by
 have heq : naturalFloor cell7 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_1_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_1_2_g]
def cell7_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/10368:ℝ), (2749675/5184:ℝ), (3296875/10368:ℝ)]]
theorem cell7_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_1_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_1_2_g]
def cell7_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(33331342578125/429981696:ℝ), (36215866248125/214990848:ℝ), (38616930078125/429981696:ℝ)],
  ![(31915195038125/214990848:ℝ), (161911420273266875/501251162112:ℝ), (172817531066796875/1002502324224:ℝ)],
  ![(30257317578125/429981696:ℝ), (153855878723046875/1002502324224:ℝ), (164506748779296875/2005004648448:ℝ)]]
theorem cell7_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 1 2 b ν := by
 have heq : pairedCleared cell7 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_1_2_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_1_2_g]
theorem cell7_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_1_2 hb hν
def cell7_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(95293400523011/4765473828312500:ℝ)]]
theorem cell7_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 1 3) := by
 have heq : (-orderedLow cell7 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_1_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_1_3_g]
def cell7_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(4911369576487737979/158106984486220800:ℝ), (16993615307161147627/79053492243110400:ℝ), (1238925794066768275/6324279379448832:ℝ)]]
theorem cell7_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 1 3 ν := by
 have heq : mixedLowHigh cell7 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_1_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_1_3_g]
def cell7_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/6912:ℝ), (2749675/3456:ℝ), (3296875/6912:ℝ)]]
theorem cell7_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 3 false ν := by
 have heq : naturalFloor cell7 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_1_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_1_3_g]
def cell7_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(740145155893/2331742464:ℝ), (897712724725/1165871232:ℝ), (1083261203125/2331742464:ℝ)]]
theorem cell7_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 3 true ν := by
 have heq : naturalFloor cell7 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_1_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_1_3_g]
def cell7_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/6912:ℝ), (2749675/3456:ℝ), (3296875/6912:ℝ)]]
theorem cell7_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_1_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_1_3_g]
def cell7_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (13589730625/497664:ℝ), (12750390625/497664:ℝ)],
  ![(236081691875/4478976:ℝ), (404890274958125/2610683136:ℝ), (2069999676171875/20885465088:ℝ)],
  ![(233563671875/4478976:ℝ), (2646044109765625/20885465088:ℝ), (380971923828125/5221366272:ℝ)]]
theorem cell7_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 1 3 b ν := by
 have heq : pairedCleared cell7 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_1_3_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_1_3_g]
theorem cell7_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_1_3 hb hν
def cell7_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(13982204703632783/19061895313250000:ℝ)]]
theorem cell7_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 1 4) := by
 have heq : (-orderedLow cell7 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_1_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_1_4_g]
def cell7_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(55330105734086997529/210809312648294400:ℝ), (75370617754172606377/105404656324147200:ℝ), (3951363151065237025/8432372505931776:ℝ)]]
theorem cell7_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 1 4 ν := by
 have heq : mixedLowHigh cell7 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_1_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_1_4_g]
def cell7_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/5184:ℝ), (2749675/2592:ℝ), (3296875/5184:ℝ)]]
theorem cell7_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 4 false ν := by
 have heq : naturalFloor cell7 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_1_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_1_4_g]
def cell7_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(241576037381/582935616:ℝ), (294257260325/291467808:ℝ), (356265453125/582935616:ℝ)]]
theorem cell7_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 4 true ν := by
 have heq : naturalFloor cell7 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_1_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_1_4_g]
def cell7_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/5184:ℝ), (2749675/2592:ℝ), (3296875/5184:ℝ)]]
theorem cell7_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_1_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_1_4_g]
def cell7_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(6970820703125/143327232:ℝ), (9364780233125/71663616:ℝ), (11436433203125/143327232:ℝ)],
  ![(9751609023125/71663616:ℝ), (55858623772821875/167083720704:ℝ), (64788991326171875/334167441408:ℝ)],
  ![(12451820703125/143327232:ℝ), (67685151482421875/334167441408:ℝ), (75897371826171875/668334882816:ℝ)]]
theorem cell7_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 1 4 b ν := by
 have heq : pairedCleared cell7 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_1_4_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_1_4_g]
theorem cell7_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_1_4 hb hν
def cell7_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(13791617902586761/9530947656625000:ℝ)]]
theorem cell7_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 1 5) := by
 have heq : (-orderedLow cell7 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_1_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_1_5_g]
def cell7_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(156167578049285516629/316213968972441600:ℝ), (192124622648195523877/158106984486220800:ℝ), (9376237865062174525/12648558758897664:ℝ)]]
theorem cell7_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 1 5 ν := by
 have heq : mixedLowHigh cell7 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_1_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_1_5_g]
def cell7_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(11427095/20736:ℝ), (13748375/10368:ℝ), (16484375/20736:ℝ)]]
theorem cell7_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 5 false ν := by
 have heq : naturalFloor cell7 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_1_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_1_5_g]
def cell7_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(132495904795/259082496:ℝ), (161816150875/129541248:ℝ), (196318046875/259082496:ℝ)]]
theorem cell7_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 5 true ν := by
 have heq : naturalFloor cell7 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_1_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_1_5_g]
def cell7_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(11427095/20736:ℝ), (13748375/10368:ℝ), (16484375/20736:ℝ)]]
theorem cell7_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_1_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_1_5_g]
def cell7_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(6970820703125/71663616:ℝ), (8386319628125/35831808:ℝ), (9600376953125/71663616:ℝ)],
  ![(7862955488125/35831808:ℝ), (42902134974161875/83541860352:ℝ), (48228993916796875/167083720704:ℝ)],
  ![(968311328125/7962624:ℝ), (15505599534765625/55694573568:ℝ), (17171722900390625/111389147136:ℝ)]]
theorem cell7_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 1 5 b ν := by
 have heq : pairedCleared cell7 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_1_5_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_1_5_g]
theorem cell7_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_1_5 hb hν
def cell7_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(93966780741313129/19061895313250000:ℝ)]]
theorem cell7_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 1 6) := by
 have heq : (-orderedLow cell7 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_1_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_1_6_g]
def cell7_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(27500430229969391627/23423256960921600:ℝ), (82652318976812975153/35134885441382400:ℝ), (3379592870596165225/2810790835310592:ℝ)]]
theorem cell7_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 1 6 ν := by
 have heq : mixedLowHigh cell7 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_1_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_1_6_g]
def cell7_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(5754691/5184:ℝ), (5776075/2592:ℝ), (5921875/5184:ℝ)]]
theorem cell7_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 6 false ν := by
 have heq : naturalFloor cell7 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_1_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_1_6_g]
def cell7_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(616275160759/582935616:ℝ), (619631970175/291467808:ℝ), (636979234375/582935616:ℝ)]]
theorem cell7_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 1 6 true ν := by
 have heq : naturalFloor cell7 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_1_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_1_6_g]
def cell7_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(5754691/5184:ℝ), (5776075/2592:ℝ), (5921875/5184:ℝ)]]
theorem cell7_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_1_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_1_6_g]
def cell7_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(116981191015625/429981696:ℝ), (111047674525625/214990848:ℝ), (103663778515625/429981696:ℝ)],
  ![(117669318475625/214990848:ℝ), (521259174379289375/501251162112:ℝ), (487272051655859375/1002502324224:ℝ)],
  ![(118115716015625/429981696:ℝ), (523610664937109375/1002502324224:ℝ), (490102335693359375/2005004648448:ℝ)]]
theorem cell7_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 1 6 b ν := by
 have heq : pairedCleared cell7 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_1_6_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_1_6_g]
theorem cell7_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_1_6 hb hν
def cell7_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(23282258251314261/19061895313250000:ℝ)]]
theorem cell7_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 2 1) := by
 have heq : (-orderedLow cell7 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_2_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_2_1_g]
def cell7_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(58507291631025829/197633730607776:ℝ), (57965559253680175/98816865303888:ℝ), (58214361798765625/197633730607776:ℝ)]]
theorem cell7_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 2 1 ν := by
 have heq : mixedLowHigh cell7 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_2_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_2_1_g]
def cell7_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(4807919/20736:ℝ), (4792175/10368:ℝ), (4859375/20736:ℝ)]]
theorem cell7_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 1 false ν := by
 have heq : naturalFloor cell7 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_2_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_2_1_g]
def cell7_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(4807919/20736:ℝ), (4792175/10368:ℝ), (4859375/20736:ℝ)]]
theorem cell7_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 1 true ν := by
 have heq : naturalFloor cell7 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_2_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_2_1_g]
def cell7_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(4807919/20736:ℝ), (4792175/10368:ℝ), (4859375/20736:ℝ)]]
theorem cell7_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_2_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_2_1_g]
def cell7_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(33331342578125/429981696:ℝ), (31915195038125/214990848:ℝ), (30257317578125/429981696:ℝ)],
  ![(36215866248125/214990848:ℝ), (161911420273266875/501251162112:ℝ), (153855878723046875/1002502324224:ℝ)],
  ![(38616930078125/429981696:ℝ), (172817531066796875/1002502324224:ℝ), (164506748779296875/2005004648448:ℝ)]]
theorem cell7_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 2 1 b ν := by
 have heq : pairedCleared cell7 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_2_1_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_2_1_g]
theorem cell7_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_2_1 hb hν
def cell7_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(989282805192/381237906265:ℝ)]]
theorem cell7_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 2 2) := by
 have heq : (-orderedLow cell7 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_2_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_2_2_g]
def cell7_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(342392911526002691/395267461215552:ℝ), (352209196287350075/197633730607776:ℝ), (365187620738421875/395267461215552:ℝ)]]
theorem cell7_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 2 2 ν := by
 have heq : mixedLowHigh cell7 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_2_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_2_2_g]
def cell7_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(2704723/3456:ℝ), (2799475/1728:ℝ), (2921875/3456:ℝ)]]
theorem cell7_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 2 false ν := by
 have heq : naturalFloor cell7 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_2_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_2_2_g]
def cell7_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(943264277381/1165871232:ℝ), (974276380325/582935616:ℝ), (1014615453125/1165871232:ℝ)]]
theorem cell7_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 2 true ν := by
 have heq : naturalFloor cell7 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_2_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_2_2_g]
def cell7_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(2704723/3456:ℝ), (2799475/1728:ℝ), (2921875/3456:ℝ)]]
theorem cell7_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_2_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_2_2_g]
def cell7_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(2577400390625/11943936:ℝ), (2606524485625/5971968:ℝ), (874073046875/3981312:ℝ)],
  ![(2606524485625/5971968:ℝ), (4090060030698125/4641214464:ℝ), (12325448868359375/27847286784:ℝ)],
  ![(874073046875/3981312:ℝ), (12325448868359375/27847286784:ℝ), (12364736083984375/55694573568:ℝ)]]
theorem cell7_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 2 2 b ν := by
 have heq : pairedCleared cell7 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_2_2_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_2_2_g]
theorem cell7_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_2_2 hb hν
def cell7_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(56965364860900739/19061895313250000:ℝ)]]
theorem cell7_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 2 3) := by
 have heq : (-orderedLow cell7 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_2_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_2_3_g]
def cell7_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(694173497337914346271/632427937944883200:ℝ), (721672106093633348623/316213968972441600:ℝ), (30270394004187637975/25297117517795328:ℝ)]]
theorem cell7_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 2 3 ν := by
 have heq : mixedLowHigh cell7 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_2_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_2_3_g]
def cell7_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(18513757/20736:ℝ), (19546525/10368:ℝ), (20828125/20736:ℝ)]]
theorem cell7_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 3 false ν := by
 have heq : naturalFloor cell7 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_2_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_2_3_g]
def cell7_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(2112687548393/2331742464:ℝ), (2227869077225/1165871232:ℝ), (2371031515625/2331742464:ℝ)]]
theorem cell7_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 3 true ν := by
 have heq : naturalFloor cell7 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_2_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_2_3_g]
def cell7_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(18513757/20736:ℝ), (19546525/10368:ℝ), (20828125/20736:ℝ)]]
theorem cell7_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_2_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_2_3_g]
def cell7_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(37899625390625/143327232:ℝ), (38686152850625/71663616:ℝ), (39230950390625/143327232:ℝ)],
  ![(12417531926875/23887872:ℝ), (59062602426878125/55694573568:ℝ), (59858127642578125/111389147136:ℝ)],
  ![(36444412890625/143327232:ℝ), (173253832146484375/334167441408:ℝ), (175509798583984375/668334882816:ℝ)]]
theorem cell7_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 2 3 b ν := by
 have heq : pairedCleared cell7 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_2_3_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_2_3_g]
theorem cell7_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_2_3 hb hν
def cell7_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(11043784761285511/4765473828312500:ℝ)]]
theorem cell7_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 2 4) := by
 have heq : (-orderedLow cell7 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_2_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_2_4_g]
def cell7_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(39277586934843550393/52702328162073600:ℝ), (43501935674973179209/26351164081036800:ℝ), (1942780866627839425/2108093126482944:ℝ)]]
theorem cell7_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 2 4 ν := by
 have heq : mixedLowHigh cell7 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_2_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_2_4_g]
def cell7_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(2599897/2592:ℝ), (2787025/1296:ℝ), (3015625/2592:ℝ)]]
theorem cell7_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 4 false ν := by
 have heq : naturalFloor cell7 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_2_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_2_4_g]
def cell7_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(2599897/2592:ℝ), (2787025/1296:ℝ), (3015625/2592:ℝ)]]
theorem cell7_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 4 true ν := by
 have heq : naturalFloor cell7 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_2_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_2_4_g]
def cell7_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(2599897/2592:ℝ), (2787025/1296:ℝ), (3015625/2592:ℝ)]]
theorem cell7_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_2_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_2_4_g]
def cell7_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(40183766796875/214990848:ℝ), (42856677966875/107495424:ℝ), (45046129296875/214990848:ℝ)],
  ![(45587256756875/107495424:ℝ), (223695467180298125/250625581056:ℝ), (232632801086328125/501251162112:ℝ)],
  ![(50749016796875/214990848:ℝ), (246457867492578125/501251162112:ℝ), (254157932861328125/1002502324224:ℝ)]]
theorem cell7_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 2 4 b ν := by
 have heq : pairedCleared cell7 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_2_4_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_2_4_g]
theorem cell7_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_2_4 hb hν
def cell7_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(57776170146682783/19061895313250000:ℝ)]]
theorem cell7_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 2 5) := by
 have heq : (-orderedLow cell7 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_2_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_2_5_g]
def cell7_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(617675882114432645387/632427937944883200:ℝ), (680160620133551379131/316213968972441600:ℝ), (30211756676462711075/25297117517795328:ℝ)]]
theorem cell7_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 2 5 ν := by
 have heq : mixedLowHigh cell7 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_2_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_2_5_g]
def cell7_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(284995/256:ℝ), (927625/384:ℝ), (1015625/768:ℝ)]]
theorem cell7_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 5 false ν := by
 have heq : naturalFloor cell7 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_2_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_2_5_g]
def cell7_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(2565005535655/2331742464:ℝ), (2786501710375/1165871232:ℝ), (3054632734375/2331742464:ℝ)]]
theorem cell7_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 5 true ν := by
 have heq : naturalFloor cell7 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_2_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_2_5_g]
def cell7_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(284995/256:ℝ), (927625/384:ℝ), (1015625/768:ℝ)]]
theorem cell7_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_2_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_2_5_g]
def cell7_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(101279995703125/429981696:ℝ), (107936933003125/214990848:ℝ), (113385220703125/429981696:ℝ)],
  ![(109097419373125/214990848:ℝ), (537227872887101875/501251162112:ℝ), (560272591694921875/1002502324224:ℝ)],
  ![(116431383203125/429981696:ℝ), (568961072163671875/1002502324224:ℝ), (589714762451171875/2005004648448:ℝ)]]
theorem cell7_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 2 5 b ν := by
 have heq : pairedCleared cell7 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_2_5_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_2_5_g]
theorem cell7_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_2_5 hb hν
def cell7_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(35688600624111761/9530947656625000:ℝ)]]
theorem cell7_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 2 6) := by
 have heq : (-orderedLow cell7 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_2_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_2_6_g]
def cell7_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(382010360505371343029/316213968972441600:ℝ), (419149006083712303877/158106984486220800:ℝ), (18555071476695674525/12648558758897664:ℝ)]]
theorem cell7_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 2 6 ν := by
 have heq : mixedLowHigh cell7 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_2_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_2_6_g]
def cell7_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(12685007/10368:ℝ), (13897775/5184:ℝ), (15359375/10368:ℝ)]]
theorem cell7_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 6 false ν := by
 have heq : naturalFloor cell7 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_2_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_2_6_g]
def cell7_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1395582264643/1165871232:ℝ), (1532909013475/582935616:ℝ), (1698216671875/1165871232:ℝ)]]
theorem cell7_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 2 6 true ν := by
 have heq : naturalFloor cell7 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_2_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_2_6_g]
def cell7_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(12685007/10368:ℝ), (13897775/5184:ℝ), (15359375/10368:ℝ)]]
theorem cell7_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_2_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_2_6_g]
def cell7_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(30548114453125/107495424:ℝ), (32540127518125/53747712:ℝ), (34169545703125/107495424:ℝ)],
  ![(31755081308125/53747712:ℝ), (156766202853401875/125312790528:ℝ), (163819895304296875/250625581056:ℝ)],
  ![(32841183203125/107495424:ℝ), (161251602335546875/250625581056:ℝ), (167778414794921875/501251162112:ℝ)]]
theorem cell7_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 2 6 b ν := by
 have heq : pairedCleared cell7 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_2_6_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_2_6_g]
theorem cell7_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_2_6 hb hν
def cell7_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(346339379112327/9530947656625000:ℝ)]]
theorem cell7_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 3 1) := by
 have heq : (-orderedLow cell7 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_3_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_3_1_g]
def cell7_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(135966428639352013/1054046563241472:ℝ), (240712148993232125/527023281620736:ℝ), (38852672844453125/117116284804608:ℝ)]]
theorem cell7_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 3 1 ν := by
 have heq : mixedLowHigh cell7 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_3_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_3_1_g]
def cell7_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(3852919/20736:ℝ), (5877175/10368:ℝ), (7984375/20736:ℝ)]]
theorem cell7_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 1 false ν := by
 have heq : naturalFloor cell7 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_3_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_3_1_g]
def cell7_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(402422801131/2331742464:ℝ), (631000564075/1165871232:ℝ), (868905296875/2331742464:ℝ)]]
theorem cell7_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 1 true ν := by
 have heq : naturalFloor cell7 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_3_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_3_1_g]
def cell7_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(19553/432:ℝ), (2650/9:ℝ), (109375/432:ℝ)]]
theorem cell7_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_3_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_3_1_g]
def cell7_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (236081691875/4478976:ℝ), (233563671875/4478976:ℝ)],
  ![(13589730625/497664:ℝ), (404890274958125/2610683136:ℝ), (2646044109765625/20885465088:ℝ)],
  ![(12750390625/497664:ℝ), (2069999676171875/20885465088:ℝ), (380971923828125/5221366272:ℝ)]]
theorem cell7_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 3 1 b ν := by
 have heq : pairedCleared cell7 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_3_1_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_3_1_g]
theorem cell7_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_3_1 hb hν
def cell7_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(67076223694364261/19061895313250000:ℝ)]]
theorem cell7_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 3 2) := by
 have heq : (-orderedLow cell7 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_3_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_3_2_g]
def cell7_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(399318061332158941/395267461215552:ℝ), (399711597801756325/197633730607776:ℝ), (403267273961078125/395267461215552:ℝ)]]
theorem cell7_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 3 2 ν := by
 have heq : mixedLowHigh cell7 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_3_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_3_2_g]
def cell7_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(9375419/10368:ℝ), (9419675/5184:ℝ), (9546875/10368:ℝ)]]
theorem cell7_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 2 false ν := by
 have heq : naturalFloor cell7 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_3_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_3_2_g]
def cell7_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(1069673534881/1165871232:ℝ), (1074173977825/582935616:ℝ), (1088001390625/1165871232:ℝ)]]
theorem cell7_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 2 true ν := by
 have heq : naturalFloor cell7 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_3_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_3_2_g]
def cell7_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(9375419/10368:ℝ), (9419675/5184:ℝ), (9546875/10368:ℝ)]]
theorem cell7_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_3_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_3_2_g]
def cell7_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(37899625390625/143327232:ℝ), (12417531926875/23887872:ℝ), (36444412890625/143327232:ℝ)],
  ![(38686152850625/71663616:ℝ), (59062602426878125/55694573568:ℝ), (173253832146484375/334167441408:ℝ)],
  ![(39230950390625/143327232:ℝ), (59858127642578125/111389147136:ℝ), (175509798583984375/668334882816:ℝ)]]
theorem cell7_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 3 2 b ν := by
 have heq : pairedCleared cell7 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_3_2_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_3_2_g]
theorem cell7_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_3_2 hb hν
def cell7_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(1865162114053/381237906265:ℝ)]]
theorem cell7_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 3 3) := by
 have heq : (-orderedLow cell7 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_3_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_3_3_g]
def cell7_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(312348194798054987/197633730607776:ℝ), (317994837790873025/98816865303888:ℝ), (326013085550984375/197633730607776:ℝ)]]
theorem cell7_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 3 3 ν := by
 have heq : mixedLowHigh cell7 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_3_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_3_3_g]
def cell7_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(30171257/20736:ℝ), (30844025/10368:ℝ), (31765625/20736:ℝ)]]
theorem cell7_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 3 false ν := by
 have heq : naturalFloor cell7 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_3_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_3_3_g]
def cell7_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1161743313631/777247488:ℝ), (1186008476575/388623744:ℝ), (1219600609375/777247488:ℝ)]]
theorem cell7_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 3 true ν := by
 have heq : naturalFloor cell7 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_3_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_3_3_g]
def cell7_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(30171257/20736:ℝ), (30844025/10368:ℝ), (31765625/20736:ℝ)]]
theorem cell7_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_3_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_3_3_g]
def cell7_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(86576973828125/214990848:ℝ), (86838736893125/107495424:ℝ), (86737905078125/214990848:ℝ)],
  ![(86838736893125/107495424:ℝ), (405689242442016875/250625581056:ℝ), (404810888488671875/501251162112:ℝ)],
  ![(86737905078125/214990848:ℝ), (404810888488671875/501251162112:ℝ), (403576572998046875/1002502324224:ℝ)]]
theorem cell7_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 3 3 b ν := by
 have heq : pairedCleared cell7 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_3_3_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_3_3_g]
theorem cell7_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_3_3 hb hν
def cell7_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(100759330303950739/19061895313250000:ℝ)]]
theorem cell7_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 3 4) := by
 have heq : (-orderedLow cell7 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_3_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_3_4_g]
def cell7_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(381953020750028666357/210809312648294400:ℝ), (391906957654888969541/105404656324147200:ℝ), (16209353742484879325/8432372505931776:ℝ)]]
theorem cell7_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 3 4 ν := by
 have heq : mixedLowHigh cell7 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_3_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_3_4_g]
def cell7_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2704723/1728:ℝ), (2799475/864:ℝ), (2921875/1728:ℝ)]]
theorem cell7_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 4 false ν := by
 have heq : naturalFloor cell7 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_3_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_3_4_g]
def cell7_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(927847233631/582935616:ℝ), (959335436575/291467808:ℝ), (1000150609375/582935616:ℝ)]]
theorem cell7_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 4 true ν := by
 have heq : naturalFloor cell7 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_3_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_3_4_g]
def cell7_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2704723/1728:ℝ), (2799475/864:ℝ), (2921875/1728:ℝ)]]
theorem cell7_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_3_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_3_4_g]
def cell7_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(194066409765625/429981696:ℝ), (195901050855625/214990848:ℝ), (196768772265625/429981696:ℝ)],
  ![(191600379645625/214990848:ℝ), (901215423410539375/501251162112:ℝ), (904628766499609375/1002502324224:ℝ)],
  ![(188409159765625/429981696:ℝ), (885667114155859375/1002502324224:ℝ), (888552042724609375/2005004648448:ℝ)]]
theorem cell7_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 3 4 b ν := by
 have heq : pairedCleared cell7 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_3_4_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_3_4_g]
theorem cell7_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_3_4 hb hν
def cell7_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(21992276122048011/4765473828312500:ℝ)]]
theorem cell7_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 3 5) := by
 have heq : (-orderedLow cell7 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_3_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_3_5_g]
def cell7_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(230754152032573564379/158106984486220800:ℝ), (244017998742677927627/79053492243110400:ℝ), (10417759405700268275/6324279379448832:ℝ)]]
theorem cell7_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 3 5 ν := by
 have heq : mixedLowHigh cell7 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_3_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_3_5_g]
def cell7_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(34742095/20736:ℝ), (36343375/10368:ℝ), (38359375/20736:ℝ)]]
theorem cell7_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 5 false ν := by
 have heq : naturalFloor cell7 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_3_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_3_5_g]
def cell7_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(3937547928155/2331742464:ℝ), (4116658062875/1165871232:ℝ), (4342403046875/2331742464:ℝ)]]
theorem cell7_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 5 true ν := by
 have heq : naturalFloor cell7 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_3_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_3_5_g]
def cell7_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(34742095/20736:ℝ), (36343375/10368:ℝ), (38359375/20736:ℝ)]]
theorem cell7_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_3_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_3_5_g]
def cell7_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(40183766796875/107495424:ℝ), (41388987059375/53747712:ℝ), (42292044921875/107495424:ℝ)],
  ![(42754276454375/53747712:ℝ), (204260733982308125/125312790528:ℝ), (207792804972265625/250625581056:ℝ)],
  ![(45143488671875/107495424:ℝ), (214705338175390625/250625581056:ℝ), (217584628173828125/501251162112:ℝ)]]
theorem cell7_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 3 5 b ν := by
 have heq : pairedCleared cell7 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_3_5_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_3_5_g]
theorem cell7_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_3_5 hb hν
def cell7_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(101570135589732783/19061895313250000:ℝ)]]
theorem cell7_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 3 6) := by
 have heq : (-orderedLow cell7 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_3_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_3_6_g]
def cell7_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(1069361447026604298187/632427937944883200:ℝ), (1134209387004584939131/316213968972441600:ℝ), (48569423899729711075/25297117517795328:ℝ)]]
theorem cell7_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 3 6 ν := by
 have heq : mixedLowHigh cell7 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_3_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_3_6_g]
def cell7_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(18513757/10368:ℝ), (19546525/5184:ℝ), (20828125/10368:ℝ)]]
theorem cell7_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 6 false ν := by
 have heq : naturalFloor cell7 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_3_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_3_6_g]
def cell7_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(18513757/10368:ℝ), (19546525/5184:ℝ), (20828125/10368:ℝ)]]
theorem cell7_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 3 6 true ν := by
 have heq : naturalFloor cell7 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_3_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_3_6_g]
def cell7_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(18513757/10368:ℝ), (19546525/5184:ℝ), (20828125/10368:ℝ)]]
theorem cell7_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_3_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_3_6_g]
def cell7_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(181647529296875/429981696:ℝ), (187779525306875/214990848:ℝ), (192461141796875/429981696:ℝ)],
  ![(188940011676875/214990848:ℝ), (906879874455738125/501251162112:ℝ), (926178209411328125/1002502324224:ℝ)],
  ![(195507304296875/429981696:ℝ), (934866689880078125/1002502324224:ℝ), (951737409423828125/2005004648448:ℝ)]]
theorem cell7_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 3 6 b ν := by
 have heq : pairedCleared cell7 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_3_6_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_3_6_g]
theorem cell7_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_3_6 hb hν
def cell7_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(6177122619946783/3812379062650000:ℝ)]]
theorem cell7_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 4 1) := by
 have heq : (-orderedLow cell7 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_4_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_4_1_g]
def cell7_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(216473335301860219/527023281620736:ℝ), (254040852200962075/263511640810368:ℝ), (293716462226546875/527023281620736:ℝ)]]
theorem cell7_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 4 1 ν := by
 have heq : mixedLowHigh cell7 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_4_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_4_1_g]
def cell7_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(12204169/20736:ℝ), (13568425/10368:ℝ), (15015625/20736:ℝ)]]
theorem cell7_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 1 false ν := by
 have heq : naturalFloor cell7 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_4_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_4_1_g]
def cell7_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(1310678424881/2331742464:ℝ), (1465992047825/1165871232:ℝ), (1630632640625/2331742464:ℝ)]]
theorem cell7_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 1 true ν := by
 have heq : naturalFloor cell7 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_4_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_4_1_g]
def cell7_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(6375419/20736:ℝ), (7919675/10368:ℝ), (9546875/20736:ℝ)]]
theorem cell7_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_4_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_4_1_g]
def cell7_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(6970820703125/143327232:ℝ), (9751609023125/71663616:ℝ), (12451820703125/143327232:ℝ)],
  ![(9364780233125/71663616:ℝ), (55858623772821875/167083720704:ℝ), (67685151482421875/334167441408:ℝ)],
  ![(11436433203125/143327232:ℝ), (64788991326171875/334167441408:ℝ), (75897371826171875/668334882816:ℝ)]]
theorem cell7_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 4 1 b ν := by
 have heq : pairedCleared cell7 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_4_1_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_4_1_g]
theorem cell7_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_4_1 hb hν
def cell7_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(22243322100637327/9530947656625000:ℝ)]]
theorem cell7_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 4 2) := by
 have heq : (-orderedLow cell7 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_4_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_4_2_g]
def cell7_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(2666327110478914303/3162139689724416:ℝ), (2992380281334864175/1581069844862208:ℝ), (3343730569708609375/3162139689724416:ℝ)]]
theorem cell7_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 4 2 ν := by
 have heq : mixedLowHigh cell7 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_4_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_4_2_g]
def cell7_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(2965973/3456:ℝ), (3320725/1728:ℝ), (1234375/1152:ℝ)]]
theorem cell7_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 2 false ν := by
 have heq : naturalFloor cell7 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_4_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_4_2_g]
def cell7_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(2965973/3456:ℝ), (3320725/1728:ℝ), (1234375/1152:ℝ)]]
theorem cell7_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 2 true ν := by
 have heq : naturalFloor cell7 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_4_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_4_2_g]
def cell7_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(50473139/62208:ℝ), (56948675/31104:ℝ), (63921875/62208:ℝ)]]
theorem cell7_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_4_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_4_2_g]
def cell7_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(40183766796875/214990848:ℝ), (45587256756875/107495424:ℝ), (50749016796875/214990848:ℝ)],
  ![(42856677966875/107495424:ℝ), (223695467180298125/250625581056:ℝ), (246457867492578125/501251162112:ℝ)],
  ![(45046129296875/214990848:ℝ), (232632801086328125/501251162112:ℝ), (254157932861328125/1002502324224:ℝ)]]
theorem cell7_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 4 2 b ν := by
 have heq : pairedCleared cell7 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_4_2_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_4_2_g]
theorem cell7_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_4_2 hb hν
def cell7_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(110870189137414261/19061895313250000:ℝ)]]
theorem cell7_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 4 3) := by
 have heq : (-orderedLow cell7 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_4_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_4_3_g]
def cell7_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(14200448737547213/8234738775324:ℝ), (18985891030448675/5489825850216:ℝ), (28754409346859375/16469477550648:ℝ)]]
theorem cell7_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 4 3 ν := by
 have heq : mixedLowHigh cell7 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_4_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_4_3_g]
def cell7_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(10897919/6912:ℝ), (10962175/3456:ℝ), (1234375/768:ℝ)]]
theorem cell7_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 3 false ν := by
 have heq : naturalFloor cell7 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_4_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_4_3_g]
def cell7_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(3738048455893/2331742464:ℝ), (3757820624725/1165871232:ℝ), (3805573703125/2331742464:ℝ)]]
theorem cell7_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 3 true ν := by
 have heq : naturalFloor cell7 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_4_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_4_3_g]
def cell7_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(10897919/6912:ℝ), (10962175/3456:ℝ), (1234375/768:ℝ)]]
theorem cell7_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_4_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_4_3_g]
def cell7_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(194066409765625/429981696:ℝ), (191600379645625/214990848:ℝ), (188409159765625/429981696:ℝ)],
  ![(195901050855625/214990848:ℝ), (901215423410539375/501251162112:ℝ), (885667114155859375/1002502324224:ℝ)],
  ![(196768772265625/429981696:ℝ), (904628766499609375/1002502324224:ℝ), (888552042724609375/2005004648448:ℝ)]]
theorem cell7_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 4 3 b ν := by
 have heq : pairedCleared cell7 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_4_3_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_4_3_g]
theorem cell7_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_4_3 hb hν
def cell7_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(2741041422914/381237906265:ℝ)]]
theorem cell7_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 4 4) := by
 have heq : (-orderedLow cell7 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_4_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_4_4_g]
def cell7_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(302333289222072419/131755820405184:ℝ), (306590051625380675/65877910202592:ℝ), (312954907155171875/131755820405184:ℝ)]]
theorem cell7_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 4 4 ν := by
 have heq : mixedLowHigh cell7 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_4_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_4_4_g]
def cell7_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(172321/81:ℝ), (701425/162:ℝ), (359375/162:ℝ)]]
theorem cell7_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 4 false ν := by
 have heq : naturalFloor cell7 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_4_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_4_4_g]
def cell7_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(317745707939/145733904:ℝ), (322968631175/72866952:ℝ), (330523296875/145733904:ℝ)]]
theorem cell7_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 4 true ν := by
 have heq : naturalFloor cell7 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_4_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_4_4_g]
def cell7_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(172321/81:ℝ), (701425/162:ℝ), (359375/162:ℝ)]]
theorem cell7_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_4_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_4_4_g]
def cell7_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(15845092578125/26873856:ℝ), (15845004130625/13436928:ℝ), (15784483203125/26873856:ℝ)],
  ![(15845004130625/13436928:ℝ), (73814405403291875/31328197632:ℝ), (73470462168359375/62656395264:ℝ)],
  ![(15784483203125/26873856:ℝ), (73470462168359375/62656395264:ℝ), (73073487060546875/125312790528:ℝ)]]
theorem cell7_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 4 4 b ν := by
 have heq : pairedCleared cell7 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_4_4_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_4_4_g]
theorem cell7_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_4_4 hb hν
def cell7_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(144553295747000739/19061895313250000:ℝ)]]
theorem cell7_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 4 5) := by
 have heq : (-orderedLow cell7 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_4_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_4_5_g]
def cell7_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(1597544627162257651871/632427937944883200:ℝ), (1629769639835700468623/316213968972441600:ℝ), (66985728450721637975/25297117517795328:ℝ)]]
theorem cell7_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 4 5 ν := by
 have heq : mixedLowHigh cell7 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_4_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_4_5_g]
def cell7_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(46399595/20736:ℝ), (47640875/10368:ℝ), (49296875/20736:ℝ)]]
theorem cell7_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 5 false ν := by
 have heq : naturalFloor cell7 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_4_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_4_5_g]
def cell7_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(1770030106885/777247488:ℝ), (1815604805125/388623744:ℝ), (1876724453125/777247488:ℝ)]]
theorem cell7_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 5 true ν := by
 have heq : naturalFloor cell7 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_4_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_4_5_g]
def cell7_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(46399595/20736:ℝ), (47640875/10368:ℝ), (49296875/20736:ℝ)]]
theorem cell7_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_4_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_4_5_g]
def cell7_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(274433943359375/429981696:ℝ), (275743643159375/214990848:ℝ), (275844693359375/429981696:ℝ)],
  ![(271442971949375/214990848:ℝ), (1270867424979175625/501251162112:ℝ), (1270534384216015625/1002502324224:ℝ)],
  ![(267485080859375/429981696:ℝ), (1251572731872265625/1002502324224:ℝ), (1250574689697265625/2005004648448:ℝ)]]
theorem cell7_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 4 5 b ν := by
 have heq : pairedCleared cell7 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_4_5_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_4_5_g]
theorem cell7_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_4_5 hb hν
def cell7_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(32940767482810511/4765473828312500:ℝ)]]
theorem cell7_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 4 6) := by
 have heq : (-orderedLow cell7 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_4_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_4_6_g]
def cell7_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(343675543260616477579/158106984486220800:ℝ), (357530190460436317627/79053492243110400:ℝ), (15007176211517018275/6324279379448832:ℝ)]]
theorem cell7_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 4 6 ν := by
 have heq : mixedLowHigh cell7 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_4_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_4_6_g]
def cell7_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(2704723/1152:ℝ), (2799475/576:ℝ), (2921875/1152:ℝ)]]
theorem cell7_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 6 false ν := by
 have heq : naturalFloor cell7 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_4_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_4_6_g]
def cell7_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(2768124657143/1165871232:ℝ), (2863065365975/582935616:ℝ), (2985986984375/1165871232:ℝ)]]
theorem cell7_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 4 6 true ν := by
 have heq : naturalFloor cell7 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_4_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_4_6_g]
def cell7_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(2704723/1152:ℝ), (2799475/576:ℝ), (2921875/1152:ℝ)]]
theorem cell7_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_4_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_4_6_g]
def cell7_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(40183766796875/71663616:ℝ), (40899756756875/35831808:ℝ), (41374016796875/71663616:ℝ)],
  ![(13936649895625/11943936:ℝ), (65927496527659375/27847286784:ℝ), (66504268755859375/55694573568:ℝ)],
  ![(43274979296875/71663616:ℝ), (204121161736328125/167083720704:ℝ), (205393526611328125/334167441408:ℝ)]]
theorem cell7_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 4 6 b ν := by
 have heq : pairedCleared cell7 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_4_6_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_4_6_g]
theorem cell7_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_4_6 hb hν
def cell7_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(7634818430155397/2382736914156250:ℝ)]]
theorem cell7_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 5 1) := by
 have heq : (-orderedLow cell7 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_5_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_5_1_g]
def cell7_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(81102990285343207/117116284804608:ℝ), (775451259810616175/527023281620736:ℝ), (825191793306109375/1054046563241472:ℝ)]]
theorem cell7_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 5 1 ν := by
 have heq : mixedLowHigh cell7 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_5_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_5_1_g]
def cell7_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(20555419/20736:ℝ), (21259675/10368:ℝ), (22046875/20736:ℝ)]]
theorem cell7_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 1 false ν := by
 have heq : naturalFloor cell7 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_5_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_5_1_g]
def cell7_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(739644682877/777247488:ℝ), (766994510525/388623744:ℝ), (797453328125/777247488:ℝ)]]
theorem cell7_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 1 true ν := by
 have heq : naturalFloor cell7 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_5_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_5_1_g]
def cell7_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(5906147/10368:ℝ), (6393275/5184:ℝ), (6921875/10368:ℝ)]]
theorem cell7_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_5_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_5_1_g]
def cell7_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(6970820703125/71663616:ℝ), (7862955488125/35831808:ℝ), (968311328125/7962624:ℝ)],
  ![(8386319628125/35831808:ℝ), (42902134974161875/83541860352:ℝ), (15505599534765625/55694573568:ℝ)],
  ![(9600376953125/71663616:ℝ), (48228993916796875/167083720704:ℝ), (17171722900390625/111389147136:ℝ)]]
theorem cell7_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 5 1 b ν := by
 have heq : pairedCleared cell7 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_5_1_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_5_1_g]
theorem cell7_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_5_1 hb hν
def cell7_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(14935915708556783/3812379062650000:ℝ)]]
theorem cell7_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 5 2) := by
 have heq : (-orderedLow cell7 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_5_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_5_2_g]
def cell7_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1778633918186009789/1581069844862208:ℝ), (1897244473780470125/790534922431104:ℝ), (2028503588133828125/1581069844862208:ℝ)]]
theorem cell7_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 5 2 ν := by
 have heq : mixedLowHigh cell7 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_5_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_5_2_g]
def cell7_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(181577/144:ℝ), (63925/24:ℝ), (203125/144:ℝ)]]
theorem cell7_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 2 false ν := by
 have heq : naturalFloor cell7 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_5_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_5_2_g]
def cell7_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(727344952753/582935616:ℝ), (768866179225/291467808:ℝ), (815050890625/582935616:ℝ)]]
theorem cell7_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 2 true ν := by
 have heq : naturalFloor cell7 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_5_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_5_2_g]
def cell7_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(16695941/15552:ℝ), (17887325/7776:ℝ), (19203125/15552:ℝ)]]
theorem cell7_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_5_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_5_2_g]
def cell7_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(101279995703125/429981696:ℝ), (109097419373125/214990848:ℝ), (116431383203125/429981696:ℝ)],
  ![(107936933003125/214990848:ℝ), (537227872887101875/501251162112:ℝ), (568961072163671875/1002502324224:ℝ)],
  ![(113385220703125/429981696:ℝ), (560272591694921875/1002502324224:ℝ), (589714762451171875/2005004648448:ℝ)]]
theorem cell7_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 5 2 b ν := by
 have heq : pairedCleared cell7 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_5_2_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_5_2_g]
theorem cell7_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_5_2 hb hν
def cell7_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(44140304822162327/9530947656625000:ℝ)]]
theorem cell7_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 5 3) := by
 have heq : (-orderedLow cell7 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_5_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_5_3_g]
def cell7_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(4924754935039772567/3162139689724416:ℝ), (5262624115690031975/1581069844862208:ℝ), (5638438972616984375/3162139689724416:ℝ)]]
theorem cell7_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 5 3 ν := by
 have heq : mixedLowHigh cell7 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_5_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_5_3_g]
def cell7_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(31738757/20736:ℝ), (33971525/10368:ℝ), (36453125/20736:ℝ)]]
theorem cell7_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 3 false ν := by
 have heq : naturalFloor cell7 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_5_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_5_3_g]
def cell7_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(3599825573393/2331742464:ℝ), (3849945902225/1165871232:ℝ), (4128047140625/2331742464:ℝ)]]
theorem cell7_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 3 true ν := by
 have heq : naturalFloor cell7 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_5_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_5_3_g]
def cell7_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(31738757/20736:ℝ), (33971525/10368:ℝ), (36453125/20736:ℝ)]]
theorem cell7_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_5_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_5_3_g]
def cell7_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(40183766796875/107495424:ℝ), (42754276454375/53747712:ℝ), (45143488671875/107495424:ℝ)],
  ![(41388987059375/53747712:ℝ), (204260733982308125/125312790528:ℝ), (214705338175390625/250625581056:ℝ)],
  ![(42292044921875/107495424:ℝ), (207792804972265625/250625581056:ℝ), (217584628173828125/501251162112:ℝ)]]
theorem cell7_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 5 3 b ν := by
 have heq : pairedCleared cell7 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_5_3_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_5_3_g]
theorem cell7_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_5_3 hb hν
def cell7_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(154664154580464261/19061895313250000:ℝ)]]
theorem cell7_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 5 4) := by
 have heq : (-orderedLow cell7 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_5_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_5_4_g]
def cell7_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(963925017472373507/395267461215552:ℝ), (967272556390548275/197633730607776:ℝ), (976944374688171875/395267461215552:ℝ)]]
theorem cell7_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 5 4 ν := by
 have heq : mixedLowHigh cell7 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_5_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_5_4_g]
def cell7_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(11659169/5184:ℝ), (11733425/2592:ℝ), (11890625/5184:ℝ)]]
theorem cell7_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 4 false ν := by
 have heq : naturalFloor cell7 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_5_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_5_4_g]
def cell7_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(222364576751/97155936:ℝ), (223637220575/48577968:ℝ), (226464359375/97155936:ℝ)]]
theorem cell7_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 4 true ν := by
 have heq : naturalFloor cell7 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_5_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_5_4_g]
def cell7_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(11659169/5184:ℝ), (11733425/2592:ℝ), (11890625/5184:ℝ)]]
theorem cell7_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_5_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_5_4_g]
def cell7_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(274433943359375/429981696:ℝ), (271442971949375/214990848:ℝ), (267485080859375/429981696:ℝ)],
  ![(275743643159375/214990848:ℝ), (1270867424979175625/501251162112:ℝ), (1251572731872265625/1002502324224:ℝ)],
  ![(275844693359375/429981696:ℝ), (1270534384216015625/1002502324224:ℝ), (1250574689697265625/2005004648448:ℝ)]]
theorem cell7_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 5 4 b ν := by
 have heq : pairedCleared cell7 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_5_4_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_5_4_g]
theorem cell7_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_5_4 hb hν
def cell7_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(723384146355/76247581253:ℝ)]]
theorem cell7_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 5 5) := by
 have heq : (-orderedLow cell7 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_5_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_5_5_g]
def cell7_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(297325836434081135/98816865303888:ℝ), (75221914635658625/12352108162986:ℝ), (306425817957265625/98816865303888:ℝ)]]
theorem cell7_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 5 5 ν := by
 have heq : mixedLowHigh cell7 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_5_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_5_5_g]
def cell7_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(19352365/6912:ℝ), (19646125/3456:ℝ), (20078125/6912:ℝ)]]
theorem cell7_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 5 false ν := by
 have heq : naturalFloor cell7 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_5_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_5_5_g]
def cell7_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(6682632713155/2331742464:ℝ), (6776970767875/1165871232:ℝ), (6917943671875/2331742464:ℝ)]]
theorem cell7_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 5 true ν := by
 have heq : naturalFloor cell7 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_5_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_5_5_g]
def cell7_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(19352365/6912:ℝ), (19646125/3456:ℝ), (20078125/6912:ℝ)]]
theorem cell7_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_5_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_5_5_g]
def cell7_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(55648169140625/71663616:ℝ), (55560443065625/35831808:ℝ), (55271275390625/71663616:ℝ)],
  ![(55560443065625/35831808:ℝ), (258447081336884375/83541860352:ℝ), (256905502068359375/167083720704:ℝ)],
  ![(55271275390625/71663616:ℝ), (256905502068359375/167083720704:ℝ), (255199739990234375/334167441408:ℝ)]]
theorem cell7_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 5 5 b ν := by
 have heq : pairedCleared cell7 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_5_5_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_5_5_g]
theorem cell7_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_5_5 hb hν
def cell7_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(188347261190050739/19061895313250000:ℝ)]]
theorem cell7_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 5 6) := by
 have heq : (-orderedLow cell7 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_5_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_5_6_g]
def cell7_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(2049230192074429304671/632427937944883200:ℝ), (2083818406706734028623/316213968972441600:ℝ), (85343395673988637975/25297117517795328:ℝ)]]
theorem cell7_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 5 6 ν := by
 have heq : mixedLowHigh cell7 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_5_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_5_6_g]
def cell7_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(30171257/10368:ℝ), (30844025/5184:ℝ), (31765625/10368:ℝ)]]
theorem cell7_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 6 false ν := by
 have heq : naturalFloor cell7 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_5_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_5_6_g]
def cell7_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(3454395853393/1165871232:ℝ), (3528143542225/582935616:ℝ), (3629872140625/1165871232:ℝ)]]
theorem cell7_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 5 6 true ν := by
 have heq : naturalFloor cell7 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_5_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_5_6_g]
def cell7_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(30171257/10368:ℝ), (30844025/5184:ℝ), (31765625/10368:ℝ)]]
theorem cell7_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_5_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_5_6_g]
def cell7_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(39422386328125/47775744:ℝ), (39509581718125/23887872:ℝ), (39435623828125/47775744:ℝ)],
  ![(117095188084375/71663616:ℝ), (546839808849270625/167083720704:ℝ), (545480000644140625/334167441408:ℝ)],
  ![(115520333984375/143327232:ℝ), (539159449862890625/334167441408:ℝ), (537532445556640625/668334882816:ℝ)]]
theorem cell7_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 5 6 b ν := by
 have heq : pairedCleared cell7 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_5_6_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_5_6_g]
theorem cell7_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_5_6 hb hν
def cell7_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(117662738700051871/19061895313250000:ℝ)]]
theorem cell7_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 6 1) := by
 have heq : (-orderedLow cell7 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_6_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_6_1_g]
def cell7_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(54740643651976453057/35134885441382400:ℝ), (163913126526568891123/52702328162073600:ℝ), (6561037628900200475/4216186252965888:ℝ)]]
theorem cell7_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 6 1 ν := by
 have heq : mixedLowHigh cell7 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_6_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_6_1_g]
def cell7_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(28906669/20736:ℝ), (28950925/10368:ℝ), (29078125/20736:ℝ)]]
theorem cell7_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 1 false ν := by
 have heq : naturalFloor cell7 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_6_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_6_1_g]
def cell7_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(3127189672381/2331742464:ℝ), (3135975015325/1165871232:ℝ), (3154087328125/2331742464:ℝ)]]
theorem cell7_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 1 true ν := by
 have heq : naturalFloor cell7 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_6_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_6_1_g]
def cell7_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(5749723/6912:ℝ), (5884475/3456:ℝ), (671875/768:ℝ)]]
theorem cell7_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_6_1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_6_1_g]
def cell7_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(116981191015625/429981696:ℝ), (117669318475625/214990848:ℝ), (118115716015625/429981696:ℝ)],
  ![(111047674525625/214990848:ℝ), (521259174379289375/501251162112:ℝ), (523610664937109375/1002502324224:ℝ)],
  ![(103663778515625/429981696:ℝ), (487272051655859375/1002502324224:ℝ), (490102335693359375/2005004648448:ℝ)]]
theorem cell7_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 6 1 b ν := by
 have heq : pairedCleared cell7 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_6_1_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_6_1_g]
theorem cell7_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_6_1 hb hν
def cell7_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(13109064110536647/2382736914156250:ℝ)]]
theorem cell7_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 6 2) := by
 have heq : (-orderedLow cell7 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_6_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_6_2_g]
def cell7_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(4448208562265124853/3162139689724416:ℝ), (4596597613787016325/1581069844862208:ℝ), (4770283782826703125/3162139689724416:ℝ)]]
theorem cell7_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 6 2 ν := by
 have heq : mixedLowHigh cell7 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_6_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_6_2_g]
def cell7_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(5749723/3456:ℝ), (5884475/1728:ℝ), (671875/384:ℝ)]]
theorem cell7_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 2 false ν := by
 have heq : naturalFloor cell7 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_6_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_6_2_g]
def cell7_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(1908817717381/1165871232:ℝ), (1955228100325/582935616:ℝ), (2010965453125/1165871232:ℝ)]]
theorem cell7_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 2 true ν := by
 have heq : naturalFloor cell7 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_6_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_6_2_g]
def cell7_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(83094389/62208:ℝ), (86149925/31104:ℝ), (89703125/62208:ℝ)]]
theorem cell7_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_6_2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_6_2_g]
def cell7_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(30548114453125/107495424:ℝ), (31755081308125/53747712:ℝ), (32841183203125/107495424:ℝ)],
  ![(32540127518125/53747712:ℝ), (156766202853401875/125312790528:ℝ), (161251602335546875/250625581056:ℝ)],
  ![(34169545703125/107495424:ℝ), (163819895304296875/250625581056:ℝ), (167778414794921875/501251162112:ℝ)]]
theorem cell7_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 6 2 b ν := by
 have heq : pairedCleared cell7 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_6_2_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_6_2_g]
theorem cell7_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_6_2 hb hν
def cell7_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(23694708797166783/3812379062650000:ℝ)]]
theorem cell7_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 6 3) := by
 have heq : (-orderedLow cell7 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_6_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_6_3_g]
def cell7_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2907847830466438921/1581069844862208:ℝ), (3032366390958054025/790534922431104:ℝ), (3175857789588015625/1581069844862208:ℝ)]]
theorem cell7_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 6 3 ν := by
 have heq : mixedLowHigh cell7 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_6_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_6_3_g]
def cell7_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(40090007/20736:ℝ), (41662775/10368:ℝ), (43484375/20736:ℝ)]]
theorem cell7_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 3 false ν := by
 have heq : naturalFloor cell7 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_6_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_6_3_g]
def cell7_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(40090007/20736:ℝ), (41662775/10368:ℝ), (43484375/20736:ℝ)]]
theorem cell7_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 3 true ν := by
 have heq : naturalFloor cell7 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_6_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_6_3_g]
def cell7_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(114441271/62208:ℝ), (119339575/31104:ℝ), (124984375/62208:ℝ)]]
theorem cell7_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_6_3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_6_3_g]
def cell7_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(181647529296875/429981696:ℝ), (188940011676875/214990848:ℝ), (195507304296875/429981696:ℝ)],
  ![(187779525306875/214990848:ℝ), (906879874455738125/501251162112:ℝ), (934866689880078125/1002502324224:ℝ)],
  ![(192461141796875/429981696:ℝ), (926178209411328125/1002502324224:ℝ), (951737409423828125/2005004648448:ℝ)]]
theorem cell7_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 6 3 b ν := by
 have heq : pairedCleared cell7 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_6_3_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_6_3_g]
theorem cell7_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_6_3 hb hν
def cell7_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(66037287543687327/9530947656625000:ℝ)]]
theorem cell7_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 6 4) := by
 have heq : (-orderedLow cell7 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_6_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_6_4_g]
def cell7_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(2394394253200210277/1054046563241472:ℝ), (278995109260933325/58558142402304:ℝ), (2644382458508453125/1054046563241472:ℝ)]]
theorem cell7_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 6 4 ν := by
 have heq : mixedLowHigh cell7 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_6_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_6_4_g]
def cell7_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(11420419/5184:ℝ), (12004675/2592:ℝ), (12671875/5184:ℝ)]]
theorem cell7_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 4 false ν := by
 have heq : naturalFloor cell7 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_6_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_6_4_g]
def cell7_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(1299631739881/582935616:ℝ), (1364854642825/291467808:ℝ), (1439404515625/582935616:ℝ)]]
theorem cell7_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 4 true ν := by
 have heq : naturalFloor cell7 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_6_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_6_4_g]
def cell7_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(11420419/5184:ℝ), (12004675/2592:ℝ), (12671875/5184:ℝ)]]
theorem cell7_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_6_4_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_6_4_g]
def cell7_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(40183766796875/71663616:ℝ), (13936649895625/11943936:ℝ), (43274979296875/71663616:ℝ)],
  ![(40899756756875/35831808:ℝ), (65927496527659375/27847286784:ℝ), (204121161736328125/167083720704:ℝ)],
  ![(41374016796875/71663616:ℝ), (66504268755859375/55694573568:ℝ), (205393526611328125/334167441408:ℝ)]]
theorem cell7_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 6 4 b ν := by
 have heq : pairedCleared cell7 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_6_4_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_6_4_g]
theorem cell7_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_6_4 hb hν
def cell7_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(198458120023514261/19061895313250000:ℝ)]]
theorem cell7_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 6 5) := by
 have heq : (-orderedLow cell7 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_6_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_6_5_g]
def cell7_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(623114247771240395/197633730607776:ℝ), (625526517842472125/98816865303888:ℝ), (631891462525859375/197633730607776:ℝ)]]
theorem cell7_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 6 5 ν := by
 have heq : mixedLowHigh cell7 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_6_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_6_5_g]
def cell7_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(60579595/20736:ℝ), (60980875/10368:ℝ), (61796875/20736:ℝ)]]
theorem cell7_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 5 false ν := by
 have heq : naturalFloor cell7 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_6_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_6_5_g]
def cell7_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(6935451228155/2331742464:ℝ), (6976765962875/1165871232:ℝ), (7064715546875/2331742464:ℝ)]]
theorem cell7_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 5 true ν := by
 have heq : naturalFloor cell7 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_6_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_6_5_g]
def cell7_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(60579595/20736:ℝ), (60980875/10368:ℝ), (61796875/20736:ℝ)]]
theorem cell7_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_6_5_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_6_5_g]
def cell7_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(39422386328125/47775744:ℝ), (117095188084375/71663616:ℝ), (115520333984375/143327232:ℝ)],
  ![(39509581718125/23887872:ℝ), (546839808849270625/167083720704:ℝ), (539159449862890625/334167441408:ℝ)],
  ![(39435623828125/47775744:ℝ), (545480000644140625/334167441408:ℝ), (537532445556640625/668334882816:ℝ)]]
theorem cell7_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 6 5 b ν := by
 have heq : pairedCleared cell7 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_6_5_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_6_5_g]
theorem cell7_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_6_5 hb hν
def cell7_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(4492800040636/381237906265:ℝ)]]
theorem cell7_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell7 6 6) := by
 have heq : (-orderedLow cell7 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell7_ordered_6_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_ordered_6_6_g]
def cell7_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(1471606823806431823/395267461215552:ℝ), (1487331113464933975/197633730607776:ℝ), (1512541822192609375/395267461215552:ℝ)]]
theorem cell7_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell7 6 6 ν := by
 have heq : mixedLowHigh cell7 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_mixed_6_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_mixed_6_6_g]
def cell7_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(36000007/10368:ℝ), (36492775/5184:ℝ), (37234375/10368:ℝ)]]
theorem cell7_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 6 false ν := by
 have heq : naturalFloor cell7 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor0_6_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor0_6_6_g]
def cell7_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(460074116627/129541248:ℝ), (465913524275/64770624:ℝ), (474861921875/129541248:ℝ)]]
theorem cell7_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell7 6 6 true ν := by
 have heq : naturalFloor cell7 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_floor1_6_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_floor1_6_6_g]
def cell7_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(36000007/10368:ℝ), (36492775/5184:ℝ), (37234375/10368:ℝ)]]
theorem cell7_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell7_complement_floor_6_6_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_complement_floor_6_6_g]
def cell7_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(103564137109375/107495424:ℝ), (103301312674375/53747712:ℝ), (102675893359375/107495424:ℝ)],
  ![(103301312674375/53747712:ℝ), (480083622397485625/125312790528:ℝ), (476834657531640625/250625581056:ℝ)],
  ![(102675893359375/107495424:ℝ), (476834657531640625/250625581056:ℝ), (473305271728515625/501251162112:ℝ)]]
theorem cell7_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell7 6 6 b ν := by
 have heq : pairedCleared cell7 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell7_paired_cleared_6_6_g (1587/2500:ℝ) (3/4:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_cleared_6_6_g]
theorem cell7_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell7 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell7_paired_cleared_6_6 hb hν
def cell7_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(12357108727104261/19061895313250000:ℝ)]]
theorem cell7_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell7.q/K)+1+17/50*(cell7.q/cell7.priorL)+17/25*(cell7.q/cell7.priorL)*cell7.priorB) := by
 have heq : ((2-17/50-17/25)*(cell7.q/K)+1+17/50*(cell7.q/cell7.priorL)+17/25*(cell7.q/cell7.priorL)*cell7.priorB) = Record12518109.Bernstein.bsum 0 0 (12357108727104261/19061895313250000:ℝ) cell7_increment0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_increment0_g]
def cell7_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(254512018633/508547750000:ℝ)]]
theorem cell7_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell7.q/cell7.priorL)*(1-cell7.priorB)) := by
 have heq : (1+17/25*(cell7.q/cell7.priorL)*(1-cell7.priorB)) = Record12518109.Bernstein.bsum 0 0 (254512018633/508547750000:ℝ) cell7_increment1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_increment1_g]
def cell7_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(1017809930899/2034191000000:ℝ)]]
theorem cell7_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell7.q/cell7.priorL)*(1-cell7.priorB)) := by
 have heq : (1+omega*(cell7.q/cell7.priorL)*(1-cell7.priorB)) = Record12518109.Bernstein.bsum 0 0 (1017809930899/2034191000000:ℝ) cell7_increment2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_increment2_g]
def cell7_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(4823663/41472:ℝ), (4792175/20736:ℝ), (4926575/41472:ℝ)]]
theorem cell7_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (191687/125000:ℝ) cell7_high_increment_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_high_increment_g]
def cell7_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(14594749747/1327104:ℝ), (120722587609/1327104:ℝ), (204698282009/1327104:ℝ), (93745094003/1327104:ℝ)]]
theorem cell7_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (131352747723/7812500000:ℝ) cell7_three_gate0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_three_gate0_g]
def cell7_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(2285419/41472:ℝ), (3213931/20736:ℝ), (4308331/41472:ℝ)]]
theorem cell7_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (2285419/3125000:ℝ) cell7_three_gate1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_three_gate1_g]
def cell7_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(510629793187/4663484928:ℝ), (508993399075/2331742464:ℝ), (526010944675/4663484928:ℝ)]]
theorem cell7_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell7.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell7.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (20359735963/14056125000:ℝ) cell7_three_gate2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_three_gate2_g]
def cell7_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(107159/224898:ℝ)]]
theorem cell7_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (1-cell7.q/K/3) := by
 have heq : (1-cell7.q/K/3) = Record12518109.Bernstein.bsum 0 0 (107159/224898:ℝ) cell7_paired_margin0_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_margin0_g]
def cell7_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(1119303/11657500:ℝ)]]
theorem cell7_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (gamma cell7-13/50) := by
 have heq : (gamma cell7-13/50) = Record12518109.Bernstein.bsum 0 0 (1119303/11657500:ℝ) cell7_paired_margin1_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_margin1_g]
def cell7_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(3409/37304:ℝ)]]
theorem cell7_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (cell7.q-gamma cell7) := by
 have heq : (cell7.q-gamma cell7) = Record12518109.Bernstein.bsum 0 0 (3409/37304:ℝ) cell7_paired_margin2_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_margin2_g]
def cell7_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(47629983/163205000:ℝ)]]
theorem cell7_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4:ℝ)) : 0 < (min (cell7.q+rho cell7.q) (3/4+rho (3/4))-gamma cell7) := by
 have heq : (min (cell7.q+rho cell7.q) (3/4+rho (3/4))-gamma cell7) = Record12518109.Bernstein.bsum 0 0 (47629983/163205000:ℝ) cell7_paired_margin3_g (9/250:ℝ) (3/80:ℝ) (1587/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell7, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell7_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell7_paired_margin3_g]
theorem cell7_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (1587/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1587/2500:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell7 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell7_paired_1_1 hb hν
 · exact cell7_paired_1_2 hb hν
 · exact cell7_paired_1_3 hb hν
 · exact cell7_paired_1_4 hb hν
 · exact cell7_paired_1_5 hb hν
 · exact cell7_paired_1_6 hb hν
 · exact cell7_paired_2_1 hb hν
 · exact cell7_paired_2_2 hb hν
 · exact cell7_paired_2_3 hb hν
 · exact cell7_paired_2_4 hb hν
 · exact cell7_paired_2_5 hb hν
 · exact cell7_paired_2_6 hb hν
 · exact cell7_paired_3_1 hb hν
 · exact cell7_paired_3_2 hb hν
 · exact cell7_paired_3_3 hb hν
 · exact cell7_paired_3_4 hb hν
 · exact cell7_paired_3_5 hb hν
 · exact cell7_paired_3_6 hb hν
 · exact cell7_paired_4_1 hb hν
 · exact cell7_paired_4_2 hb hν
 · exact cell7_paired_4_3 hb hν
 · exact cell7_paired_4_4 hb hν
 · exact cell7_paired_4_5 hb hν
 · exact cell7_paired_4_6 hb hν
 · exact cell7_paired_5_1 hb hν
 · exact cell7_paired_5_2 hb hν
 · exact cell7_paired_5_3 hb hν
 · exact cell7_paired_5_4 hb hν
 · exact cell7_paired_5_5 hb hν
 · exact cell7_paired_5_6 hb hν
 · exact cell7_paired_6_1 hb hν
 · exact cell7_paired_6_2 hb hν
 · exact cell7_paired_6_3 hb hν
 · exact cell7_paired_6_4 hb hν
 · exact cell7_paired_6_5 hb hν
 · exact cell7_paired_6_6 hb hν
end
end Record12518109Admission
