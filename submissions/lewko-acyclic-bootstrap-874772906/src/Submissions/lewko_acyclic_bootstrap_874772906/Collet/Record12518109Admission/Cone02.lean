/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell02
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell2_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(114046616348/381237906265:ℝ)]]
theorem cell2_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 1 1) := by
 have heq : (-orderedLow cell2 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_1_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_1_1_g]
def cell2_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(323763821109090064/1978395990771591:ℝ), (734180887491066200/1978395990771591:ℝ), (418330650345062500/1978395990771591:ℝ)]]
theorem cell2_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 1 1 ν := by
 have heq : mixedLowHigh cell2 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_1_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_1_1_g]
def cell2_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(9258064/77841:ℝ), (22134200/77841:ℝ), (13187500/77841:ℝ)]]
theorem cell2_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 1 false ν := by
 have heq : naturalFloor cell2 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_1_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_1_1_g]
def cell2_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(1164856438736/8753142609:ℝ), (2729140055800/8753142609:ℝ), (1599296187500/8753142609:ℝ)]]
theorem cell2_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 1 true ν := by
 have heq : naturalFloor cell2 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_1_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_1_1_g]
def cell2_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(9258064/77841:ℝ), (22134200/77841:ℝ), (13187500/77841:ℝ)]]
theorem cell2_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_1_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_1_1_g]
def cell2_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(193257350000000/6059221281:ℝ), (435359832640000/6059221281:ℝ), (238479762500000/6059221281:ℝ)],
  ![(435359832640000/6059221281:ℝ), (2238245942644060000/14099807920887:ℝ), (1208808842018750000/14099807920887:ℝ)],
  ![(238479762500000/6059221281:ℝ), (1208808842018750000/14099807920887:ℝ), (645941734375000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 1 1 b ν := by
 have heq : pairedCleared cell2 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_1_1_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_1_1_g]
theorem cell2_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_1_1 hb hν
def cell2_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(3302335234913553/4765473828312500:ℝ)]]
theorem cell2_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 1 2) := by
 have heq : (-orderedLow cell2 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_1_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_1_2_g]
def cell2_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(61033531586410936586/148379699307869325:ℝ), (134317555464572740111/148379699307869325:ℝ), (2978842458904990325/5935187972314773:ℝ)]]
theorem cell2_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 1 2 ν := by
 have heq : mixedLowHigh cell2 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_1_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_1_2_g]
def cell2_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(18516128/77841:ℝ), (44268400/77841:ℝ), (26375000/77841:ℝ)]]
theorem cell2_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 2 false ν := by
 have heq : naturalFloor cell2 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_1_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_1_2_g]
def cell2_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(18516128/77841:ℝ), (44268400/77841:ℝ), (26375000/77841:ℝ)]]
theorem cell2_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 2 true ν := by
 have heq : naturalFloor cell2 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_1_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_1_2_g]
def cell2_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(18516128/77841:ℝ), (44268400/77841:ℝ), (26375000/77841:ℝ)]]
theorem cell2_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_1_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_1_2_g]
def cell2_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(521887925000000/6059221281:ℝ), (1133350702780000/6059221281:ℝ), (604217337500000/6059221281:ℝ)],
  ![(1000263845140000/6059221281:ℝ), (5061319085266090000/14099807920887:ℝ), (2700995577481250000/14099807920887:ℝ)],
  ![(474753200000000/6059221281:ℝ), (2407657229825000000/14099807920887:ℝ), (1287057132812500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 1 2 b ν := by
 have heq : pairedCleared cell2 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_1_2_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_1_2_g]
theorem cell2_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_1_2 hb hν
def cell2_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(57375788391019/2382736914156250:ℝ)]]
theorem cell2_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 1 3) := by
 have heq : (-orderedLow cell2 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_1_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_1_3_g]
def cell2_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(5785140133991858956/148379699307869325:ℝ), (35087505356131988306/148379699307869325:ℝ), (1243316864553382450/5935187972314773:ℝ)]]
theorem cell2_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 1 3 ν := by
 have heq : mixedLowHigh cell2 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_1_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_1_3_g]
def cell2_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(9258064/25947:ℝ), (22134200/25947:ℝ), (13187500/25947:ℝ)]]
theorem cell2_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 3 false ν := by
 have heq : naturalFloor cell2 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_1_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_1_3_g]
def cell2_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(2999383716208/8753142609:ℝ), (7226734567400/8753142609:ℝ), (4332388562500/8753142609:ℝ)]]
theorem cell2_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 3 true ν := by
 have heq : naturalFloor cell2 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_1_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_1_3_g]
def cell2_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(9258064/25947:ℝ), (22134200/25947:ℝ), (13187500/25947:ℝ)]]
theorem cell2_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_1_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_1_3_g]
def cell2_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (216597160000/7239213:ℝ), (203612500000/7239213:ℝ)],
  ![(3774791480000/65152917:ℝ), (25841747045840000/151610837859:ℝ), (533233356250000/4890672189:ℝ)],
  ![(3735837500000/65152917:ℝ), (21129694981250000/151610837859:ℝ), (12180765625000000/151610837859:ℝ)]]
theorem cell2_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 1 3 b ν := by
 have heq : pairedCleared cell2 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_1_3_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_1_3_g]
theorem cell2_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_1_3 hb hν
def cell2_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(3516455732405591/4765473828312500:ℝ)]]
theorem cell2_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 1 4) := by
 have heq : (-orderedLow cell2 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_1_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_1_4_g]
def cell2_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(14178795045740346914/49459899769289775:ℝ), (38113831419624921139/49459899769289775:ℝ), (989055790807728425/1978395990771591:ℝ)]]
theorem cell2_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 1 4 ν := by
 have heq : mixedLowHigh cell2 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_1_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_1_4_g]
def cell2_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(37032256/77841:ℝ), (88536800/77841:ℝ), (52750000/77841:ℝ)]]
theorem cell2_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 4 false ν := by
 have heq : naturalFloor cell2 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_1_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_1_4_g]
def cell2_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(3916647354944/8753142609:ℝ), (9475531823200/8753142609:ℝ), (5698934750000/8753142609:ℝ)]]
theorem cell2_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 4 true ν := by
 have heq : naturalFloor cell2 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_1_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_1_4_g]
def cell2_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(37032256/77841:ℝ), (88536800/77841:ℝ), (52750000/77841:ℝ)]]
theorem cell2_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_1_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_1_4_g]
def cell2_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(109543525000000/2019740427:ℝ), (293094231020000/2019740427:ℝ), (178720412500000/2019740427:ℝ)],
  ![(305319873380000/2019740427:ℝ), (1742118539295050000/4699935973629:ℝ), (1009832833843750000/4699935973629:ℝ)],
  ![(194568775000000/2019740427:ℝ), (1054636673687500000/4699935973629:ℝ), (591308867187500000/4699935973629:ℝ)]]
theorem cell2_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 1 4 b ν := by
 have heq : pairedCleared cell2 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_1_4_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_1_4_g]
theorem cell2_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_1_4 hb hν
def cell2_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(1729539972007286/1191368457078125:ℝ)]]
theorem cell2_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 1 5) := by
 have heq : (-orderedLow cell2 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_1_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_1_5_g]
def cell2_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(79287630140450222528/148379699307869325:ℝ), (193595483161617538528/148379699307869325:ℝ), (4691017880292988100/5935187972314773:ℝ)]]
theorem cell2_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 1 5 ν := by
 have heq : mixedLowHigh cell2 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_1_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_1_5_g]
def cell2_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(46290320/77841:ℝ), (110671000/77841:ℝ), (65937500/77841:ℝ)]]
theorem cell2_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 5 false ν := by
 have heq : naturalFloor cell2 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_1_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_1_5_g]
def cell2_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(537101221520/972571401:ℝ), (1302703231000/972571401:ℝ), (785053437500/972571401:ℝ)]]
theorem cell2_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 5 true ν := by
 have heq : naturalFloor cell2 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_1_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_1_5_g]
def cell2_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(46290320/77841:ℝ), (110671000/77841:ℝ), (65937500/77841:ℝ)]]
theorem cell2_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_1_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_1_5_g]
def cell2_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(219087050000000/2019740427:ℝ), (525757854400000/2019740427:ℝ), (300632937500000/2019740427:ℝ)],
  ![(493621210880000/2019740427:ℝ), (2683142920169060000/4699935973629:ℝ), (1507228412331250000/4699935973629:ℝ)],
  ![(91108862500000/673246809:ℝ), (484750934318750000/1566645324543:ℝ), (89446000000000000/522215108181:ℝ)]]
theorem cell2_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 1 5 b ν := by
 have heq : pairedCleared cell2 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_1_5_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_1_5_g]
theorem cell2_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_1_5 hb hν
def cell2_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(23498439671162833/4765473828312500:ℝ)]]
theorem cell2_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 1 6) := by
 have heq : (-orderedLow cell2 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_1_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_1_6_g]
def cell2_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(61903367504536051438/49459899769289775:ℝ), (124101636953747396213/49459899769289775:ℝ), (2535412281746971975/1978395990771591:ℝ)]]
theorem cell2_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 1 6 ν := by
 have heq : mixedLowHigh cell2 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_1_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_1_6_g]
def cell2_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(92098384/77841:ℝ), (184980200/77841:ℝ), (94750000/77841:ℝ)]]
theorem cell2_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 6 false ν := by
 have heq : naturalFloor cell2 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_1_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_1_6_g]
def cell2_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(9861185582416/8753142609:ℝ), (19840152909800/8753142609:ℝ), (10189042750000/8753142609:ℝ)]]
theorem cell2_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 1 6 true ν := by
 have heq : naturalFloor cell2 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_1_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_1_6_g]
def cell2_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(92098384/77841:ℝ), (184980200/77841:ℝ), (94750000/77841:ℝ)]]
theorem cell2_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_1_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_1_6_g]
def cell2_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(1836410225000000/6059221281:ℝ), (3489376683340000/6059221281:ℝ), (1631230137500000/6059221281:ℝ)],
  ![(3695817395140000/6059221281:ℝ), (16353611655754210000/14099807920887:ℝ), (7655315956831250000/14099807920887:ℝ)],
  ![(1855784450000000/6059221281:ℝ), (8217477343550000000/14099807920887:ℝ), (3851518726562500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 1 6 b ν := by
 have heq : pairedCleared cell2 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_1_6_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_1_6_g]
theorem cell2_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_1_6 hb hν
def cell2_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(5835196183015197/4765473828312500:ℝ)]]
theorem cell2_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 2 1) := by
 have heq : (-orderedLow cell2 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_2_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_2_1_g]
def cell2_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(1873471818532400192/5935187972314773:ℝ), (3714750174734578600/5935187972314773:ℝ), (1865019108091437500/5935187972314773:ℝ)]]
theorem cell2_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 2 1 ν := by
 have heq : mixedLowHigh cell2 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_2_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_2_1_g]
def cell2_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(19228064/77841:ℝ), (38354200/77841:ℝ), (19437500/77841:ℝ)]]
theorem cell2_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 1 false ν := by
 have heq : naturalFloor cell2 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_2_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_2_1_g]
def cell2_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(19228064/77841:ℝ), (38354200/77841:ℝ), (19437500/77841:ℝ)]]
theorem cell2_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 1 true ν := by
 have heq : naturalFloor cell2 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_2_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_2_1_g]
def cell2_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(19228064/77841:ℝ), (38354200/77841:ℝ), (19437500/77841:ℝ)]]
theorem cell2_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_2_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_2_1_g]
def cell2_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(521887925000000/6059221281:ℝ), (1000263845140000/6059221281:ℝ), (474753200000000/6059221281:ℝ)],
  ![(1133350702780000/6059221281:ℝ), (5061319085266090000/14099807920887:ℝ), (2407657229825000000/14099807920887:ℝ)],
  ![(604217337500000/6059221281:ℝ), (2700995577481250000/14099807920887:ℝ), (1287057132812500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 2 1 b ν := by
 have heq : pairedCleared cell2 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_2_1_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_2_1_g]
theorem cell2_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_2_1 hb hν
def cell2_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(990569045226/381237906265:ℝ)]]
theorem cell2_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 2 2) := by
 have heq : (-orderedLow cell2 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_2_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_2_2_g]
def cell2_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(5491145358169160384/5935187972314773:ℝ), (11289479436279767200/5935187972314773:ℝ), (5845815581889125000/5935187972314773:ℝ)]]
theorem cell2_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 2 2 ν := by
 have heq : mixedLowHigh cell2 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_2_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_2_2_g]
def cell2_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(21685376/25947:ℝ), (44852800/25947:ℝ), (23375000/25947:ℝ)]]
theorem cell2_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 2 false ν := by
 have heq : naturalFloor cell2 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_2_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_2_2_g]
def cell2_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(7563089337472/8753142609:ℝ), (15611300321600/8753142609:ℝ), (8118236125000/8753142609:ℝ)]]
theorem cell2_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 2 true ν := by
 have heq : naturalFloor cell2 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_2_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_2_2_g]
def cell2_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(21685376/25947:ℝ), (44852800/25947:ℝ), (23375000/25947:ℝ)]]
theorem cell2_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_2_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_2_2_g]
def cell2_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(489833500000000/2019740427:ℝ), (990589321760000/2019740427:ℝ), (498340675000000/2019740427:ℝ)],
  ![(990589321760000/2019740427:ℝ), (4653891478546040000/4699935973629:ℝ), (2337886946762500000/4699935973629:ℝ)],
  ![(498340675000000/2019740427:ℝ), (2337886946762500000/4699935973629:ℝ), (1172965062500000000/4699935973629:ℝ)]]
theorem cell2_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 2 2 b ν := by
 have heq : pairedCleared cell2 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_2_2_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_2_2_g]
theorem cell2_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_2_2 hb hν
def cell2_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(14258865595888553/4765473828312500:ℝ)]]
theorem cell2_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 2 3) := by
 have heq : (-orderedLow cell2 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_2_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_2_3_g]
def cell2_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(174029878957458191386/148379699307869325:ℝ), (361490974809736955111/148379699307869325:ℝ), (7569666089758927825/5935187972314773:ℝ)]]
theorem cell2_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 2 3 ν := by
 have heq : mixedLowHigh cell2 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_2_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_2_3_g]
def cell2_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(2397232/2511:ℝ), (5054600/2511:ℝ), (2687500/2511:ℝ)]]
theorem cell2_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 3 false ν := by
 have heq : naturalFloor cell2 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_2_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_2_3_g]
def cell2_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(8480352976208/8753142609:ℝ), (17860097577400/8753142609:ℝ), (9484782312500/8753142609:ℝ)]]
theorem cell2_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 3 true ν := by
 have heq : naturalFloor cell2 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_2_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_2_3_g]
def cell2_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(2397232/2511:ℝ), (5054600/2511:ℝ), (2687500/2511:ℝ)]]
theorem cell2_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_2_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_2_3_g]
def cell2_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(599377025000000/2019740427:ℝ), (1223252945140000/2019740427:ℝ), (620253200000000/2019740427:ℝ)],
  ![(1178890659260000/2019740427:ℝ), (5594915859420050000/4699935973629:ℝ), (2835282525250000000/4699935973629:ℝ)],
  ![(192366162500000/673246809:ℝ), (912501025343750000/1566645324543:ℝ), (462223398437500000/1566645324543:ℝ)]]
theorem cell2_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 2 3 b ν := by
 have heq : pairedCleared cell2 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_2_3_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_2_3_g]
theorem cell2_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_2_3 hb hν
def cell2_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(5535640968878519/2382736914156250:ℝ)]]
theorem cell2_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 2 4) := by
 have heq : (-orderedLow cell2 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_2_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_2_4_g]
def cell2_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(13197943056115457084/16486633256429925:ℝ), (29140102744588467034/16486633256429925:ℝ), (648237832823035550/659465330257197:ℝ)]]
theorem cell2_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 2 4 ν := by
 have heq : mixedLowHigh cell2 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_2_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_2_4_g]
def cell2_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(83572256/77841:ℝ), (178826800/77841:ℝ), (96500000/77841:ℝ)]]
theorem cell2_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 4 false ν := by
 have heq : naturalFloor cell2 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_2_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_2_4_g]
def cell2_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(83572256/77841:ℝ), (178826800/77841:ℝ), (96500000/77841:ℝ)]]
theorem cell2_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 4 true ν := by
 have heq : naturalFloor cell2 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_2_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_2_4_g]
def cell2_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(83572256/77841:ℝ), (178826800/77841:ℝ), (96500000/77841:ℝ)]]
theorem cell2_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_2_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_2_4_g]
def cell2_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(1276243150000000/6059221281:ℝ), (2717699955560000/6059221281:ℝ), (1426965925000000/6059221281:ℝ)],
  ![(2887463740280000/6059221281:ℝ), (14126710968257180000/14099807920887:ℝ), (7342163764337500000/14099807920887:ℝ)],
  ![(1603975150000000/6059221281:ℝ), (7769913631525000000/14099807920887:ℝ), (4005764656250000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 2 4 b ν := by
 have heq : pairedCleared cell2 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_2_4_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_2_4_g]
theorem cell2_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_2_4 hb hν
def cell2_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(14472986093380591/4765473828312500:ℝ)]]
theorem cell2_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 2 5) := by
 have heq : (-orderedLow cell2 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_2_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_2_5_g]
def cell2_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(155532732508268295542/148379699307869325:ℝ), (341514913604038978417/148379699307869325:ℝ), (7557991003277122775/5935187972314773:ℝ)]]
theorem cell2_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 2 5 ν := by
 have heq : mixedLowHigh cell2 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_2_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_2_5_g]
def cell2_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(3438160/2883:ℝ), (2481000/961:ℝ), (4062500/2883:ℝ)]]
theorem cell2_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 5 false ν := by
 have heq : naturalFloor cell2 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_2_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_2_5_g]
def cell2_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(10314880253680/8753142609:ℝ), (22357692089000/8753142609:ℝ), (12217874687500/8753142609:ℝ)]]
theorem cell2_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 5 true ν := by
 have heq : naturalFloor cell2 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_2_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_2_5_g]
def cell2_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(3438160/2883:ℝ), (2481000/961:ℝ), (4062500/2883:ℝ)]]
theorem cell2_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_2_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_2_5_g]
def cell2_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(1604873725000000/6059221281:ℝ), (3415690825700000/6059221281:ℝ), (1792703500000000/6059221281:ℝ)],
  ![(3452367752780000/6059221281:ℝ), (16949784110879210000/14099807920887:ℝ), (8834350499800000000/14099807920887:ℝ)],
  ![(1840248587500000/6059221281:ℝ), (8968762019331250000/14099807920887:ℝ), (4646880054687500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 2 5 b ν := by
 have heq : pairedCleared cell2 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_2_5_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_2_5_g]
theorem cell2_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_2_5 hb hν
def cell2_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(4468672562251036/1191368457078125:ℝ)]]
theorem cell2_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 2 6) := by
 have heq : (-orderedLow cell2 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_2_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_2_6_g]
def cell2_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(192283977511497477328/148379699307869325:ℝ), (420768902506781753528/148379699307869325:ℝ), (9281841511146925600/5935187972314773:ℝ)]]
theorem cell2_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 2 6 ν := by
 have heq : mixedLowHigh cell2 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_2_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_2_6_g]
def cell2_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(102088384/77841:ℝ), (223095200/77841:ℝ), (122875000/77841:ℝ)]]
theorem cell2_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 6 false ν := by
 have heq : naturalFloor cell2 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_2_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_2_6_g]
def cell2_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(362327222336/282359439:ℝ), (793757720800/282359439:ℝ), (438207125000/282359439:ℝ)]]
theorem cell2_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 2 6 true ν := by
 have heq : naturalFloor cell2 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_2_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_2_6_g]
def cell2_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(102088384/77841:ℝ), (223095200/77841:ℝ), (122875000/77841:ℝ)]]
theorem cell2_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_2_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_2_6_g]
def cell2_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(1933504300000000/6059221281:ℝ), (4113681695840000/6059221281:ℝ), (2158441075000000/6059221281:ℝ)],
  ![(4017271765280000/6059221281:ℝ), (19772857253501240000/14099807920887:ℝ), (10326537235262500000/14099807920887:ℝ)],
  ![(2076522025000000/6059221281:ℝ), (10167610407137500000/14099807920887:ℝ), (5287995453125000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 2 6 b ν := by
 have heq : pairedCleared cell2 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_2_6_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_2_6_g]
theorem cell2_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_2_6 hb hν
def cell2_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(52861690214127/1191368457078125:ℝ)]]
theorem cell2_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 3 1) := by
 have heq : (-orderedLow cell2 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_3_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_3_1_g]
def cell2_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(286066958220487364/1978395990771591:ℝ), (36239712251819250/73273925584133:ℝ), (700318856541718750/1978395990771591:ℝ)]]
theorem cell2_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 3 1 ν := by
 have heq : mixedLowHigh cell2 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_3_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_3_1_g]
def cell2_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(15918064/77841:ℝ), (47544200/77841:ℝ), (31937500/77841:ℝ)]]
theorem cell2_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 1 false ν := by
 have heq : naturalFloor cell2 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_3_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_3_1_g]
def cell2_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(1666173978736/8753142609:ℝ), (5106126345800/8753142609:ℝ), (3474964937500/8753142609:ℝ)]]
theorem cell2_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 1 true ν := by
 have heq : naturalFloor cell2 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_3_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_3_1_g]
def cell2_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(158632/2883:ℝ), (8323900/25947:ℝ), (7000000/25947:ℝ)]]
theorem cell2_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_3_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_3_1_g]
def cell2_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (3774791480000/65152917:ℝ), (3735837500000/65152917:ℝ)],
  ![(216597160000/7239213:ℝ), (25841747045840000/151610837859:ℝ), (21129694981250000/151610837859:ℝ)],
  ![(203612500000/7239213:ℝ), (533233356250000/4890672189:ℝ), (12180765625000000/151610837859:ℝ)]]
theorem cell2_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 3 1 b ν := by
 have heq : pairedCleared cell2 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_3_1_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_3_1_g]
theorem cell2_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_3_1 hb hν
def cell2_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(16791726543990197/4765473828312500:ℝ)]]
theorem cell2_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 3 2) := by
 have heq : (-orderedLow cell2 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_3_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_3_2_g]
def cell2_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(6393325713374290384/5935187972314773:ℝ), (12801686948541147200/5935187972314773:ℝ), (6455842738945375000/5935187972314773:ℝ)]]
theorem cell2_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 3 2 ν := by
 have heq : mixedLowHigh cell2 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_3_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_3_2_g]
def cell2_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(75026128/77841:ℝ), (150778400/77841:ℝ), (76375000/77841:ℝ)]]
theorem cell2_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 2 false ν := by
 have heq : naturalFloor cell2 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_3_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_3_2_g]
def cell2_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(8560409467472/8753142609:ℝ), (17195051701600/8753142609:ℝ), (8704667375000/8753142609:ℝ)]]
theorem cell2_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 2 true ν := by
 have heq : naturalFloor cell2 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_3_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_3_2_g]
def cell2_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(75026128/77841:ℝ), (150778400/77841:ℝ), (76375000/77841:ℝ)]]
theorem cell2_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_3_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_3_2_g]
def cell2_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(599377025000000/2019740427:ℝ), (1178890659260000/2019740427:ℝ), (192366162500000/673246809:ℝ)],
  ![(1223252945140000/2019740427:ℝ), (5594915859420050000/4699935973629:ℝ), (912501025343750000/1566645324543:ℝ)],
  ![(620253200000000/2019740427:ℝ), (2835282525250000000/4699935973629:ℝ), (462223398437500000/1566645324543:ℝ)]]
theorem cell2_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 3 2 b ν := by
 have heq : pairedCleared cell2 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_3_2_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_3_2_g]
theorem cell2_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_3_2 hb hν
def cell2_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(1867091474104/381237906265:ℝ)]]
theorem cell2_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 3 3) := by
 have heq : (-orderedLow cell2 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_3_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_3_3_g]
def cell2_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(10010999253011050576/5935187972314773:ℝ), (20376416210086335800/5935187972314773:ℝ), (10436639212743062500/5935187972314773:ℝ)]]
theorem cell2_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 3 3 ν := by
 have heq : mixedLowHigh cell2 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_3_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_3_3_g]
def cell2_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(120854192/77841:ℝ), (246982600/77841:ℝ), (127062500/77841:ℝ)]]
theorem cell2_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 3 false ν := by
 have heq : naturalFloor cell2 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_3_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_3_3_g]
def cell2_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(4653774078736/2917714203:ℝ), (9497820195800/2917714203:ℝ), (4879058687500/2917714203:ℝ)]]
theorem cell2_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 3 true ν := by
 have heq : naturalFloor cell2 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_3_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_3_3_g]
def cell2_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(120854192/77841:ℝ), (246982600/77841:ℝ), (127062500/77841:ℝ)]]
theorem cell2_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_3_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_3_3_g]
def cell2_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(2745743650000000/6059221281:ℝ), (5508176097920000/6059221281:ℝ), (2751564287500000/6059221281:ℝ)],
  ![(5508176097920000/6059221281:ℝ), (25685102928632180000/14099807920887:ℝ), (12818512838556250000/14099807920887:ℝ)],
  ![(2751564287500000/6059221281:ℝ), (12818512838556250000/14099807920887:ℝ), (6391848640625000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 3 3 b ν := by
 have heq : pairedCleared cell2 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_3_3_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_3_3_g]
theorem cell2_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_3_3 hb hν
def cell2_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(25215395956863553/4765473828312500:ℝ)]]
theorem cell2_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 3 4) := by
 have heq : (-orderedLow cell2 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_3_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_3_4_g]
def cell2_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(95675408776168482062/49459899769289775:ℝ), (196221464718300390037/49459899769289775:ℝ), (4053496573537621775/1978395990771591:ℝ)]]
theorem cell2_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 3 4 ν := by
 have heq : mixedLowHigh cell2 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_3_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_3_4_g]
def cell2_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(43370752/25947:ℝ), (89705600/25947:ℝ), (46750000/25947:ℝ)]]
theorem cell2_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 4 false ν := by
 have heq : naturalFloor cell2 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_3_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_3_4_g]
def cell2_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(14878585874944/8753142609:ℝ), (30742257843200/8753142609:ℝ), (16003722250000/8753142609:ℝ)]]
theorem cell2_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 4 true ν := by
 have heq : naturalFloor cell2 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_3_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_3_4_g]
def cell2_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(43370752/25947:ℝ), (89705600/25947:ℝ), (46750000/25947:ℝ)]]
theorem cell2_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_3_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_3_4_g]
def cell2_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(3074374225000000/6059221281:ℝ), (6206166968060000/6059221281:ℝ), (3117301862500000/6059221281:ℝ)],
  ![(6073080110420000/6059221281:ℝ), (28508176071254210000/14099807920887:ℝ), (14310699574018750000/14099807920887:ℝ)],
  ![(2987837725000000/6059221281:ℝ), (14017361226362500000/14099807920887:ℝ), (7032964039062500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 3 4 b ν := by
 have heq : pairedCleared cell2 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_3_4_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_3_4_g]
theorem cell2_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_3_4 hb hν
def cell2_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(11013906149366019/2382736914156250:ℝ)]]
theorem cell2_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 3 5) := by
 have heq : (-orderedLow cell2 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_3_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_3_5_g]
def cell2_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(231777834876086368556/148379699307869325:ℝ), (489434344046460418306/148379699307869325:ℝ), (10424964126261257450/5935187972314773:ℝ)]]
theorem cell2_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 3 5 ν := by
 have heq : mixedLowHigh cell2 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_3_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_3_5_g]
def cell2_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(139370320/77841:ℝ), (291251000/77841:ℝ), (153437500/77841:ℝ)]]
theorem cell2_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 5 false ν := by
 have heq : naturalFloor cell2 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_3_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_3_5_g]
def cell2_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(15795849513680/8753142609:ℝ), (32991055099000/8753142609:ℝ), (17370268437500/8753142609:ℝ)]]
theorem cell2_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 5 true ν := by
 have heq : naturalFloor cell2 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_3_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_3_5_g]
def cell2_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(139370320/77841:ℝ), (291251000/77841:ℝ), (153437500/77841:ℝ)]]
theorem cell2_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_3_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_3_5_g]
def cell2_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(2552486300000000/6059221281:ℝ), (5254108088200000/6059221281:ℝ), (2683508187500000/6059221281:ℝ)],
  ![(5423871872920000/6059221281:ℝ), (25850139461251240000/14099807920887:ℝ), (13147015762606250000/14099807920887:ℝ)],
  ![(2860517412500000/6059221281:ℝ), (13574765629793750000/14099807920887:ℝ), (6878718109375000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 3 5 b ν := by
 have heq : pairedCleared cell2 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_3_5_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_3_5_g]
theorem cell2_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_3_5 hb hν
def cell2_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(25429516454355591/4765473828312500:ℝ)]]
theorem cell2_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 3 6) := by
 have heq : (-orderedLow cell2 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_3_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_3_6_g]
def cell2_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(268529079879315550342/148379699307869325:ℝ), (568688332949203193417/148379699307869325:ℝ), (12148814634131060275/5935187972314773:ℝ)]]
theorem cell2_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 3 6 ν := by
 have heq : mixedLowHigh cell2 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_3_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_3_6_g]
def cell2_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(4794464/2511:ℝ), (10109200/2511:ℝ), (5375000/2511:ℝ)]]
theorem cell2_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 6 false ν := by
 have heq : naturalFloor cell2 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_3_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_3_6_g]
def cell2_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(4794464/2511:ℝ), (10109200/2511:ℝ), (5375000/2511:ℝ)]]
theorem cell2_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 3 6 true ν := by
 have heq : naturalFloor cell2 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_3_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_3_6_g]
def cell2_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(4794464/2511:ℝ), (10109200/2511:ℝ), (5375000/2511:ℝ)]]
theorem cell2_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_3_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_3_6_g]
def cell2_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(2881116875000000/6059221281:ℝ), (5952098958340000/6059221281:ℝ), (3049245762500000/6059221281:ℝ)],
  ![(5988775885420000/6059221281:ℝ), (28673212603873270000/14099807920887:ℝ), (14639202498068750000/14099807920887:ℝ)],
  ![(3096790850000000/6059221281:ℝ), (14773614017600000000/14099807920887:ℝ), (7519833507812500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 3 6 b ν := by
 have heq : pairedCleared cell2 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_3_6_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_3_6_g]
theorem cell2_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_3_6 hb hν
def cell2_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(1553254593241591/953094765662500:ℝ)]]
theorem cell2_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 4 1) := by
 have heq : (-orderedLow cell2 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_4_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_4_1_g]
def cell2_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(876593008529224664/1978395990771591:ℝ), (2044766920645138300/1978395990771591:ℝ), (1176087496079000000/1978395990771591:ℝ)]]
theorem cell2_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 4 1 ν := by
 have heq : mixedLowHigh cell2 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_4_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_4_1_g]
def cell2_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(1585744/2511:ℝ), (3513200/2511:ℝ), (62500/81:ℝ)]]
theorem cell2_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 1 false ν := by
 have heq : naturalFloor cell2 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_4_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_4_1_g]
def cell2_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(5280182338736/8753142609:ℝ), (11766387830800/8753142609:ℝ), (6521218062500/8753142609:ℝ)]]
theorem cell2_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 1 true ν := by
 have heq : naturalFloor cell2 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_4_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_4_1_g]
def cell2_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(25888064/77841:ℝ), (63764200/77841:ℝ), (38187500/77841:ℝ)]]
theorem cell2_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_4_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_4_1_g]
def cell2_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(109543525000000/2019740427:ℝ), (305319873380000/2019740427:ℝ), (194568775000000/2019740427:ℝ)],
  ![(293094231020000/2019740427:ℝ), (1742118539295050000/4699935973629:ℝ), (1054636673687500000/4699935973629:ℝ)],
  ![(178720412500000/2019740427:ℝ), (1009832833843750000/4699935973629:ℝ), (591308867187500000/4699935973629:ℝ)]]
theorem cell2_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 4 1 b ν := by
 have heq : pairedCleared cell2 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_4_1_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_4_1_g]
theorem cell2_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_4_1 hb hν
def cell2_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(2791994280457877/1191368457078125:ℝ)]]
theorem cell2_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 4 2) := by
 have heq : (-orderedLow cell2 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_4_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_4_2_g]
def cell2_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(5378054769503352284/5935187972314773:ℝ), (12022353466203927850/5935187972314773:ℝ), (6691780200479093750/5935187972314773:ℝ)]]
theorem cell2_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 4 2 ν := by
 have heq : mixedLowHigh cell2 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_4_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_4_2_g]
def cell2_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(23905376/25947:ℝ), (53322800/25947:ℝ), (9875000/8649:ℝ)]]
theorem cell2_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 2 false ν := by
 have heq : naturalFloor cell2 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_4_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_4_2_g]
def cell2_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(23905376/25947:ℝ), (53322800/25947:ℝ), (9875000/8649:ℝ)]]
theorem cell2_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 2 true ν := by
 have heq : naturalFloor cell2 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_4_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_4_2_g]
def cell2_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(203513384/233523:ℝ), (457332700/233523:ℝ), (255687500/233523:ℝ)]]
theorem cell2_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_4_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_4_2_g]
def cell2_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(1276243150000000/6059221281:ℝ), (2887463740280000/6059221281:ℝ), (1603975150000000/6059221281:ℝ)],
  ![(2717699955560000/6059221281:ℝ), (14126710968257180000/14099807920887:ℝ), (7769913631525000000/14099807920887:ℝ)],
  ![(1426965925000000/6059221281:ℝ), (7342163764337500000/14099807920887:ℝ), (4005764656250000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 4 2 b ν := by
 have heq : pairedCleared cell2 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_4_2_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_4_2_g]
theorem cell2_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_4_2 hb hν
def cell2_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(27748256904965197/4765473828312500:ℝ)]]
theorem cell2_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 4 3) := by
 have heq : (-orderedLow cell2 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_4_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_4_3_g]
def cell2_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(1212575512024020064/659465330257197:ℝ), (7296207907449238600/1978395990771591:ℝ), (3682222123266437500/1978395990771591:ℝ)]]
theorem cell2_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 4 3 ν := by
 have heq : mixedLowHigh cell2 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_4_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_4_3_g]
def cell2_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(43608064/25947:ℝ), (87734200/25947:ℝ), (4937500/2883:ℝ)]]
theorem cell2_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 3 false ν := by
 have heq : naturalFloor cell2 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_4_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_4_3_g]
def cell2_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(14958642366208/8753142609:ℝ), (30077211967400/8753142609:ℝ), (15223607312500/8753142609:ℝ)]]
theorem cell2_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 3 true ν := by
 have heq : naturalFloor cell2 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_4_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_4_3_g]
def cell2_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(43608064/25947:ℝ), (87734200/25947:ℝ), (4937500/2883:ℝ)]]
theorem cell2_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_4_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_4_3_g]
def cell2_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(3074374225000000/6059221281:ℝ), (6073080110420000/6059221281:ℝ), (2987837725000000/6059221281:ℝ)],
  ![(6206166968060000/6059221281:ℝ), (28508176071254210000/14099807920887:ℝ), (14017361226362500000/14099807920887:ℝ)],
  ![(3117301862500000/6059221281:ℝ), (14310699574018750000/14099807920887:ℝ), (7032964039062500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 4 3 b ν := by
 have heq : pairedCleared cell2 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_4_3_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_4_3_g]
theorem cell2_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_4_3 hb hν
def cell2_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(2743613902982/381237906265:ℝ)]]
theorem cell2_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 4 4) := by
 have heq : (-orderedLow cell2 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_4_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_4_4_g]
def cell2_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(538179746216775584/219821776752399:ℝ), (1091235295699737200/219821776752399:ℝ), (185524232637000000/73273925584133:ℝ)]]
theorem cell2_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 4 4 ν := by
 have heq : mixedLowHigh cell2 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_4_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_4_4_g]
def cell2_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(176652256/77841:ℝ), (359406800/77841:ℝ), (184000000/77841:ℝ)]]
theorem cell2_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 4 false ν := by
 have heq : naturalFloor cell2 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_4_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_4_4_g]
def cell2_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(20359555134944/8753142609:ℝ), (41375620853200/8753142609:ℝ), (21156116000000/8753142609:ℝ)]]
theorem cell2_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 4 true ν := by
 have heq : naturalFloor cell2 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_4_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_4_4_g]
def cell2_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(176652256/77841:ℝ), (359406800/77841:ℝ), (184000000/77841:ℝ)]]
theorem cell2_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_4_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_4_4_g]
def cell2_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(4021986800000000/6059221281:ℝ), (8044584230560000/6059221281:ℝ), (4008106550000000/6059221281:ℝ)],
  ![(8044584230560000/6059221281:ℝ), (37408531421626240000/14099807920887:ℝ), (18623364836825000000/14099807920887:ℝ)],
  ![(4008106550000000/6059221281:ℝ), (18623364836825000000/14099807920887:ℝ), (9264802093750000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 4 4 b ν := by
 have heq : pairedCleared cell2 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_4_4_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_4_4_g]
theorem cell2_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_4_4 hb hν
def cell2_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(36171926317838553/4765473828312500:ℝ)]]
theorem cell2_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 4 5) := by
 have heq : (-orderedLow cell2 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_4_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_4_5_g]
def cell2_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(400022573699552700986/148379699307869325:ℝ), (815837813500065385111/148379699307869325:ℝ), (16751313351466802825/5935187972314773:ℝ)]]
theorem cell2_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 4 5 ν := by
 have heq : mixedLowHigh cell2 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_4_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_4_5_g]
def cell2_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(185910320/77841:ℝ), (381541000/77841:ℝ), (197187500/77841:ℝ)]]
theorem cell2_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 5 false ν := by
 have heq : naturalFloor cell2 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_4_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_4_5_g]
def cell2_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(7092272924560/2917714203:ℝ), (14541472703000/2917714203:ℝ), (7507554062500/2917714203:ℝ)]]
theorem cell2_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 5 true ν := by
 have heq : naturalFloor cell2 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_4_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_4_5_g]
def cell2_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(185910320/77841:ℝ), (381541000/77841:ℝ), (197187500/77841:ℝ)]]
theorem cell2_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_4_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_4_5_g]
def cell2_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(4350617375000000/6059221281:ℝ), (8742575100700000/6059221281:ℝ), (4373844125000000/6059221281:ℝ)],
  ![(8609488243060000/6059221281:ℝ), (40231604564248270000/14099807920887:ℝ), (20115551572287500000/14099807920887:ℝ)],
  ![(4244379987500000/6059221281:ℝ), (19822213224631250000/14099807920887:ℝ), (9905917492187500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 4 5 b ν := by
 have heq : pairedCleared cell2 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_4_5_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_4_5_g]
theorem cell2_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_4_5 hb hν
def cell2_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(16492171329853519/2382736914156250:ℝ)]]
theorem cell2_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 4 6) := by
 have heq : (-orderedLow cell2 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_4_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_4_6_g]
def cell2_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(344774182247133623356/148379699307869325:ℝ), (716607763391624633306/148379699307869325:ℝ), (15015787757115194950/5935187972314773:ℝ)]]
theorem cell2_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 4 6 ν := by
 have heq : mixedLowHigh cell2 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_4_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_4_6_g]
def cell2_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(21685376/8649:ℝ), (44852800/8649:ℝ), (23375000/8649:ℝ)]]
theorem cell2_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 6 false ν := by
 have heq : naturalFloor cell2 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_4_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_4_6_g]
def cell2_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(715938142336/282359439:ℝ), (1479781140800/282359439:ℝ), (770619625000/282359439:ℝ)]]
theorem cell2_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 4 6 true ν := by
 have heq : naturalFloor cell2 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_4_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_4_6_g]
def cell2_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(21685376/8649:ℝ), (44852800/8649:ℝ), (23375000/8649:ℝ)]]
theorem cell2_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_4_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_4_6_g]
def cell2_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(1276243150000000/2019740427:ℝ), (2596838740280000/2019740427:ℝ), (1313350150000000/2019740427:ℝ)],
  ![(2653426668520000/2019740427:ℝ), (12524522651415100000/4699935973629:ℝ), (6317289253625000000/4699935973629:ℝ)],
  ![(457451075000000/673246809:ℝ), (2153290847562500000/1566645324543:ℝ), (1083519062500000000/1566645324543:ℝ)]]
theorem cell2_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 4 6 b ν := by
 have heq : pairedCleared cell2 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_4_6_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_4_6_g]
theorem cell2_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_4_6 hb hν
def cell2_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(7660549585779701/2382736914156250:ℝ)]]
theorem cell2_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 5 1) := by
 have heq : (-orderedLow cell2 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_5_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_5_1_g]
def cell2_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(1467119058837961964/1978395990771591:ℝ), (3111061610491156850/1978395990771591:ℝ), (183539570624031250/219821776752399:ℝ)]]
theorem cell2_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 5 1 ν := by
 have heq : mixedLowHigh cell2 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_5_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_5_1_g]
def cell2_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(82398064/77841:ℝ), (170274200/77841:ℝ), (88187500/77841:ℝ)]]
theorem cell2_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 1 false ν := by
 have heq : naturalFloor cell2 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_5_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_5_1_g]
def cell2_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(2964730232912/2917714203:ℝ), (6142216438600/2917714203:ℝ), (3189157062500/2917714203:ℝ)]]
theorem cell2_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 1 true ν := by
 have heq : naturalFloor cell2 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_5_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_5_1_g]
def cell2_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(47493064/77841:ℝ), (102556700/77841:ℝ), (55375000/77841:ℝ)]]
theorem cell2_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_5_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_5_1_g]
def cell2_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(219087050000000/2019740427:ℝ), (493621210880000/2019740427:ℝ), (91108862500000/673246809:ℝ)],
  ![(525757854400000/2019740427:ℝ), (2683142920169060000/4699935973629:ℝ), (484750934318750000/1566645324543:ℝ)],
  ![(300632937500000/2019740427:ℝ), (1507228412331250000/4699935973629:ℝ), (89446000000000000/522215108181:ℝ)]]
theorem cell2_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 5 1 b ν := by
 have heq : pairedCleared cell2 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_5_1_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_5_1_g]
theorem cell2_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_5_1 hb hν
def cell2_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(3744560665436591/953094765662500:ℝ)]]
theorem cell2_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 5 2) := by
 have heq : (-orderedLow cell2 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_5_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_5_2_g]
def cell2_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(7149632920429564184/5935187972314773:ℝ), (15221237535741983500/5935187972314773:ℝ), (8119086119090937500/5935187972314773:ℝ)]]
theorem cell2_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 5 2 ν := by
 have heq : mixedLowHigh cell2 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_5_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_5_2_g]
def cell2_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(3887264/2883:ℝ), (24592600/8649:ℝ), (13000000/8649:ℝ)]]
theorem cell2_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 2 false ν := by
 have heq : naturalFloor cell2 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_5_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_5_2_g]
def cell2_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(11678415237472/8753142609:ℝ), (24648548096600/8753142609:ℝ), (13040158000000/8753142609:ℝ)]]
theorem cell2_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 2 true ν := by
 have heq : naturalFloor cell2 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_5_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_5_2_g]
def cell2_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(268328384/233523:ℝ), (573710200/233523:ℝ), (307250000/233523:ℝ)]]
theorem cell2_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_5_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_5_2_g]
def cell2_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(1604873725000000/6059221281:ℝ), (3452367752780000/6059221281:ℝ), (1840248587500000/6059221281:ℝ)],
  ![(3415690825700000/6059221281:ℝ), (16949784110879210000/14099807920887:ℝ), (8968762019331250000/14099807920887:ℝ)],
  ![(1792703500000000/6059221281:ℝ), (8834350499800000000/14099807920887:ℝ), (4646880054687500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 5 2 b ν := by
 have heq : pairedCleared cell2 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_5_2_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_5_2_g]
theorem cell2_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_5_2 hb hν
def cell2_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(5531126870701627/1191368457078125:ℝ)]]
theorem cell2_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 5 3) := by
 have heq : (-orderedLow cell2 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_5_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_5_3_g]
def cell2_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(9897908664345242476/5935187972314773:ℝ), (21109290240010496450/5935187972314773:ℝ), (11282603831333031250/5935187972314773:ℝ)]]
theorem cell2_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 5 3 ν := by
 have heq : mixedLowHigh cell2 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_5_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_5_3_g]
def cell2_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(127514192/77841:ℝ), (272392600/77841:ℝ), (145812500/77841:ℝ)]]
theorem cell2_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 3 false ν := by
 have heq : naturalFloor cell2 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_5_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_5_3_g]
def cell2_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(14462639776208/8753142609:ℝ), (30870446877400/8753142609:ℝ), (16512844812500/8753142609:ℝ)]]
theorem cell2_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 3 true ν := by
 have heq : naturalFloor cell2 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_5_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_5_3_g]
def cell2_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(127514192/77841:ℝ), (272392600/77841:ℝ), (145812500/77841:ℝ)]]
theorem cell2_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_5_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_5_3_g]
def cell2_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(2552486300000000/6059221281:ℝ), (5423871872920000/6059221281:ℝ), (2860517412500000/6059221281:ℝ)],
  ![(5254108088200000/6059221281:ℝ), (25850139461251240000/14099807920887:ℝ), (13574765629793750000/14099807920887:ℝ)],
  ![(2683508187500000/6059221281:ℝ), (13147015762606250000/14099807920887:ℝ), (6878718109375000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 5 3 b ν := by
 have heq : pairedCleared cell2 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_5_3_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_5_3_g]
theorem cell2_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_5_3 hb hν
def cell2_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(38704787265940197/4765473828312500:ℝ)]]
theorem cell2_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 5 4) := by
 have heq : (-orderedLow cell2 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_5_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_5_4_g]
def cell2_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(15433033503058070768/5935187972314773:ℝ), (30975560496154284400/5935187972314773:ℝ), (15637490000653250000/5935187972314773:ℝ)]]
theorem cell2_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 5 4 ν := by
 have heq : mixedLowHigh cell2 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_5_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_5_4_g]
def cell2_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(186622256/77841:ℝ), (375626800/77841:ℝ), (190250000/77841:ℝ)]]
theorem cell2_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 4 false ν := by
 have heq : naturalFloor cell2 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_5_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_5_4_g]
def cell2_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(7118958421648/2917714203:ℝ), (14319790744400/2917714203:ℝ), (7247515750000/2917714203:ℝ)]]
theorem cell2_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 4 true ν := by
 have heq : naturalFloor cell2 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_5_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_5_4_g]
def cell2_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(186622256/77841:ℝ), (375626800/77841:ℝ), (190250000/77841:ℝ)]]
theorem cell2_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_5_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_5_4_g]
def cell2_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(4350617375000000/6059221281:ℝ), (8609488243060000/6059221281:ℝ), (4244379987500000/6059221281:ℝ)],
  ![(8742575100700000/6059221281:ℝ), (40231604564248270000/14099807920887:ℝ), (19822213224631250000/14099807920887:ℝ)],
  ![(4373844125000000/6059221281:ℝ), (20115551572287500000/14099807920887:ℝ), (9905917492187500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 5 4 b ν := by
 have heq : pairedCleared cell2 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_5_4_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_5_4_g]
theorem cell2_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_5_4 hb hν
def cell2_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(724027266372/76247581253:ℝ)]]
theorem cell2_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 5 5) := by
 have heq : (-orderedLow cell2 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_5_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_5_5_g]
def cell2_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(19050707042694830960/5935187972314773:ℝ), (38550289757699473000/5935187972314773:ℝ), (19618286474450937500/5935187972314773:ℝ)]]
theorem cell2_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 5 5 ν := by
 have heq : mixedLowHigh cell2 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_5_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_5_5_g]
def cell2_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(77483440/25947:ℝ), (157277000/25947:ℝ), (80312500/25947:ℝ)]]
theorem cell2_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 5 false ν := by
 have heq : naturalFloor cell2 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_5_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_5_5_g]
def cell2_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(26757788033680/8753142609:ℝ), (54257781119000/8753142609:ℝ), (27675055937500/8753142609:ℝ)]]
theorem cell2_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 5 true ν := by
 have heq : naturalFloor cell2 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_5_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_5_5_g]
def cell2_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(77483440/25947:ℝ), (157277000/25947:ℝ), (80312500/25947:ℝ)]]
theorem cell2_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_5_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_5_5_g]
def cell2_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(1766076650000000/2019740427:ℝ), (3526997454400000/2019740427:ℝ), (1754882937500000/2019740427:ℝ)],
  ![(3526997454400000/2019740427:ℝ), (16377319971540100000/4699935973629:ℝ), (8142738945031250000/4699935973629:ℝ)],
  ![(1754882937500000/2019740427:ℝ), (8142738945031250000/4699935973629:ℝ), (4045918515625000000/4699935973629:ℝ)]]
theorem cell2_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 5 5 b ν := by
 have heq : pairedCleared cell2 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_5_5_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_5_5_g]
theorem cell2_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_5_5 hb hν
def cell2_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(47128456678813553/4765473828312500:ℝ)]]
theorem cell2_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 5 6) := by
 have heq : (-orderedLow cell2 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_5_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_5_6_g]
def cell2_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(513018921070599955786/148379699307869325:ℝ), (1043011232845229600111/148379699307869325:ℝ), (21342136982320740325/5935187972314773:ℝ)]]
theorem cell2_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 5 6 ν := by
 have heq : mixedLowHigh cell2 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_5_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_5_6_g]
def cell2_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(241708384/77841:ℝ), (493965200/77841:ℝ), (254125000/77841:ℝ)]]
theorem cell2_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 6 false ν := by
 have heq : naturalFloor cell2 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_5_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_5_6_g]
def cell2_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(892743602336/282359439:ℝ), (1822792850800/282359439:ℝ), (936825875000/282359439:ℝ)]]
theorem cell2_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 5 6 true ν := by
 have heq : naturalFloor cell2 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_5_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_5_6_g]
def cell2_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(241708384/77841:ℝ), (493965200/77841:ℝ), (254125000/77841:ℝ)]]
theorem cell2_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_5_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_5_6_g]
def cell2_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(625206725000000/673246809:ℝ), (1253220359260000/673246809:ℝ), (625598487500000/673246809:ℝ)],
  ![(3715298791900000/2019740427:ℝ), (17318344352414110000/4699935973629:ℝ), (8640134523518750000/4699935973629:ℝ)],
  ![(1833640750000000/2019740427:ℝ), (8542355074300000000/4699935973629:ℝ), (4259623648437500000/4699935973629:ℝ)]]
theorem cell2_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 5 6 b ν := by
 have heq : pairedCleared cell2 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_5_6_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_5_6_g]
theorem cell2_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_5_6 hb hν
def cell2_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(29465213190665917/4765473828312500:ℝ)]]
theorem cell2_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 6 1) := by
 have heq : (-orderedLow cell2 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_6_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_6_1_g]
def cell2_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(27369224404627856024/16486633256429925:ℝ), (163928587178823893972/49459899769289775:ℝ), (3280750142560699400/1978395990771591:ℝ)]]
theorem cell2_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 6 1 ν := by
 have heq : mixedLowHigh cell2 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_6_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_6_1_g]
def cell2_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(115638064/77841:ℝ), (231639200/77841:ℝ), (116312500/77841:ℝ)]]
theorem cell2_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 1 false ν := by
 have heq : naturalFloor cell2 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_6_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_6_1_g]
def cell2_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(12508199058736/8753142609:ℝ), (25086910800800/8753142609:ℝ), (12613724312500/8753142609:ℝ)]]
theorem cell2_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 1 true ν := by
 have heq : naturalFloor cell2 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_6_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_6_1_g]
def cell2_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(23032688/25947:ℝ), (47116400/25947:ℝ), (2687500/2883:ℝ)]]
theorem cell2_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_6_1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_6_1_g]
def cell2_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(1836410225000000/6059221281:ℝ), (3695817395140000/6059221281:ℝ), (1855784450000000/6059221281:ℝ)],
  ![(3489376683340000/6059221281:ℝ), (16353611655754210000/14099807920887:ℝ), (8217477343550000000/14099807920887:ℝ)],
  ![(1631230137500000/6059221281:ℝ), (7655315956831250000/14099807920887:ℝ), (3851518726562500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 6 1 b ν := by
 have heq : pairedCleared cell2 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_6_1_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_6_1_g]
theorem cell2_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_6_1 hb hν
def cell2_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(13138814766267201/2382736914156250:ℝ)]]
theorem cell2_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 6 2) := by
 have heq : (-orderedLow cell2 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_6_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_6_2_g]
def cell2_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(8921211071355776084/5935187972314773:ℝ), (18420121605280039150/5935187972314773:ℝ), (9546392037702781250/5935187972314773:ℝ)]]
theorem cell2_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 6 2 ν := by
 have heq : mixedLowHigh cell2 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_6_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_6_2_g]
def cell2_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(46065376/25947:ℝ), (94232800/25947:ℝ), (5375000/2883:ℝ)]]
theorem cell2_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 2 false ν := by
 have heq : naturalFloor cell2 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_6_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_6_2_g]
def cell2_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(15292423597472/8753142609:ℝ), (31308809581600/8753142609:ℝ), (16086411125000/8753142609:ℝ)]]
theorem cell2_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 2 true ν := by
 have heq : naturalFloor cell2 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_6_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_6_2_g]
def cell2_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(333143384/233523:ℝ), (690087700/233523:ℝ), (358812500/233523:ℝ)]]
theorem cell2_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_6_2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_6_2_g]
def cell2_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(1933504300000000/6059221281:ℝ), (4017271765280000/6059221281:ℝ), (2076522025000000/6059221281:ℝ)],
  ![(4113681695840000/6059221281:ℝ), (19772857253501240000/14099807920887:ℝ), (10167610407137500000/14099807920887:ℝ)],
  ![(2158441075000000/6059221281:ℝ), (10326537235262500000/14099807920887:ℝ), (5287995453125000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 6 2 b ν := by
 have heq : pairedCleared cell2 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_6_2_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_6_2_g]
theorem cell2_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_6_2 hb hν
def cell2_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(5935866737631591/953094765662500:ℝ)]]
theorem cell2_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 6 3) := by
 have heq : (-orderedLow cell2 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_6_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_6_3_g]
def cell2_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(11669486815271454376/5935187972314773:ℝ), (24308174309548552100/5935187972314773:ℝ), (12709909749944875000/5935187972314773:ℝ)]]
theorem cell2_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 6 3 ν := by
 have heq : mixedLowHigh cell2 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_6_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_6_3_g]
def cell2_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(160754192/77841:ℝ), (333757600/77841:ℝ), (173937500/77841:ℝ)]]
theorem cell2_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 3 false ν := by
 have heq : naturalFloor cell2 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_6_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_6_3_g]
def cell2_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(160754192/77841:ℝ), (333757600/77841:ℝ), (173937500/77841:ℝ)]]
theorem cell2_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 3 true ν := by
 have heq : naturalFloor cell2 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_6_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_6_3_g]
def cell2_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(458992576/233523:ℝ), (956127800/233523:ℝ), (499937500/233523:ℝ)]]
theorem cell2_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_6_3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_6_3_g]
def cell2_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(2881116875000000/6059221281:ℝ), (5988775885420000/6059221281:ℝ), (3096790850000000/6059221281:ℝ)],
  ![(5952098958340000/6059221281:ℝ), (28673212603873270000/14099807920887:ℝ), (14773614017600000000/14099807920887:ℝ)],
  ![(3049245762500000/6059221281:ℝ), (14639202498068750000/14099807920887:ℝ), (7519833507812500000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 6 3 b ν := by
 have heq : pairedCleared cell2 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_6_3_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_6_3_g]
theorem cell2_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_6_3 hb hν
def cell2_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(8270259460945377/1191368457078125:ℝ)]]
theorem cell2_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 6 4) := by
 have heq : (-orderedLow cell2 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_6_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_6_4_g]
def cell2_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(4805920853062377556/1978395990771591:ℝ), (10065409004605688350/1978395990771591:ℝ), (1763714162465218750/659465330257197:ℝ)]]
theorem cell2_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 6 4 ν := by
 have heq : mixedLowHigh cell2 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_6_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_6_4_g]
def cell2_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(183312256/77841:ℝ), (384816800/77841:ℝ), (202750000/77841:ℝ)]]
theorem cell2_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 4 false ν := by
 have heq : naturalFloor cell2 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_6_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_6_4_g]
def cell2_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(20860872674944/8753142609:ℝ), (43752607143200/8753142609:ℝ), (23031784750000/8753142609:ℝ)]]
theorem cell2_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 4 true ν := by
 have heq : naturalFloor cell2 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_6_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_6_4_g]
def cell2_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(183312256/77841:ℝ), (384816800/77841:ℝ), (202750000/77841:ℝ)]]
theorem cell2_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_6_4_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_6_4_g]
def cell2_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(1276243150000000/2019740427:ℝ), (2653426668520000/2019740427:ℝ), (457451075000000/673246809:ℝ)],
  ![(2596838740280000/2019740427:ℝ), (12524522651415100000/4699935973629:ℝ), (2153290847562500000/1566645324543:ℝ)],
  ![(1313350150000000/2019740427:ℝ), (6317289253625000000/4699935973629:ℝ), (1083519062500000000/1566645324543:ℝ)]]
theorem cell2_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 6 4 b ν := by
 have heq : pairedCleared cell2 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_6_4_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_6_4_g]
theorem cell2_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_6_4 hb hν
def cell2_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(49661317626915197/4765473828312500:ℝ)]]
theorem cell2_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 6 5) := by
 have heq : (-orderedLow cell2 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_6_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_6_5_g]
def cell2_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(19952887397899960960/5935187972314773:ℝ), (40062497269960853000/5935187972314773:ℝ), (20228313631507187500/5935187972314773:ℝ)]]
theorem cell2_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 6 5 ν := by
 have heq : mixedLowHigh cell2 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_6_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_6_5_g]
def cell2_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(242420320/77841:ℝ), (488051000/77841:ℝ), (247187500/77841:ℝ)]]
theorem cell2_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 5 false ν := by
 have heq : naturalFloor cell2 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_6_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_6_5_g]
def cell2_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(27755108163680/8753142609:ℝ), (55841532499000/8753142609:ℝ), (28261487187500/8753142609:ℝ)]]
theorem cell2_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 5 true ν := by
 have heq : naturalFloor cell2 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_6_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_6_5_g]
def cell2_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(242420320/77841:ℝ), (488051000/77841:ℝ), (247187500/77841:ℝ)]]
theorem cell2_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_6_5_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_6_5_g]
def cell2_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(625206725000000/673246809:ℝ), (3715298791900000/2019740427:ℝ), (1833640750000000/2019740427:ℝ)],
  ![(1253220359260000/673246809:ℝ), (17318344352414110000/4699935973629:ℝ), (8542355074300000000/4699935973629:ℝ)],
  ![(625598487500000/673246809:ℝ), (8640134523518750000/4699935973629:ℝ), (4259623648437500000/4699935973629:ℝ)]]
theorem cell2_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 6 5 b ν := by
 have heq : pairedCleared cell2 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_6_5_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_6_5_g]
theorem cell2_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_6_5 hb hν
def cell2_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(4496658760738/381237906265:ℝ)]]
theorem cell2_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell2 6 6) := by
 have heq : (-orderedLow cell2 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell2_ordered_6_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_ordered_6_6_g]
def cell2_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(23570560937536721152/5935187972314773:ℝ), (47637226531506041600/5935187972314773:ℝ), (24209110105304875000/5935187972314773:ℝ)]]
theorem cell2_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell2 6 6 ν := by
 have heq : mixedLowHigh cell2 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_mixed_6_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_mixed_6_6_g]
def cell2_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(288248384/77841:ℝ), (584255200/77841:ℝ), (297875000/77841:ℝ)]]
theorem cell2_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 6 false ν := by
 have heq : naturalFloor cell2 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor0_6_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor0_6_6_g]
def cell2_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(3833509184/1012041:ℝ), (240644951200/31373271:ℝ), (122559125000/31373271:ℝ)]]
theorem cell2_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell2 6 6 true ν := by
 have heq : naturalFloor cell2 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_floor1_6_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_floor1_6_6_g]
def cell2_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(288248384/77841:ℝ), (584255200/77841:ℝ), (297875000/77841:ℝ)]]
theorem cell2_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell2_complement_floor_6_6_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_complement_floor_6_6_g]
def cell2_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(6574473100000000/6059221281:ℝ), (13117400495840000/6059221281:ℝ), (6521191075000000/6059221281:ℝ)],
  ![(13117400495840000/6059221281:ℝ), (60855388407614360000/14099807920887:ℝ), (30233068833362500000/14099807920887:ℝ)],
  ![(6521191075000000/6059221281:ℝ), (30233068833362500000/14099807920887:ℝ), (15010709000000000000/14099807920887:ℝ)]]
theorem cell2_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell2 6 6 b ν := by
 have heq : pairedCleared cell2 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell2_paired_cleared_6_6_g (399/625:ℝ) (3/4:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_cleared_6_6_g]
theorem cell2_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) : 0 ≤ pairedGap cell2 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell2_paired_cleared_6_6 hb hν
def cell2_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(3093284026393947/4765473828312500:ℝ)]]
theorem cell2_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell2.q/K)+1+17/50*(cell2.q/cell2.priorL)+17/25*(cell2.q/cell2.priorL)*cell2.priorB) := by
 have heq : ((2-17/50-17/25)*(cell2.q/K)+1+17/50*(cell2.q/cell2.priorL)+17/25*(cell2.q/cell2.priorL)*cell2.priorB) = Record12518109.Bernstein.bsum 0 0 (3093284026393947/4765473828312500:ℝ) cell2_increment0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_increment0_g]
def cell2_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(63628342291/127136937500:ℝ)]]
theorem cell2_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell2.q/cell2.priorL)*(1-cell2.priorB)) := by
 have heq : (1+17/25*(cell2.q/cell2.priorL)*(1-cell2.priorB)) = Record12518109.Bernstein.bsum 0 0 (63628342291/127136937500:ℝ) cell2_increment1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_increment1_g]
def cell2_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(254453495623/508547750000:ℝ)]]
theorem cell2_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell2.q/cell2.priorL)*(1-cell2.priorB)) := by
 have heq : (1+omega*(cell2.q/cell2.priorL)*(1-cell2.priorB)) = Record12518109.Bernstein.bsum 0 0 (254453495623/508547750000:ℝ) cell2_increment2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_increment2_g]
def cell2_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(9639514/77841:ℝ), (19177100/77841:ℝ), (9848950/77841:ℝ)]]
theorem cell2_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (191771/125000:ℝ) cell2_high_increment_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_high_increment_g]
def cell2_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(31600547728/2413071:ℝ), (244694463616/2413071:ℝ), (406946981816/2413071:ℝ), (185079139772/2413071:ℝ)]]
theorem cell2_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (17775308097/976562500:ℝ) cell2_three_gate0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_three_gate0_g]
def cell2_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(4629032/77841:ℝ), (12876136/77841:ℝ), (8558468/77841:ℝ)]]
theorem cell2_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (578629/781250:ℝ) cell2_three_gate1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_three_gate1_g]
def cell2_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(1020200159786/8753142609:ℝ), (2036360017900/8753142609:ℝ), (1051172428550/8753142609:ℝ)]]
theorem cell2_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell2.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell2.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (20363600179/14056125000:ℝ) cell2_three_gate2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_three_gate2_g]
def cell2_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(107129/224898:ℝ)]]
theorem cell2_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (1-cell2.q/K/3) := by
 have heq : (1-cell2.q/K/3) = Record12518109.Bernstein.bsum 0 0 (107129/224898:ℝ) cell2_paired_margin0_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_margin0_g]
def cell2_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(1163217/11635000:ℝ)]]
theorem cell2_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (gamma cell2-13/50) := by
 have heq : (gamma cell2-13/50) = Record12518109.Bernstein.bsum 0 0 (1163217/11635000:ℝ) cell2_paired_margin1_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_margin1_g]
def cell2_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(1661/18616:ℝ)]]
theorem cell2_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (cell2.q-gamma cell2) := by
 have heq : (cell2.q-gamma cell2) = Record12518109.Bernstein.bsum 0 0 (1661/18616:ℝ) cell2_paired_margin2_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_margin2_g]
def cell2_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(11723253/40722500:ℝ)]]
theorem cell2_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4:ℝ)) : 0 < (min (cell2.q+rho cell2.q) (3/4+rho (3/4))-gamma cell2) := by
 have heq : (min (cell2.q+rho cell2.q) (3/4+rho (3/4))-gamma cell2) = Record12518109.Bernstein.bsum 0 0 (11723253/40722500:ℝ) cell2_paired_margin3_g (17/500:ℝ) (9/250:ℝ) (399/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell2, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell2_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell2_paired_margin3_g]
theorem cell2_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (399/625:ℝ) (3/4)) (hν : ν ∈ Set.Icc (399/625:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell2 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell2_paired_1_1 hb hν
 · exact cell2_paired_1_2 hb hν
 · exact cell2_paired_1_3 hb hν
 · exact cell2_paired_1_4 hb hν
 · exact cell2_paired_1_5 hb hν
 · exact cell2_paired_1_6 hb hν
 · exact cell2_paired_2_1 hb hν
 · exact cell2_paired_2_2 hb hν
 · exact cell2_paired_2_3 hb hν
 · exact cell2_paired_2_4 hb hν
 · exact cell2_paired_2_5 hb hν
 · exact cell2_paired_2_6 hb hν
 · exact cell2_paired_3_1 hb hν
 · exact cell2_paired_3_2 hb hν
 · exact cell2_paired_3_3 hb hν
 · exact cell2_paired_3_4 hb hν
 · exact cell2_paired_3_5 hb hν
 · exact cell2_paired_3_6 hb hν
 · exact cell2_paired_4_1 hb hν
 · exact cell2_paired_4_2 hb hν
 · exact cell2_paired_4_3 hb hν
 · exact cell2_paired_4_4 hb hν
 · exact cell2_paired_4_5 hb hν
 · exact cell2_paired_4_6 hb hν
 · exact cell2_paired_5_1 hb hν
 · exact cell2_paired_5_2 hb hν
 · exact cell2_paired_5_3 hb hν
 · exact cell2_paired_5_4 hb hν
 · exact cell2_paired_5_5 hb hν
 · exact cell2_paired_5_6 hb hν
 · exact cell2_paired_6_1 hb hν
 · exact cell2_paired_6_2 hb hν
 · exact cell2_paired_6_3 hb hν
 · exact cell2_paired_6_4 hb hν
 · exact cell2_paired_6_5 hb hν
 · exact cell2_paired_6_6 hb hν
end
end Record12518109Admission
