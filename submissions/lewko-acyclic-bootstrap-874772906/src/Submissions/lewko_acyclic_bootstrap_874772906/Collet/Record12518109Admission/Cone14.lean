/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell14
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell14_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(223162645899/762475812530:ℝ)]]
theorem cell14_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 1 1) := by
 have heq : (-orderedLow cell14 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_1_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_1_1_g]
def cell14_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(339538056466151968/2725012306400967:ℝ), (71185244351652100/247728391490997:ℝ), (454399680627625000/2725012306400967:ℝ)]]
theorem cell14_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 1 1 ν := by
 have heq : mixedLowHigh cell14 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_1_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_1_1_g]
def cell14_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(35261716/393129:ℝ), (86439200/393129:ℝ), (52750000/393129:ℝ)]]
theorem cell14_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 1 false ν := by
 have heq : naturalFloor cell14 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_1_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_1_1_g]
def cell14_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(494801950276/4911884769:ℝ), (1184834661200/4911884769:ℝ), (709680250000/4911884769:ℝ)]]
theorem cell14_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 1 true ν := by
 have heq : naturalFloor cell14 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_1_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_1_1_g]
def cell14_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(35261716/393129:ℝ), (86439200/393129:ℝ), (52750000/393129:ℝ)]]
theorem cell14_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_1_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_1_1_g]
def cell14_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(1142587450000000/51516803547:ℝ), (858771509740000/17172267849:ℝ), (1409151275000000/51516803547:ℝ)],
  ![(858771509740000/17172267849:ℝ), (53363243423691880000/483073066860219:ℝ), (28759656480100000000/483073066860219:ℝ)],
  ![(1409151275000000/51516803547:ℝ), (28759656480100000000/483073066860219:ℝ), (567815062500000000/17891595068897:ℝ)]]
theorem cell14_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 1 1 b ν := by
 have heq : pairedCleared cell14 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_1_1_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_1_1_g]
theorem cell14_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_1_1 hb hν
def cell14_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(26127796878815131/38123790626500000:ℝ)]]
theorem cell14_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 1 2) := by
 have heq : (-orderedLow cell14 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_1_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_1_2_g]
def cell14_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(951503612128812179761/2997513537041063700:ℝ), (2118047316426405858911/2997513537041063700:ℝ), (23810476251878443775/59950270740821274:ℝ)]]
theorem cell14_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 1 2 ν := by
 have heq : mixedLowHigh cell14 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_1_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_1_2_g]
def cell14_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(70523432/393129:ℝ), (172878400/393129:ℝ), (105500000/393129:ℝ)]]
theorem cell14_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 2 false ν := by
 have heq : naturalFloor cell14 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_1_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_1_2_g]
def cell14_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(70523432/393129:ℝ), (172878400/393129:ℝ), (105500000/393129:ℝ)]]
theorem cell14_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 2 true ν := by
 have heq : naturalFloor cell14 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_1_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_1_2_g]
def cell14_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(70523432/393129:ℝ), (172878400/393129:ℝ), (105500000/393129:ℝ)]]
theorem cell14_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_1_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_1_2_g]
def cell14_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(823066175000000/14050037331:ℝ), (1791573559120000/14050037331:ℝ), (955102400000000/14050037331:ℝ)],
  ![(15884701940000/141919569:ℝ), (10713429365921620000/43915733350929:ℝ), (5717053930525000000/43915733350929:ℝ)],
  ![(742816825000000/14050037331:ℝ), (15219206760325000000/131747200052787:ℝ), (8136519781250000000/131747200052787:ℝ)]]
theorem cell14_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 1 2 b ν := by
 have heq : pairedCleared cell14 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_1_2_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_1_2_g]
theorem cell14_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_1_2 hb hν
def cell14_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(80323802244869/9530947656625000:ℝ)]]
theorem cell14_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 1 3) := by
 have heq : (-orderedLow cell14 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_1_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_1_3_g]
def cell14_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(1090380998486041771/83264264917807325:ℝ), (13718814571561555121/83264264917807325:ℝ), (545104190083568050/3330570596712293:ℝ)]]
theorem cell14_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 1 3 ν := by
 have heq : mixedLowHigh cell14 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_1_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_1_3_g]
def cell14_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(35261716/131043:ℝ), (86439200/131043:ℝ), (52750000/131043:ℝ)]]
theorem cell14_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 3 false ν := by
 have heq : naturalFloor cell14 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_1_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_1_3_g]
def cell14_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(3802453752484/14735654307:ℝ), (9405498150800/14735654307:ℝ), (5779872250000/14735654307:ℝ)]]
theorem cell14_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 3 true ν := by
 have heq : naturalFloor cell14 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_1_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_1_3_g]
def cell14_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(35261716/131043:ℝ), (86439200/131043:ℝ), (52750000/131043:ℝ)]]
theorem cell14_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_1_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_1_3_g]
def cell14_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (1758562580000/82163961:ℝ), (1640975000000/82163961:ℝ)],
  ![(30275687740000/739475649:ℝ), (835704566651920000/6934063160673:ℝ), (532625852150000000/6934063160673:ℝ)],
  ![(29922925000000/739475649:ℝ), (680899664650000000/6934063160673:ℝ), (391052375000000000/6934063160673:ℝ)]]
theorem cell14_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 1 3 b ν := by
 have heq : pairedCleared cell14 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_1_3_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_1_3_g]
theorem cell14_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_1_3 hb hν
def cell14_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(27490572793324607/38123790626500000:ℝ)]]
theorem cell14_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 1 4) := by
 have heq : (-orderedLow cell14 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_1_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_1_4_g]
def cell14_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(617265465961542518717/2997513537041063700:ℝ), (1750583184347631433267/2997513537041063700:ℝ), (23625558699574918675/59950270740821274:ℝ)]]
theorem cell14_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 1 4 ν := by
 have heq : mixedLowHigh cell14 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_1_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_1_4_g]
def cell14_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(141046864/393129:ℝ), (345756800/393129:ℝ), (211000000/393129:ℝ)]]
theorem cell14_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 4 false ν := by
 have heq : naturalFloor cell14 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_1_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_1_4_g]
def cell14_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(551275300368/1637294923:ℝ), (1370110581600/1637294923:ℝ), (845032000000/1637294923:ℝ)]]
theorem cell14_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 4 true ν := by
 have heq : naturalFloor cell14 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_1_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_1_4_g]
def cell14_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(141046864/393129:ℝ), (345756800/393129:ℝ), (211000000/393129:ℝ)]]
theorem cell14_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_1_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_1_4_g]
def cell14_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(5625965575000000/154550410641:ℝ), (15286221775640000/154550410641:ℝ), (9365346550000000/154550410641:ℝ)],
  ![(15897115562660000/154550410641:ℝ), (368115693234589100000/1449219200580657:ℝ), (213702613366375000000/1449219200580657:ℝ)],
  ![(10197422575000000/154550410641:ℝ), (223440334835125000000/1449219200580657:ℝ), (125238643906250000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 1 4 b ν := by
 have heq : pairedCleared cell14 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_1_4_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_1_4_g]
theorem cell14_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_1_4 hb hν
def cell14_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(27329925188834869/19061895313250000:ℝ)]]
theorem cell14_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 1 5) := by
 have heq : (-orderedLow cell14 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_1_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_1_5_g]
def cell14_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(597638607988793766839/1498756768520531850:ℝ), (1503644522059523441089/1498756768520531850:ℝ), (18719620988822806225/29975135370410637:ℝ)]]
theorem cell14_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 1 5 ν := by
 have heq : mixedLowHigh cell14 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_1_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_1_5_g]
def cell14_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(176308580/393129:ℝ), (432196000/393129:ℝ), (263750000/393129:ℝ)]]
theorem cell14_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 5 false ν := by
 have heq : naturalFloor cell14 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_1_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_1_5_g]
def cell14_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(6120501654140/14735654307:ℝ), (15256492318000/14735654307:ℝ), (9430703750000/14735654307:ℝ)]]
theorem cell14_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 5 true ν := by
 have heq : naturalFloor cell14 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_1_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_1_5_g]
def cell14_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(176308580/393129:ℝ), (432196000/393129:ℝ), (263750000/393129:ℝ)]]
theorem cell14_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_1_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_1_5_g]
def cell14_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(11251931150000000/154550410641:ℝ), (27264587338300000/154550410641:ℝ), (15644019125000000/154550410641:ℝ)],
  ![(25466612387660000/154550410641:ℝ), (561569132038926920000/1449219200580657:ℝ), (316086423633400000000/1449219200580657:ℝ)],
  ![(4713651275000000/51516803547:ℝ), (3760156046400000000/17891595068897:ℝ), (56249113812500000000/483073066860219:ℝ)]]
theorem cell14_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 1 5 b ν := by
 have heq : pairedCleared cell14 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_1_5_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_1_5_g]
theorem cell14_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_1_5 hb hν
def cell14_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(187780686470376441/38123790626500000:ℝ)]]
theorem cell14_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 1 6) := by
 have heq : (-orderedLow cell14 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_1_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_1_6_g]
def cell14_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(2966944850509347548639/2997513537041063700:ℝ), (5934198171237427331089/2997513537041063700:ℝ), (60783872912341306225/59950270740821274:ℝ)]]
theorem cell14_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 1 6 ν := by
 have heq : mixedLowHigh cell14 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_1_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_1_6_g]
def cell14_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(368120296/393129:ℝ), (737685200/393129:ℝ), (379000000/393129:ℝ)]]
theorem cell14_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 6 false ν := by
 have heq : naturalFloor cell14 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_1_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_1_6_g]
def cell14_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(13147489254968/14735654307:ℝ), (26392640551600/14735654307:ℝ), (13598807000000/14735654307:ℝ)]]
theorem cell14_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 1 6 true ν := by
 have heq : naturalFloor cell14 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_1_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_1_6_g]
def cell14_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(368120296/393129:ℝ), (737685200/393129:ℝ), (379000000/393129:ℝ)]]
theorem cell14_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_1_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_1_6_g]
def cell14_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(31557590225000000/154550410641:ℝ), (59783271400960000/154550410641:ℝ), (27783316700000000/154550410641:ℝ)],
  ![(21137975904220000/51516803547:ℝ), (125261880476973860000/161024355620073:ℝ), (174901927758475000000/483073066860219:ℝ)],
  ![(31782610075000000/154550410641:ℝ), (565432731556675000000/1449219200580657:ℝ), (263536507718750000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 1 6 b ν := by
 have heq : pairedCleared cell14 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_1_6_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_1_6_g]
theorem cell14_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_1_6 hb hν
def cell14_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(46232866445064869/38123790626500000:ℝ)]]
theorem cell14_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 2 1) := by
 have heq : (-orderedLow cell14 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_2_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_2_1_g]
def cell14_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(2491925803627087216/9991711790136879:ℝ), (14782840500290994100/29975135370410637:ℝ), (7426963630891375000/29975135370410637:ℝ)]]
theorem cell14_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 2 1 ν := by
 have heq : mixedLowHigh cell14 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_2_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_2_1_g]
def cell14_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(8553524/43681:ℝ), (153159200/393129:ℝ), (77750000/393129:ℝ)]]
theorem cell14_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 1 false ν := by
 have heq : naturalFloor cell14 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_2_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_2_1_g]
def cell14_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(8553524/43681:ℝ), (153159200/393129:ℝ), (77750000/393129:ℝ)]]
theorem cell14_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 1 true ν := by
 have heq : naturalFloor cell14 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_2_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_2_1_g]
def cell14_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(8553524/43681:ℝ), (153159200/393129:ℝ), (77750000/393129:ℝ)]]
theorem cell14_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_2_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_2_1_g]
def cell14_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(823066175000000/14050037331:ℝ), (15884701940000/141919569:ℝ), (742816825000000/14050037331:ℝ)],
  ![(1791573559120000/14050037331:ℝ), (10713429365921620000/43915733350929:ℝ), (15219206760325000000/131747200052787:ℝ)],
  ![(955102400000000/14050037331:ℝ), (5717053930525000000/43915733350929:ℝ), (8136519781250000000/131747200052787:ℝ)]]
theorem cell14_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 2 1 b ν := by
 have heq : pairedCleared cell14 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_2_1_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_2_1_g]
theorem cell14_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_2_1 hb hν
def cell14_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(985638458429/381237906265:ℝ)]]
theorem cell14_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 2 2) := by
 have heq : (-orderedLow cell14 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_2_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_2_2_g]
def cell14_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(2418812070049218144/3330570596712293:ℝ), (4985514137840269800/3330570596712293:ℝ), (2593346632564750000/3330570596712293:ℝ)]]
theorem cell14_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 2 2 ν := by
 have heq : mixedLowHigh cell14 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_2_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_2_2_g]
def cell14_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(7820104/11913:ℝ), (16224800/11913:ℝ), (8500000/11913:ℝ)]]
theorem cell14_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 2 false ν := by
 have heq : naturalFloor cell14 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_2_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_2_2_g]
def cell14_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(9998373521656/14735654307:ℝ), (20698094787200/14735654307:ℝ), (10817606500000/14735654307:ℝ)]]
theorem cell14_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 2 true ν := by
 have heq : naturalFloor cell14 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_2_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_2_2_g]
def cell14_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(7820104/11913:ℝ), (16224800/11913:ℝ), (8500000/11913:ℝ)]]
theorem cell14_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_2_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_2_2_g]
def cell14_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(24441150500000000/154550410641:ℝ), (49453262975320000/154550410641:ℝ), (24864657650000000/154550410641:ℝ)],
  ![(49453262975320000/154550410641:ℝ), (936413637668751280000/1449219200580657:ℝ), (470017477130600000000/1449219200580657:ℝ)],
  ![(24864657650000000/154550410641:ℝ), (470017477130600000000/1449219200580657:ℝ), (235571352625000000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 2 2 b ν := by
 have heq : pairedCleared cell14 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_2_2_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_2_2_g]
theorem cell14_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_2_2 hb hν
def cell14_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(113533510426765131/38123790626500000:ℝ)]]
theorem cell14_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 2 3) := by
 have heq : (-orderedLow cell14 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_2_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_2_3_g]
def cell14_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(2754942613060341344561/2997513537041063700:ℝ), (5743668583827658268911/2997513537041063700:ℝ), (60493922664236193775/59950270740821274:ℝ)]]
theorem cell14_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 2 3 ν := by
 have heq : mixedLowHigh cell14 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_2_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_2_3_g]
def cell14_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(293325148/393129:ℝ), (621857600/393129:ℝ), (333250000/393129:ℝ)]]
theorem cell14_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 3 false ν := by
 have heq : naturalFloor cell14 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_2_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_2_3_g]
def cell14_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(1239710830276/1637294923:ℝ), (2624843541200/1637294923:ℝ), (1404780250000/1637294923:ℝ)]]
theorem cell14_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 3 true ν := by
 have heq : naturalFloor cell14 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_2_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_2_3_g]
def cell14_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(293325148/393129:ℝ), (621857600/393129:ℝ), (333250000/393129:ℝ)]]
theorem cell14_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_2_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_2_3_g]
def cell14_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(3340790675000000/17172267849:ℝ), (6825736504220000/17172267849:ℝ), (1153456675000000/5724089283:ℝ)],
  ![(59022759800320000/154550410641:ℝ), (1129867076473089100000/1449219200580657:ℝ), (572401287397625000000/1449219200580657:ℝ)],
  ![(28808188900000000/154550410641:ℝ), (551149782053875000000/1449219200580657:ℝ), (279080050156250000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 2 3 b ν := by
 have heq : pairedCleared cell14 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_2_3_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_2_3_g]
theorem cell14_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_2_3 hb hν
def cell14_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(21931752189232369/9530947656625000:ℝ)]]
theorem cell14_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 2 4) := by
 have heq : (-orderedLow cell14 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_2_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_2_4_g]
def cell14_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(460673179219256667139/749378384260265925:ℝ), (1029874647994367098589/749378384260265925:ℝ), (23247660916930987450/29975135370410637:ℝ)]]
theorem cell14_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 2 4 ν := by
 have heq : mixedLowHigh cell14 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_2_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_2_4_g]
def cell14_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(328586864/393129:ℝ), (708296800/393129:ℝ), (386000000/393129:ℝ)]]
theorem cell14_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 4 false ν := by
 have heq : naturalFloor cell14 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_2_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_2_4_g]
def cell14_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(328586864/393129:ℝ), (708296800/393129:ℝ), (386000000/393129:ℝ)]]
theorem cell14_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 4 true ν := by
 have heq : naturalFloor cell14 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_2_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_2_4_g]
def cell14_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(328586864/393129:ℝ), (708296800/393129:ℝ), (386000000/393129:ℝ)]]
theorem cell14_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_2_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_2_4_g]
def cell14_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(21013388150000000/154550410641:ℝ), (45032175600640000/154550410641:ℝ), (23723877800000000/154550410641:ℝ)],
  ![(16017312708440000/51516803547:ℝ), (105665129091991880000/161024355620073:ℝ), (165019103596550000000/483073066860219:ℝ)],
  ![(26891095150000000/154550410641:ℝ), (526046537602150000000/1449219200580657:ℝ), (271308278937500000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 2 4 b ν := by
 have heq : pairedCleared cell14 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_2_4_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_2_4_g]
theorem cell14_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_2_4 hb hν
def cell14_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(114896286341274607/38123790626500000:ℝ)]]
theorem cell14_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 2 5) := by
 have heq : (-orderedLow cell14 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_2_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_2_5_g]
def cell14_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(806901488964357227839/999171179013687900:ℝ), (1792068150582961281089/999171179013687900:ℝ), (20103001703977556225/19983423580273758:ℝ)]]
theorem cell14_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 2 5 ν := by
 have heq : mixedLowHigh cell14 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_2_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_2_5_g]
def cell14_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(40427620/43681:ℝ), (88304000/43681:ℝ), (48750000/43681:ℝ)]]
theorem cell14_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 5 false ν := by
 have heq : naturalFloor cell14 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_2_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_2_5_g]
def cell14_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(709233967060/775560753:ℝ), (1551294002000/775560753:ℝ), (857571250000/775560753:ℝ)]]
theorem cell14_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 5 true ν := by
 have heq : naturalFloor cell14 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_2_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_2_5_g]
def cell14_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(40427620/43681:ℝ), (88304000/43681:ℝ), (48750000/43681:ℝ)]]
theorem cell14_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_2_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_2_5_g]
def cell14_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(8879784575000000/51516803547:ℝ), (6334504573700000/17172267849:ℝ), (10000850125000000/51516803547:ℝ)],
  ![(19207144983440000/51516803547:ℝ), (381479866877421580000/483073066860219:ℝ), (22127448928025000000/53674785206691:ℝ)],
  ![(380674400000000/1908029761:ℝ), (202392947508475000000/483073066860219:ℝ), (104938992156250000000/483073066860219:ℝ)]]
theorem cell14_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 2 5 b ν := by
 have heq : pairedCleared cell14 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_2_5_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_2_5_g]
theorem cell14_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_2_5 hb hν
def cell14_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(71032781962809869/19061895313250000:ℝ)]]
theorem cell14_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 2 6) := by
 have heq : (-orderedLow cell14 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_2_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_2_6_g]
def cell14_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(12391389326070730159/12386419574549850:ℝ), (301495923250922695099/136250615320048350:ℝ), (3369213108636516475/2725012306400967:ℝ)]]
theorem cell14_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 2 6 ν := by
 have heq : mixedLowHigh cell14 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_2_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_2_6_g]
def cell14_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(399110296/393129:ℝ), (881175200/393129:ℝ), (491500000/393129:ℝ)]]
theorem cell14_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 6 false ν := by
 have heq : naturalFloor cell14 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_2_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_2_6_g]
def cell14_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(4878156441656/4911884769:ℝ), (10800027707200/4911884769:ℝ), (6039756500000/4911884769:ℝ)]]
theorem cell14_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 2 6 true ν := by
 have heq : naturalFloor cell14 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_2_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_2_6_g]
def cell14_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(399110296/393129:ℝ), (881175200/393129:ℝ), (491500000/393129:ℝ)]]
theorem cell14_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_2_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_2_6_g]
def cell14_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(1698174700000000/8134232139:ℝ), (3630995090840000/8134232139:ℝ), (1909538050000000/8134232139:ℝ)],
  ![(1178788276760000/2711410713:ℝ), (23471807709414080000/25424898255801:ℝ), (12277630374100000000/25424898255801:ℝ)],
  ![(1830429350000000/8134232139:ℝ), (36226902497300000000/76274694767403:ℝ), (18859246000000000000/76274694767403:ℝ)]]
theorem cell14_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 2 6 b ν := by
 have heq : pairedCleared cell14 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_2_6_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_2_6_g]
theorem cell14_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_2_6 hb hν
def cell14_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(258871950154083/19061895313250000:ℝ)]]
theorem cell14_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 3 1) := by
 have heq : (-orderedLow cell14 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_3_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_3_1_g]
def cell14_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(927815948527889516/9991711790136879:ℝ), (11022719296890776000/29975135370410637:ℝ), (8359171992788750000/29975135370410637:ℝ)]]
theorem cell14_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 3 1 ν := by
 have heq : mixedLowHigh cell14 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_3_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_3_1_g]
def cell14_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(6213524/43681:ℝ), (182099200/393129:ℝ), (127750000/393129:ℝ)]]
theorem cell14_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 1 false ν := by
 have heq : naturalFloor cell14 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_3_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_3_1_g]
def cell14_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(1933422730828/14735654307:ℝ), (2170373621200/4911884769:ℝ), (4636640750000/14735654307:ℝ)]]
theorem cell14_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 1 true ν := by
 have heq : naturalFloor cell14 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_3_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_3_1_g]
def cell14_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(9036716/393129:ℝ), (91464200/393129:ℝ), (28000000/131043:ℝ)]]
theorem cell14_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_3_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_3_1_g]
def cell14_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (30275687740000/739475649:ℝ), (29922925000000/739475649:ℝ)],
  ![(1758562580000/82163961:ℝ), (835704566651920000/6934063160673:ℝ), (680899664650000000/6934063160673:ℝ)],
  ![(1640975000000/82163961:ℝ), (532625852150000000/6934063160673:ℝ), (391052375000000000/6934063160673:ℝ)]]
theorem cell14_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 3 1 b ν := by
 have heq : pairedCleared cell14 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_3_1_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_3_1_g]
theorem cell14_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_3_1 hb hν
def cell14_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(133638579993014869/38123790626500000:ℝ)]]
theorem cell14_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 3 2) := by
 have heq : (-orderedLow cell14 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_3_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_3_2_g]
def cell14_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(25510167420196553296/29975135370410637:ℝ), (17013017724767839400/9991711790136879:ℝ), (25768686837070250000/29975135370410637:ℝ)]]
theorem cell14_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 3 2 ν := by
 have heq : mixedLowHigh cell14 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_3_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_3_2_g]
def cell14_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(299783432/393129:ℝ), (200712800/131043:ℝ), (305500000/393129:ℝ)]]
theorem cell14_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 2 false ν := by
 have heq : naturalFloor cell14 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_3_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_3_2_g]
def cell14_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(11399473331656/14735654307:ℝ), (22884457097200/14735654307:ℝ), (3867623000000/4911884769:ℝ)]]
theorem cell14_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 2 true ν := by
 have heq : naturalFloor cell14 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_3_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_3_2_g]
def cell14_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(299783432/393129:ℝ), (200712800/131043:ℝ), (305500000/393129:ℝ)]]
theorem cell14_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_3_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_3_2_g]
def cell14_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(3340790675000000/17172267849:ℝ), (59022759800320000/154550410641:ℝ), (28808188900000000/154550410641:ℝ)],
  ![(6825736504220000/17172267849:ℝ), (1129867076473089100000/1449219200580657:ℝ), (551149782053875000000/1449219200580657:ℝ)],
  ![(1153456675000000/5724089283:ℝ), (572401287397625000000/1449219200580657:ℝ), (279080050156250000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 3 2 b ν := by
 have heq : pairedCleared cell14 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_3_2_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_3_2_g]
theorem cell14_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_3_2 hb hν
def cell14_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(3719391187817/762475812530:ℝ)]]
theorem cell14_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 3 3) := by
 have heq : (-orderedLow cell14 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_3_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_3_3_g]
def cell14_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(39803698639758254944/29975135370410637:ℝ), (81125839914574952300/29975135370410637:ℝ), (41681842899261625000/29975135370410637:ℝ)]]
theorem cell14_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 3 3 ν := by
 have heq : mixedLowHigh cell14 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_3_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_3_3_g]
def cell14_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(25308692/20691:ℝ), (51810400/20691:ℝ), (26750000/20691:ℝ)]]
theorem cell14_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 3 false ν := by
 have heq : naturalFloor cell14 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_3_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_3_3_g]
def cell14_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(18512341192484/14735654307:ℝ), (37841685590800/14735654307:ℝ), (19506172250000/14735654307:ℝ)]]
theorem cell14_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 3 true ν := by
 have heq : naturalFloor cell14 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_3_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_3_3_g]
def cell14_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(25308692/20691:ℝ), (51810400/20691:ℝ), (26750000/20691:ℝ)]]
theorem cell14_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_3_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_3_3_g]
def cell14_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(45454538650000000/154550410641:ℝ), (91177582362980000/154550410641:ℝ), (45501861475000000/154550410641:ℝ)],
  ![(91177582362980000/154550410641:ℝ), (1712737545066426920000/1449219200580657:ℝ), (853755984820900000000/1449219200580657:ℝ)],
  ![(45501861475000000/154550410641:ℝ), (853755984820900000000/1449219200580657:ℝ), (425149685187500000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 3 3 b ν := by
 have heq : pairedCleared cell14 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_3_3_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_3_3_g]
theorem cell14_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_3_3 hb hν
def cell14_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(200939223974715131/38123790626500000:ℝ)]]
theorem cell14_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 3 4) := by
 have heq : (-orderedLow cell14 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_3_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_3_4_g]
def cell14_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(138132776181571833617/90833743546698900:ℝ), (283917874279663959967/90833743546698900:ℝ), (2944768759896786175/1816674870933978:ℝ)]]
theorem cell14_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 3 4 ν := by
 have heq : mixedLowHigh cell14 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_3_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_3_4_g]
def cell14_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(15640208/11913:ℝ), (32449600/11913:ℝ), (17000000/11913:ℝ)]]
theorem cell14_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 4 false ν := by
 have heq : naturalFloor cell14 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_3_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_3_4_g]
def cell14_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(19671365143312/14735654307:ℝ), (40767182674400/14735654307:ℝ), (21331588000000/14735654307:ℝ)]]
theorem cell14_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 4 true ν := by
 have heq : naturalFloor cell14 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_3_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_3_4_g]
def cell14_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(15640208/11913:ℝ), (32449600/11913:ℝ), (17000000/11913:ℝ)]]
theorem cell14_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_3_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_3_4_g]
def cell14_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(51080504225000000/154550410641:ℝ), (103155947925640000/154550410641:ℝ), (51780534050000000/154550410641:ℝ)],
  ![(100747079187980000/154550410641:ℝ), (1906190983870764740000/1449219200580657:ℝ), (956139795087925000000/1449219200580657:ℝ)],
  ![(5493932525000000/17172267849:ℝ), (311629429914725000000/483073066860219:ℝ), (156219460906250000000/483073066860219:ℝ)]]
theorem cell14_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 3 4 b ν := by
 have heq : pairedCleared cell14 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_3_4_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_3_4_g]
theorem cell14_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_3_4 hb hν
def cell14_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(43783180576219869/9530947656625000:ℝ)]]
theorem cell14_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 3 5) := by
 have heq : (-orderedLow cell14 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_3_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_3_5_g]
def cell14_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(911532929452138958339/749378384260265925:ℝ), (1936279964844680201089/749378384260265925:ℝ), (41589384123109862450/29975135370410637:ℝ)]]
theorem cell14_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 3 5 ν := by
 have heq : mixedLowHigh cell14 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_3_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_3_5_g]
def cell14_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(551388580/393129:ℝ), (1157276000/393129:ℝ), (613750000/393129:ℝ)]]
theorem cell14_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 5 false ν := by
 have heq : naturalFloor cell14 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_3_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_3_5_g]
def cell14_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(6943463031380/4911884769:ℝ), (14564226586000/4911884769:ℝ), (7719001250000/4911884769:ℝ)]]
theorem cell14_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 5 true ν := by
 have heq : naturalFloor cell14 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_3_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_3_5_g]
def cell14_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(551388580/393129:ℝ), (1157276000/393129:ℝ), (613750000/393129:ℝ)]]
theorem cell14_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_3_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_3_5_g]
def cell14_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(42026776300000000/154550410641:ℝ), (86756494988300000/154550410641:ℝ), (44361081625000000/154550410641:ℝ)],
  ![(89776257512980000/154550410641:ℝ), (1727310069225602560000/1449219200580657:ℝ), (878795818479950000000/1449219200580657:ℝ)],
  ![(15842766325000000/51516803547:ℝ), (303261681764150000000/483073066860219:ℝ), (17069874500000000000/53674785206691:ℝ)]]
theorem cell14_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 3 5 b ν := by
 have heq : pairedCleared cell14 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_3_5_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_3_5_g]
theorem cell14_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_3_5 hb hν
def cell14_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(202301999889224607/38123790626500000:ℝ)]]
theorem cell14_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 3 6) := by
 have heq : (-orderedLow cell14 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_3_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_3_6_g]
def cell14_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(4224143467824600848317/2997513537041063700:ℝ), (9001825719150136253267/2997513537041063700:ℝ), (96992451524290418675/59950270740821274:ℝ)]]
theorem cell14_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 3 6 ν := by
 have heq : mixedLowHigh cell14 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_3_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_3_6_g]
def cell14_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(586650296/393129:ℝ), (1243715200/393129:ℝ), (666500000/393129:ℝ)]]
theorem cell14_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 6 false ν := by
 have heq : naturalFloor cell14 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_3_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_3_6_g]
def cell14_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(586650296/393129:ℝ), (1243715200/393129:ℝ), (666500000/393129:ℝ)]]
theorem cell14_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 3 6 true ν := by
 have heq : naturalFloor cell14 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_3_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_3_6_g]
def cell14_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(586650296/393129:ℝ), (1243715200/393129:ℝ), (666500000/393129:ℝ)]]
theorem cell14_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_3_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_3_6_g]
def cell14_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(47652741875000000/154550410641:ℝ), (98734860550960000/154550410641:ℝ), (50639754200000000/154550410641:ℝ)],
  ![(99345754337980000/154550410641:ℝ), (1920763508029940380000/1449219200580657:ℝ), (981179628746975000000/1449219200580657:ℝ)],
  ![(51471830225000000/154550410641:ℝ), (990917350215725000000/1449219200580657:ℝ), (504395309031250000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 3 6 b ν := by
 have heq : pairedCleared cell14 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_3_6_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_3_6_g]
theorem cell14_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_3_6 hb hν
def cell14_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(12150835972782607/7624758125300000:ℝ)]]
theorem cell14_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 4 1) := by
 have heq : (-orderedLow cell14 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_4_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_4_1_g]
def cell14_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(10027677125443225448/29975135370410637:ℝ), (23964630766960207900/29975135370410637:ℝ), (14056854182998625000/29975135370410637:ℝ)]]
theorem cell14_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 4 1 ν := by
 have heq : mixedLowHigh cell14 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_4_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_4_1_g]
def cell14_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(191411716/393129:ℝ), (430089200/393129:ℝ), (240250000/393129:ℝ)]]
theorem cell14_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 1 false ν := by
 have heq : naturalFloor cell14 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_4_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_4_1_g]
def cell14_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(2283101150276/4911884769:ℝ), (5164008861200/4911884769:ℝ), (966851750000/1637294923:ℝ)]]
theorem cell14_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 1 true ν := by
 have heq : naturalFloor cell14 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_4_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_4_1_g]
def cell14_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(97641716/393129:ℝ), (248819200/393129:ℝ), (152750000/393129:ℝ)]]
theorem cell14_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_4_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_4_1_g]
def cell14_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(5625965575000000/154550410641:ℝ), (15897115562660000/154550410641:ℝ), (10197422575000000/154550410641:ℝ)],
  ![(15286221775640000/154550410641:ℝ), (368115693234589100000/1449219200580657:ℝ), (223440334835125000000/1449219200580657:ℝ)],
  ![(9365346550000000/154550410641:ℝ), (213702613366375000000/1449219200580657:ℝ), (125238643906250000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 4 1 b ν := by
 have heq : pairedCleared cell14 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_4_1_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_4_1_g]
theorem cell14_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_4_1 hb hν
def cell14_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(43961728724129083/19061895313250000:ℝ)]]
theorem cell14_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 4 2) := by
 have heq : (-orderedLow cell14 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_4_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_4_2_g]
def cell14_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(1095675676573629484/1577638703705823:ℝ), (2488364840573857900/1577638703705823:ℝ), (156145585958875000/175293189300647:ℝ)]]
theorem cell14_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 4 2 ν := by
 have heq : mixedLowHigh cell14 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_4_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_4_2_g]
def cell14_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(278723432/393129:ℝ), (631078400/393129:ℝ), (39500000/43681:ℝ)]]
theorem cell14_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 2 false ν := by
 have heq : naturalFloor cell14 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_4_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_4_2_g]
def cell14_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(278723432/393129:ℝ), (631078400/393129:ℝ), (39500000/43681:ℝ)]]
theorem cell14_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 2 true ν := by
 have heq : naturalFloor cell14 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_4_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_4_2_g]
def cell14_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(789285296/1179387:ℝ), (1802600200/1179387:ℝ), (1022750000/1179387:ℝ)]]
theorem cell14_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_4_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_4_2_g]
def cell14_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(21013388150000000/154550410641:ℝ), (16017312708440000/51516803547:ℝ), (26891095150000000/154550410641:ℝ)],
  ![(45032175600640000/154550410641:ℝ), (105665129091991880000/161024355620073:ℝ), (526046537602150000000/1449219200580657:ℝ)],
  ![(23723877800000000/154550410641:ℝ), (165019103596550000000/483073066860219:ℝ), (271308278937500000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 4 2 b ν := by
 have heq : pairedCleared cell14 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_4_2_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_4_2_g]
theorem cell14_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_4_2 hb hν
def cell14_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(221044293540964869/38123790626500000:ℝ)]]
theorem cell14_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 4 3) := by
 have heq : (-orderedLow cell14 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_4_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_4_3_g]
def cell14_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(43544557429511844944/29975135370410637:ℝ), (87295265848316042300/29975135370410637:ℝ), (4901156671472125000/3330570596712293:ℝ)]]
theorem cell14_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 4 3 ν := by
 have heq : mixedLowHigh cell14 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_4_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_4_3_g]
def cell14_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(522585148/393129:ℝ), (1051117600/393129:ℝ), (59250000/43681:ℝ)]]
theorem cell14_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 3 false ν := by
 have heq : naturalFloor cell14 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_4_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_4_3_g]
def cell14_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(1048075842236/775560753:ℝ), (702246454400/258520251:ℝ), (1067970250000/775560753:ℝ)]]
theorem cell14_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 3 true ν := by
 have heq : naturalFloor cell14 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_4_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_4_3_g]
def cell14_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(522585148/393129:ℝ), (1051117600/393129:ℝ), (59250000/43681:ℝ)]]
theorem cell14_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_4_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_4_3_g]
def cell14_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(51080504225000000/154550410641:ℝ), (100747079187980000/154550410641:ℝ), (5493932525000000/17172267849:ℝ)],
  ![(103155947925640000/154550410641:ℝ), (1906190983870764740000/1449219200580657:ℝ), (311629429914725000000/483073066860219:ℝ)],
  ![(51780534050000000/154550410641:ℝ), (956139795087925000000/1449219200580657:ℝ), (156219460906250000000/483073066860219:ℝ)]]
theorem cell14_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 4 3 b ν := by
 have heq : pairedCleared cell14 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_4_3_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_4_3_g]
theorem cell14_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_4_3 hb hν
def cell14_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(2733752729388/381237906265:ℝ)]]
theorem cell14_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 4 4) := by
 have heq : (-orderedLow cell14 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_4_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_4_4_g]
def cell14_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(57838088649073546592/29975135370410637:ℝ), (117382052588587476400/29975135370410637:ℝ), (60023566105440500000/29975135370410637:ℝ)]]
theorem cell14_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 4 4 ν := by
 have heq : mixedLowHigh cell14 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_4_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_4_4_g]
def cell14_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(703666864/393129:ℝ), (1433376800/393129:ℝ), (736000000/393129:ℝ)]]
theorem cell14_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 4 false ν := by
 have heq : naturalFloor cell14 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_4_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_4_4_g]
def cell14_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(818979056464/446534979:ℝ), (1666220496800/446534979:ℝ), (854386000000/446534979:ℝ)]]
theorem cell14_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 4 true ν := by
 have heq : naturalFloor cell14 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_4_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_4_4_g]
def cell14_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(703666864/393129:ℝ), (1433376800/393129:ℝ), (736000000/393129:ℝ)]]
theorem cell14_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_4_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_4_4_g]
def cell14_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(671393200000000/1561115259:ℝ), (4027330356080000/4683345777:ℝ), (2004214100000000/4683345777:ℝ)],
  ![(4027330356080000/4683345777:ℝ), (75426104620124320000/43915733350929:ℝ), (12499944368800000000/14638577783643:ℝ)],
  ![(2004214100000000/4683345777:ℝ), (12499944368800000000/14638577783643:ℝ), (18628121750000000000/43915733350929:ℝ)]]
theorem cell14_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 4 4 b ν := by
 have heq : pairedCleared cell14 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_4_4_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_4_4_g]
theorem cell14_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_4_4 hb hν
def cell14_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(288344937522665131/38123790626500000:ℝ)]]
theorem cell14_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 4 5) := by
 have heq : (-orderedLow cell14 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_4_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_4_5_g]
def cell14_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(6361820614923399674161/2997513537041063700:ℝ), (12994911118630163088911/2997513537041063700:ℝ), (133860815488951693775/59950270740821274:ℝ)]]
theorem cell14_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 4 5 ν := by
 have heq : mixedLowHigh cell14 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_4_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_4_5_g]
def cell14_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(738928580/393129:ℝ), (1519816000/393129:ℝ), (788750000/393129:ℝ)]]
theorem cell14_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 5 false ν := by
 have heq : naturalFloor cell14 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_4_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_4_5_g]
def cell14_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(28185332814140/14735654307:ℝ), (57910773478000/14735654307:ℝ), (30020153750000/14735654307:ℝ)]]
theorem cell14_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 5 true ν := by
 have heq : naturalFloor cell14 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_4_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_4_5_g]
def cell14_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(738928580/393129:ℝ), (1519816000/393129:ℝ), (788750000/393129:ℝ)]]
theorem cell14_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_4_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_4_5_g]
def cell14_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(72093892375000000/154550410641:ℝ), (144880267313300000/154550410641:ℝ), (72417737875000000/154550410641:ℝ)],
  ![(47490466191880000/51516803547:ℝ), (298057210140937820000/161024355620073:ℝ), (446626100926075000000/483073066860219:ℝ)],
  ![(70082596550000000/154550410641:ℝ), (1318626797434475000000/1449219200580657:ℝ), (658236715281250000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 4 5 b ν := by
 have heq : pairedCleared cell14 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_4_5_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_4_5_g]
theorem cell14_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_4_5 hb hν
def cell14_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(65634608963207369/9530947656625000:ℝ)]]
theorem cell14_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 4 6) := by
 have heq : (-orderedLow cell14 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_4_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_4_6_g]
def cell14_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(454130893228340416513/249792794753421975:ℝ), (947561760564997767863/249792794753421975:ℝ), (19977035776429579150/9991711790136879:ℝ)]]
theorem cell14_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 4 6 ν := by
 have heq : mixedLowHigh cell14 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_4_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_4_6_g]
def cell14_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(7820104/3971:ℝ), (16224800/3971:ℝ), (8500000/3971:ℝ)]]
theorem cell14_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 6 false ν := by
 have heq : naturalFloor cell14 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_4_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_4_6_g]
def cell14_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(29344356764968/14735654307:ℝ), (60836270561600/14735654307:ℝ), (31845569500000/14735654307:ℝ)]]
theorem cell14_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 4 6 true ν := by
 have heq : naturalFloor cell14 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_4_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_4_6_g]
def cell14_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(7820104/3971:ℝ), (16224800/3971:ℝ), (8500000/3971:ℝ)]]
theorem cell14_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_4_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_4_6_g]
def cell14_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(21013388150000000/51516803547:ℝ), (42826938125320000/51516803547:ℝ), (21666095150000000/51516803547:ℝ)],
  ![(131500576900640000/154550410641:ℝ), (2503633976623278200000/1449219200580657:ℝ), (1262534326170250000000/1449219200580657:ℝ)],
  ![(68165502800000000/154550410641:ℝ), (1293523552982750000000/1449219200580657:ℝ), (650464944062500000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 4 6 b ν := by
 have heq : pairedCleared cell14 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_4_6_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_4_6_g]
theorem cell14_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_4_6 hb hν
def cell14_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(7561913489219869/2382736914156250:ℝ)]]
theorem cell14_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 5 1) := by
 have heq : (-orderedLow cell14 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_5_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_5_1_g]
def cell14_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(17271906405302782348/29975135370410637:ℝ), (12302180745676546600/9991711790136879:ℝ), (19754536373208500000/29975135370410637:ℝ)]]
theorem cell14_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 5 1 ν := by
 have heq : mixedLowHigh cell14 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_5_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_5_1_g]
def cell14_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(326901716/393129:ℝ), (226026400/131043:ℝ), (352750000/393129:ℝ)]]
theorem cell14_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 1 false ν := by
 have heq : naturalFloor cell14 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_5_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_5_1_g]
def cell14_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(1069562197348/1339604937:ℝ), (247201336400/148844993:ℝ), (1160608250000/1339604937:ℝ)]]
theorem cell14_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 1 true ν := by
 have heq : naturalFloor cell14 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_5_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_5_1_g]
def cell14_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(186246716/393129:ℝ), (135391400/131043:ℝ), (221500000/393129:ℝ)]]
theorem cell14_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_5_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_5_1_g]
def cell14_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(11251931150000000/154550410641:ℝ), (25466612387660000/154550410641:ℝ), (4713651275000000/51516803547:ℝ)],
  ![(27264587338300000/154550410641:ℝ), (561569132038926920000/1449219200580657:ℝ), (3760156046400000000/17891595068897:ℝ)],
  ![(15644019125000000/154550410641:ℝ), (316086423633400000000/1449219200580657:ℝ), (56249113812500000000/483073066860219:ℝ)]]
theorem cell14_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 5 1 b ν := by
 have heq : pairedCleared cell14 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_5_1_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_5_1_g]
theorem cell14_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_5_1 hb hν
def cell14_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(29631978682372607/7624758125300000:ℝ)]]
theorem cell14_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 5 2) := by
 have heq : (-orderedLow cell14 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_5_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_5_2_g]
def cell14_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(9354022378252839032/9991711790136879:ℝ), (6691204826774748000/3330570596712293:ℝ), (10799525796392500000/9991711790136879:ℝ)]]
theorem cell14_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 5 2 ν := by
 have heq : mixedLowHigh cell14 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_5_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_5_2_g]
def cell14_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(138071144/131043:ℝ), (293022800/131043:ℝ), (52000000/43681:ℝ)]]
theorem cell14_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 2 false ν := by
 have heq : naturalFloor cell14 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_5_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_5_2_g]
def cell14_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(15363271121656/14735654307:ℝ), (32635617387200/14735654307:ℝ), (17390231500000/14735654307:ℝ)]]
theorem cell14_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 2 true ν := by
 have heq : naturalFloor cell14 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_5_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_5_2_g]
def cell14_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1055100296/1179387:ℝ), (2274665200/1179387:ℝ), (1229000000/1179387:ℝ)]]
theorem cell14_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_5_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_5_2_g]
def cell14_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(8879784575000000/51516803547:ℝ), (19207144983440000/51516803547:ℝ), (380674400000000/1908029761:ℝ)],
  ![(6334504573700000/17172267849:ℝ), (381479866877421580000/483073066860219:ℝ), (202392947508475000000/483073066860219:ℝ)],
  ![(10000850125000000/51516803547:ℝ), (22127448928025000000/53674785206691:ℝ), (104938992156250000000/483073066860219:ℝ)]]
theorem cell14_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 5 2 b ν := by
 have heq : pairedCleared cell14 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_5_2_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_5_2_g]
theorem cell14_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_5_2 hb hν
def cell14_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(87664585498104083/19061895313250000:ℝ)]]
theorem cell14_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 5 3) := by
 have heq : (-orderedLow cell14 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_5_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_5_3_g]
def cell14_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(38852227864214251844/29975135370410637:ℝ), (27845048214971941400/9991711790136879:ℝ), (45042618405146500000/29975135370410637:ℝ)]]
theorem cell14_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 5 3 ν := by
 have heq : mixedLowHigh cell14 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_5_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_5_3_g]
def cell14_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(501525148/393129:ℝ), (120006400/43681:ℝ), (583250000/393129:ℝ)]]
theorem cell14_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 3 false ν := by
 have heq : naturalFloor cell14 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_5_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_5_3_g]
def cell14_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(6320452690828/4911884769:ℝ), (40798302470800/14735654307:ℝ), (22013772250000/14735654307:ℝ)]]
theorem cell14_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 3 true ν := by
 have heq : naturalFloor cell14 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_5_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_5_3_g]
def cell14_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(501525148/393129:ℝ), (120006400/43681:ℝ), (583250000/393129:ℝ)]]
theorem cell14_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_5_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_5_3_g]
def cell14_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(42026776300000000/154550410641:ℝ), (89776257512980000/154550410641:ℝ), (15842766325000000/51516803547:ℝ)],
  ![(86756494988300000/154550410641:ℝ), (1727310069225602560000/1449219200580657:ℝ), (303261681764150000000/483073066860219:ℝ)],
  ![(44361081625000000/154550410641:ℝ), (878795818479950000000/1449219200580657:ℝ), (17069874500000000000/53674785206691:ℝ)]]
theorem cell14_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 5 3 b ν := by
 have heq : pairedCleared cell14 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_5_3_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_5_3_g]
theorem cell14_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_5_3 hb hν
def cell14_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(308450007088914869/38123790626500000:ℝ)]]
theorem cell14_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 5 4) := by
 have heq : (-orderedLow cell14 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_5_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_5_4_g]
def cell14_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(20526315812942378864/9991711790136879:ℝ), (123551478522328566400/29975135370410637:ℝ), (62452133249428000000/29975135370410637:ℝ)]]
theorem cell14_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 5 4 ν := by
 have heq : mixedLowHigh cell14 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_5_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_5_4_g]
def cell14_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(248462288/131043:ℝ), (1500096800/393129:ℝ), (761000000/393129:ℝ)]]
theorem cell14_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 4 false ν := by
 have heq : naturalFloor cell14 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_5_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_5_4_g]
def cell14_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(861436626464/446534979:ℝ), (5197421700400/1339604937:ℝ), (2634545500000/1339604937:ℝ)]]
theorem cell14_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 4 true ν := by
 have heq : naturalFloor cell14 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_5_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_5_4_g]
def cell14_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(248462288/131043:ℝ), (1500096800/393129:ℝ), (761000000/393129:ℝ)]]
theorem cell14_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_5_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_5_4_g]
def cell14_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(72093892375000000/154550410641:ℝ), (47490466191880000/51516803547:ℝ), (70082596550000000/154550410641:ℝ)],
  ![(144880267313300000/154550410641:ℝ), (298057210140937820000/161024355620073:ℝ), (1318626797434475000000/1449219200580657:ℝ)],
  ![(72417737875000000/154550410641:ℝ), (446626100926075000000/483073066860219:ℝ), (658236715281250000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 5 4 b ν := by
 have heq : pairedCleared cell14 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_5_4_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_5_4_g]
theorem cell14_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_5_4 hb hν
def cell14_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(1443123945947/152495162506:ℝ)]]
theorem cell14_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 5 5) := by
 have heq : (-orderedLow cell14 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_5_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_5_5_g]
def cell14_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(25290826219462946080/9991711790136879:ℝ), (51212755087533333500/9991711790136879:ℝ), (26121763103873125000/9991711790136879:ℝ)]]
theorem cell14_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 5 5 ν := by
 have heq : mixedLowHigh cell14 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_5_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_5_5_g]
def cell14_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(308822860/131043:ℝ), (627452000/131043:ℝ), (321250000/131043:ℝ)]]
theorem cell14_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 5 false ν := by
 have heq : naturalFloor cell14 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_5_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_5_5_g]
def cell14_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(35540276534140/14735654307:ℝ), (72128867198000/14735654307:ℝ), (36883303750000/14735654307:ℝ)]]
theorem cell14_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 5 true ν := by
 have heq : naturalFloor cell14 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_5_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_5_5_g]
def cell14_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(308822860/131043:ℝ), (627452000/131043:ℝ), (321250000/131043:ℝ)]]
theorem cell14_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_5_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_5_5_g]
def cell14_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(87481314950000000/154550410641:ℝ), (174626221138300000/154550410641:ℝ), (86776269125000000/154550410641:ℝ)],
  ![(174626221138300000/154550410641:ℝ), (3265385359861778200000/1449219200580657:ℝ), (1621233000201500000000/1449219200580657:ℝ)],
  ![(86776269125000000/154550410641:ℝ), (1621233000201500000000/1449219200580657:ℝ), (804306350312500000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 5 5 b ν := by
 have heq : pairedCleared cell14 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_5_5_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_5_5_g]
theorem cell14_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_5_5 hb hν
def cell14_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(375750651070615131/38123790626500000:ℝ)]]
theorem cell14_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 5 6) := by
 have heq : (-orderedLow cell14 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_5_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_5_6_g]
def cell14_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(8165259615854928838961/2997513537041063700:ℝ), (16620532386031415498911/2997513537041063700:ℝ), (170544261901309443775/59950270740821274:ℝ)]]
theorem cell14_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 5 6 ν := by
 have heq : mixedLowHigh cell14 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_5_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_5_6_g]
def cell14_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(50617384/20691:ℝ), (103620800/20691:ℝ), (53500000/20691:ℝ)]]
theorem cell14_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 6 false ν := by
 have heq : naturalFloor cell14 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_5_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_5_6_g]
def cell14_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(101100001336/40594089:ℝ), (2274374675200/446534979:ℝ), (1172991500000/446534979:ℝ)]]
theorem cell14_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 5 6 true ν := by
 have heq : naturalFloor cell14 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_5_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_5_6_g]
def cell14_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(50617384/20691:ℝ), (103620800/20691:ℝ), (53500000/20691:ℝ)]]
theorem cell14_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_5_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_5_6_g]
def cell14_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(31035760175000000/51516803547:ℝ), (62201528900320000/51516803547:ℝ), (31018313900000000/51516803547:ℝ)],
  ![(184195717963300000/154550410641:ℝ), (3458838798666116020000/1449219200580657:ℝ), (1723616810468525000000/1449219200580657:ℝ)],
  ![(90719800375000000/154550410641:ℝ), (1702365305124775000000/1449219200580657:ℝ), (847815047843750000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 5 6 b ν := by
 have heq : pairedCleared cell14 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_5_6_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_5_6_g]
theorem cell14_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_5_6 hb hν
def cell14_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(234202831045303559/38123790626500000:ℝ)]]
theorem cell14_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 6 1) := by
 have heq : (-orderedLow cell14 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_6_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_6_1_g]
def cell14_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(656979202452598935961/499585589506843950:ℝ), (3932860611165756246733/1498756768520531850:ℝ), (39358360617640831325/29975135370410637:ℝ)]]
theorem cell14_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 6 1 ν := by
 have heq : mixedLowHigh cell14 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_6_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_6_1_g]
def cell14_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(154130572/131043:ℝ), (926069200/393129:ℝ), (465250000/393129:ℝ)]]
theorem cell14_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 1 false ν := by
 have heq : naturalFloor cell14 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_6_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_6_1_g]
def cell14_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(16681064890828/14735654307:ℝ), (11151279341200/4911884769:ℝ), (16831715750000/14735654307:ℝ)]]
theorem cell14_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 1 true ν := by
 have heq : naturalFloor cell14 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_6_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_6_1_g]
def cell14_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(274851716/393129:ℝ), (563529200/393129:ℝ), (32250000/43681:ℝ)]]
theorem cell14_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_6_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_6_1_g]
def cell14_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(31557590225000000/154550410641:ℝ), (21137975904220000/51516803547:ℝ), (31782610075000000/154550410641:ℝ)],
  ![(59783271400960000/154550410641:ℝ), (125261880476973860000/161024355620073:ℝ), (565432731556675000000/1449219200580657:ℝ)],
  ![(27783316700000000/154550410641:ℝ), (174901927758475000000/483073066860219:ℝ), (263536507718750000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 6 1 b ν := by
 have heq : pairedCleared cell14 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_6_1_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_6_1_g]
theorem cell14_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_6_1 hb hν
def cell14_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(6512385292983372/1191368457078125:ℝ)]]
theorem cell14_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 6 2) := by
 have heq : (-orderedLow cell14 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_6_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_6_2_g]
def cell14_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(35306296414618073996/29975135370410637:ℝ), (73162754911042163900/29975135370410637:ℝ), (12698753193129125000/9991711790136879:ℝ)]]
theorem cell14_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 6 2 ν := by
 have heq : mixedLowHigh cell14 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_6_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_6_2_g]
def cell14_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(549703432/393129:ℝ), (1127058400/393129:ℝ), (64500000/43681:ℝ)]]
theorem cell14_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 2 false ν := by
 have heq : naturalFloor cell14 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_6_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_6_2_g]
def cell14_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(6759717280552/4911884769:ℝ), (41616523107200/14735654307:ℝ), (21455256500000/14735654307:ℝ)]]
theorem cell14_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 2 true ν := by
 have heq : naturalFloor cell14 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_6_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_6_2_g]
def cell14_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(1320915296/1179387:ℝ), (2746730200/1179387:ℝ), (1435250000/1179387:ℝ)]]
theorem cell14_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_6_2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_6_2_g]
def cell14_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(1698174700000000/8134232139:ℝ), (1178788276760000/2711410713:ℝ), (1830429350000000/8134232139:ℝ)],
  ![(3630995090840000/8134232139:ℝ), (23471807709414080000/25424898255801:ℝ), (36226902497300000000/76274694767403:ℝ)],
  ![(1909538050000000/8134232139:ℝ), (12277630374100000000/25424898255801:ℝ), (18859246000000000000/76274694767403:ℝ)]]
theorem cell14_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 6 2 b ν := by
 have heq : pairedCleared cell14 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_6_2_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_6_2_g]
theorem cell14_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_6_2 hb hν
def cell14_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(47113121391962607/7624758125300000:ℝ)]]
theorem cell14_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 6 3) := by
 have heq : (-orderedLow cell14 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_6_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_6_3_g]
def cell14_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(46096457144073808744/29975135370410637:ℝ), (96477056114985256100/29975135370410637:ℝ), (50740300595356375000/29975135370410637:ℝ)]]
theorem cell14_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 6 3 ν := by
 have heq : mixedLowHigh cell14 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_6_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_6_3_g]
def cell14_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(5264588/3249:ℝ), (10975600/3249:ℝ), (5750000/3249:ℝ)]]
theorem cell14_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 3 false ν := by
 have heq : naturalFloor cell14 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_6_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_6_3_g]
def cell14_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(5264588/3249:ℝ), (10975600/3249:ℝ), (5750000/3249:ℝ)]]
theorem cell14_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 3 true ν := by
 have heq : naturalFloor cell14 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_6_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_6_3_g]
def cell14_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(5034004/3267:ℝ), (200151200/62073:ℝ), (105250000/62073:ℝ)]]
theorem cell14_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_6_3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_6_3_g]
def cell14_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(47652741875000000/154550410641:ℝ), (99345754337980000/154550410641:ℝ), (51471830225000000/154550410641:ℝ)],
  ![(98734860550960000/154550410641:ℝ), (1920763508029940380000/1449219200580657:ℝ), (990917350215725000000/1449219200580657:ℝ)],
  ![(50639754200000000/154550410641:ℝ), (981179628746975000000/1449219200580657:ℝ), (504395309031250000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 6 3 b ν := by
 have heq : pairedCleared cell14 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_6_3_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_6_3_g]
theorem cell14_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_6_3 hb hν
def cell14_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(131367442272079083/19061895313250000:ℝ)]]
theorem cell14_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 6 4) := by
 have heq : (-orderedLow cell14 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_6_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_6_4_g]
def cell14_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(6320735319281060388/3330570596712293:ℝ), (119791357318928348300/29975135370410637:ℝ), (63384341611325375000/29975135370410637:ℝ)]]
theorem cell14_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 6 4 ν := by
 have heq : mixedLowHigh cell14 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_6_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_6_4_g]
def cell14_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(241442288/131043:ℝ), (1529036800/393129:ℝ), (811000000/393129:ℝ)]]
theorem cell14_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 4 false ν := by
 have heq : naturalFloor cell14 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_6_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_6_4_g]
def cell14_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(27475325743312/14735654307:ℝ), (6437988141600/1637294923:ℝ), (30702338000000/14735654307:ℝ)]]
theorem cell14_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 4 true ν := by
 have heq : naturalFloor cell14 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_6_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_6_4_g]
def cell14_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(241442288/131043:ℝ), (1529036800/393129:ℝ), (811000000/393129:ℝ)]]
theorem cell14_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_6_4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_6_4_g]
def cell14_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(21013388150000000/51516803547:ℝ), (131500576900640000/154550410641:ℝ), (68165502800000000/154550410641:ℝ)],
  ![(42826938125320000/51516803547:ℝ), (2503633976623278200000/1449219200580657:ℝ), (1293523552982750000000/1449219200580657:ℝ)],
  ![(21666095150000000/51516803547:ℝ), (1262534326170250000000/1449219200580657:ℝ), (650464944062500000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 6 4 b ν := by
 have heq : pairedCleared cell14 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_6_4_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_6_4_g]
theorem cell14_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_6_4 hb hν
def cell14_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(395855720636864869/38123790626500000:ℝ)]]
theorem cell14_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 6 5) := by
 have heq : (-orderedLow cell14 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_6_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_6_5_g]
def cell14_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(4190175655165390960/1577638703705823:ℝ), (2803643705198966500/525879567901941:ℝ), (4252308234505625000/1577638703705823:ℝ)]]
theorem cell14_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 6 5 ν := by
 have heq : mixedLowHigh cell14 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_6_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_6_5_g]
def cell14_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(968188580/393129:ℝ), (216564000/43681:ℝ), (988750000/393129:ℝ)]]
theorem cell14_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 5 false ν := by
 have heq : naturalFloor cell14 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_6_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_6_5_g]
def cell14_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(36941376344140/14735654307:ℝ), (74315229508000/14735654307:ℝ), (4185396250000/1637294923:ℝ)]]
theorem cell14_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 5 true ν := by
 have heq : naturalFloor cell14 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_6_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_6_5_g]
def cell14_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(968188580/393129:ℝ), (216564000/43681:ℝ), (988750000/393129:ℝ)]]
theorem cell14_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_6_5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_6_5_g]
def cell14_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(31035760175000000/51516803547:ℝ), (184195717963300000/154550410641:ℝ), (90719800375000000/154550410641:ℝ)],
  ![(62201528900320000/51516803547:ℝ), (3458838798666116020000/1449219200580657:ℝ), (1702365305124775000000/1449219200580657:ℝ)],
  ![(31018313900000000/51516803547:ℝ), (1723616810468525000000/1449219200580657:ℝ), (847815047843750000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 6 5 b ν := by
 have heq : pairedCleared cell14 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_6_5_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_6_5_g]
theorem cell14_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_6_5 hb hν
def cell14_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(4481867000347/381237906265:ℝ)]]
theorem cell14_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell14 6 6) := by
 have heq : (-orderedLow cell14 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell14_ordered_6_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordered_6_6_g]
def cell14_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(93906868667704129888/29975135370410637:ℝ), (189894477936612524600/29975135370410637:ℝ), (96707012517798250000/29975135370410637:ℝ)]]
theorem cell14_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell14 6 6 ν := by
 have heq : mixedLowHigh cell14 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_mixed_6_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_mixed_6_6_g]
def cell14_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(1149270296/393129:ℝ), (2331335200/393129:ℝ), (1191500000/393129:ℝ)]]
theorem cell14_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 6 false ν := by
 have heq : naturalFloor cell14 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor0_6_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor0_6_6_g]
def cell14_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(44054244204968/14735654307:ℝ), (89272458001600/14735654307:ℝ), (45571869500000/14735654307:ℝ)]]
theorem cell14_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell14 6 6 true ν := by
 have heq : naturalFloor cell14 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_floor1_6_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_floor1_6_6_g]
def cell14_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(1149270296/393129:ℝ), (2331335200/393129:ℝ), (1191500000/393129:ℝ)]]
theorem cell14_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell14_complement_floor_6_6_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement_floor_6_6_g]
def cell14_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(108494703100000000/154550410641:ℝ), (216350540525960000/154550410641:ℝ), (107413472950000000/154550410641:ℝ)],
  ![(216350540525960000/154550410641:ℝ), (4041709267259453840000/1449219200580657:ℝ), (2004971507891800000000/1449219200580657:ℝ)],
  ![(107413472950000000/154550410641:ℝ), (2004971507891800000000/1449219200580657:ℝ), (993884682875000000000/1449219200580657:ℝ)]]
theorem cell14_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell14 6 6 b ν := by
 have heq : pairedCleared cell14 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell14_paired_cleared_6_6_g (3123/5000:ℝ) (3/4:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_cleared_6_6_g]
theorem cell14_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell14 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell14_paired_cleared_6_6 hb hν
def cell14_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(24623395642869869/38123790626500000:ℝ)]]
theorem cell14_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell14.q/K)+1+17/50*(cell14.q/cell14.priorL)+17/25*(cell14.q/cell14.priorL)*cell14.priorB) := by
 have heq : ((2-17/50-17/25)*(cell14.q/K)+1+17/50*(cell14.q/cell14.priorL)+17/25*(cell14.q/cell14.priorL)*cell14.priorB) = Record12518109.Bernstein.bsum 0 0 (24623395642869869/38123790626500000:ℝ) cell14_increment0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_increment0_g]
def cell14_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(509016384257/1017095500000:ℝ)]]
theorem cell14_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell14.q/cell14.priorL)*(1-cell14.priorB)) := by
 have heq : (1+17/25*(cell14.q/cell14.priorL)*(1-cell14.priorB)) = Record12518109.Bernstein.bsum 0 0 (509016384257/1017095500000:ℝ) cell14_increment1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_increment1_g]
def cell14_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(2035596902771/4068382000000:ℝ)]]
theorem cell14_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell14.q/cell14.priorL)*(1-cell14.priorB)) := by
 have heq : (1+omega*(cell14.q/cell14.priorL)*(1-cell14.priorB)) = Record12518109.Bernstein.bsum 0 0 (2035596902771/4068382000000:ℝ) cell14_increment2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_increment2_g]
def cell14_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(38691916/393129:ℝ), (76579600/393129:ℝ), (13153400/131043:ℝ)]]
theorem cell14_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (191449/125000:ℝ) cell14_high_increment_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_high_increment_g]
def cell14_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(538458491198/82163961:ℝ), (5564360096606/82163961:ℝ), (9986503776406/82163961:ℝ), (4661854008802/82163961:ℝ)]]
theorem cell14_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (807687736797/62500000000:ℝ) cell14_three_gate0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_three_gate0_g]
def cell14_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(17630858/393129:ℝ), (51177484/393129:ℝ), (35119142/393129:ℝ)]]
theorem cell14_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (8815429/12500000:ℝ) cell14_three_gate1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_three_gate1_g]
def cell14_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(23968842104/258520251:ℝ), (142799022200/775560753:ℝ), (73994738900/775560753:ℝ)]]
theorem cell14_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell14.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell14.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (13565907109/9370750000:ℝ) cell14_three_gate2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_three_gate2_g]
def cell14_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(17874/37483:ℝ)]]
theorem cell14_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (1-cell14.q/K/3) := by
 have heq : (1-cell14.q/K/3) = Record12518109.Bernstein.bsum 0 0 (17874/37483:ℝ) cell14_paired_margin0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_margin0_g]
def cell14_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(7955521/93770000:ℝ)]]
theorem cell14_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (gamma cell14-13/50) := by
 have heq : (gamma cell14-13/50) = Record12518109.Bernstein.bsum 0 0 (7955521/93770000:ℝ) cell14_paired_margin1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_margin1_g]
def cell14_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(7311/75016:ℝ)]]
theorem cell14_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (cell14.q-gamma cell14) := by
 have heq : (cell14.q-gamma cell14) = Record12518109.Bernstein.bsum 0 0 (7311/75016:ℝ) cell14_paired_margin2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_margin2_g]
def cell14_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(198896903/656390000:ℝ)]]
theorem cell14_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < (min (cell14.q+rho cell14.q) (3/4+rho (3/4))-gamma cell14) := by
 have heq : (min (cell14.q+rho cell14.q) (3/4+rho (3/4))-gamma cell14) = Record12518109.Bernstein.bsum 0 0 (198896903/656390000:ℝ) cell14_paired_margin3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_paired_margin3_g]
theorem cell14_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (3123/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell14 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell14_paired_1_1 hb hν
 · exact cell14_paired_1_2 hb hν
 · exact cell14_paired_1_3 hb hν
 · exact cell14_paired_1_4 hb hν
 · exact cell14_paired_1_5 hb hν
 · exact cell14_paired_1_6 hb hν
 · exact cell14_paired_2_1 hb hν
 · exact cell14_paired_2_2 hb hν
 · exact cell14_paired_2_3 hb hν
 · exact cell14_paired_2_4 hb hν
 · exact cell14_paired_2_5 hb hν
 · exact cell14_paired_2_6 hb hν
 · exact cell14_paired_3_1 hb hν
 · exact cell14_paired_3_2 hb hν
 · exact cell14_paired_3_3 hb hν
 · exact cell14_paired_3_4 hb hν
 · exact cell14_paired_3_5 hb hν
 · exact cell14_paired_3_6 hb hν
 · exact cell14_paired_4_1 hb hν
 · exact cell14_paired_4_2 hb hν
 · exact cell14_paired_4_3 hb hν
 · exact cell14_paired_4_4 hb hν
 · exact cell14_paired_4_5 hb hν
 · exact cell14_paired_4_6 hb hν
 · exact cell14_paired_5_1 hb hν
 · exact cell14_paired_5_2 hb hν
 · exact cell14_paired_5_3 hb hν
 · exact cell14_paired_5_4 hb hν
 · exact cell14_paired_5_5 hb hν
 · exact cell14_paired_5_6 hb hν
 · exact cell14_paired_6_1 hb hν
 · exact cell14_paired_6_2 hb hν
 · exact cell14_paired_6_3 hb hν
 · exact cell14_paired_6_4 hb hν
 · exact cell14_paired_6_5 hb hν
 · exact cell14_paired_6_6 hb hν
end
end Record12518109Admission
