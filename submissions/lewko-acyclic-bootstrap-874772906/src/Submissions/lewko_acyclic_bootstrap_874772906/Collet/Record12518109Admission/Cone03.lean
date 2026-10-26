/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell03
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell3_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(340639235671/1143713718795:ℝ)]]
theorem cell3_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 1 1) := by
 have heq : (-orderedLow cell3 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_1_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_1_1_g]
def cell3_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(65701254142227224/425232760647981:ℝ), (49831117255576350/141744253549327:ℝ), (85493028667093750/425232760647981:ℝ)]]
theorem cell3_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 1 1 ν := by
 have heq : mixedLowHigh cell3 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_1_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_1_1_g]
def cell3_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(2291871/20449:ℝ), (5506950/20449:ℝ), (3296875/20449:ℝ)]]
theorem cell3_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 1 false ν := by
 have heq : naturalFloor cell3 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_1_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_1_1_g]
def cell3_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(66594993749/530646831:ℝ), (17412227450/58960759:ℝ), (7095203125/40818987:ℝ)]]
theorem cell3_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 1 true ν := by
 have heq : naturalFloor cell3 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_1_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_1_1_g]
def cell3_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(2291871/20449:ℝ), (5506950/20449:ℝ), (3296875/20449:ℝ)]]
theorem cell3_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_1_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_1_1_g]
def cell3_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(37029460156250/1254484803:ℝ), (27812257753750/418161601:ℝ), (45692467187500/1254484803:ℝ)],
  ![(27812257753750/418161601:ℝ), (286401327588270000/1949051222261:ℝ), (154615278294531250/1949051222261:ℝ)],
  ![(45692467187500/1254484803:ℝ), (154615278294531250/1949051222261:ℝ), (247745794433593750/5847153666783:ℝ)]]
theorem cell3_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 1 1 b ν := by
 have heq : pairedCleared cell3 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_1_1_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_1_1_g]
theorem cell3_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_1_1 hb hν
def cell3_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(39539492601421199/57185685939750000:ℝ)]]
theorem cell3_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 1 2) := by
 have heq : (-orderedLow cell3 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_1_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_1_2_g]
def cell3_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(728558768453223996817/1871024146851116400:ℝ), (133924094563259858541/155918678904259700:ℝ), (35739942379228129475/74840965874044656:ℝ)]]
theorem cell3_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 1 2 ν := by
 have heq : mixedLowHigh cell3 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_1_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_1_2_g]
def cell3_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(4583742/20449:ℝ), (11013900/20449:ℝ), (6593750/20449:ℝ)]]
theorem cell3_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 2 false ν := by
 have heq : naturalFloor cell3 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_1_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_1_2_g]
def cell3_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(4583742/20449:ℝ), (11013900/20449:ℝ), (6593750/20449:ℝ)]]
theorem cell3_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 2 true ν := by
 have heq : naturalFloor cell3 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_1_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_1_2_g]
def cell3_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(4583742/20449:ℝ), (11013900/20449:ℝ), (6593750/20449:ℝ)]]
theorem cell3_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_1_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_1_2_g]
def cell3_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(9047073828125/114044073:ℝ), (6552398995000/38014691:ℝ), (952741015625/10367643:ℝ)],
  ![(17328575836250/114044073:ℝ), (58573627968855000/177186474751:ℝ), (93777965077343750/531559424253:ℝ)],
  ![(2738838671875/38014691:ℝ), (27837158443750000/177186474751:ℝ), (14881888916015625/177186474751:ℝ)]]
theorem cell3_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 1 2 b ν := by
 have heq : pairedCleared cell3 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_1_2_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_1_2_g]
theorem cell3_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_1_2 hb hν
def cell3_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(298852319075051/14296421484937500:ℝ)]]
theorem cell3_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 1 3) := by
 have heq : (-orderedLow cell3 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_1_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_1_3_g]
def cell3_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(1178136831550396141/35981233593290700:ℝ), (658303368158459343/2998436132774225:ℝ), (286131135578824175/1439249343731628:ℝ)]]
theorem cell3_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 1 3 ν := by
 have heq : mixedLowHigh cell3 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_1_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_1_3_g]
def cell3_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(6875613/20449:ℝ), (16520850/20449:ℝ), (9890625/20449:ℝ)]]
theorem cell3_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 3 false ν := by
 have heq : naturalFloor cell3 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_1_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_1_3_g]
def cell3_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(2226888306211/6898408803:ℝ), (599309070550/766489867:ℝ), (3249674234375/6898408803:ℝ)]]
theorem cell3_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 3 true ν := by
 have heq : naturalFloor cell3 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_1_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_1_3_g]
def cell3_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(6875613/20449:ℝ), (16520850/20449:ℝ), (9890625/20449:ℝ)]]
theorem cell3_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_1_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_1_3_g]
def cell3_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (81468453750/2924207:ℝ), (76469531250/2924207:ℝ)],
  ![(472093453750/8772621:ℝ), (2158094430780000/13629728827:ℝ), (4138344913281250/40889186481:ℝ)],
  ![(467094531250/8772621:ℝ), (1763313213281250/13629728827:ℝ), (3047201171875000/40889186481:ℝ)]]
theorem cell3_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 1 3 b ν := by
 have heq : pairedCleared cell3 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_1_3_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_1_3_g]
theorem cell3_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_1_3 hb hν
def cell3_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(42002359594891403/57185685939750000:ℝ)]]
theorem cell3_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 1 4) := by
 have heq : (-orderedLow cell3 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_1_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_1_4_g]
def cell3_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(500736365468044810549/1871024146851116400:ℝ), (113341640726365759377/155918678904259700:ℝ), (35571988383918486575/74840965874044656:ℝ)]]
theorem cell3_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 1 4 ν := by
 have heq : mixedLowHigh cell3 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_1_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_1_4_g]
def cell3_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(9167484/20449:ℝ), (22027800/20449:ℝ), (13187500/20449:ℝ)]]
theorem cell3_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 4 false ν := by
 have heq : naturalFloor cell3 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_1_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_1_4_g]
def cell3_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(2907464999948/6898408803:ℝ), (785784127400/766489867:ℝ), (4274966687500/6898408803:ℝ)]]
theorem cell3_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 4 true ν := by
 have heq : naturalFloor cell3 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_1_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_1_4_g]
def cell3_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(9167484/20449:ℝ), (22027800/20449:ℝ), (13187500/20449:ℝ)]]
theorem cell3_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_1_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_1_4_g]
def cell3_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(62488351953125/1254484803:ℝ), (55914120077500/418161601:ℝ), (102394624609375/1254484803:ℝ)],
  ![(58228974941250/418161601:ℝ), (666516083670675000/1949051222261:ℝ), (386498367855468750/1949051222261:ℝ)],
  ![(111483726953125/1254484803:ℝ), (403747254085937500/1949051222261:ℝ), (679106307373046875/5847153666783:ℝ)]]
theorem cell3_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 1 4 b ν := by
 have heq : pairedCleared cell3 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_1_4_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_1_4_g]
theorem cell3_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_1_4 hb hν
def cell3_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(41404654956741301/28592842969875000:ℝ)]]
theorem cell3_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 1 5) := by
 have heq : (-orderedLow cell3 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_1_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_1_5_g]
def cell3_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(470104807847734510883/935512073425558200:ℝ), (96225753154245816459/77959339452129850:ℝ), (28132578858869058025/37420482937022328:ℝ)]]
theorem cell3_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 1 5 ν := by
 have heq : mixedLowHigh cell3 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_1_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_1_5_g]
def cell3_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(11459355/20449:ℝ), (27534750/20449:ℝ), (16484375/20449:ℝ)]]
theorem cell3_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 5 false ν := by
 have heq : naturalFloor cell3 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_1_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_1_5_g]
def cell3_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(1196013897895/2299469601:ℝ), (972259184250/766489867:ℝ), (1766753046875/2299469601:ℝ)]]
theorem cell3_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 5 true ν := by
 have heq : naturalFloor cell3 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_1_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_1_5_g]
def cell3_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(11459355/20449:ℝ), (27534750/20449:ℝ), (16484375/20449:ℝ)]]
theorem cell3_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_1_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_1_5_g]
def cell3_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(124976703906250/1254484803:ℝ), (100178251268750/418161601:ℝ), (171983820312500/1254484803:ℝ)],
  ![(281864485761250/1254484803:ℝ), (1024424663739810000/1949051222261:ℝ), (1727206884533593750/5847153666783:ℝ)],
  ![(52057645312500/418161601:ℝ), (555340718672656250/1949051222261:ℝ), (307487615722656250/1949051222261:ℝ)]]
theorem cell3_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 1 5 b ν := by
 have heq : pairedCleared cell3 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_1_5_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_1_5_g]
theorem cell3_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_1_5 hb hν
def cell3_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(281918327519498189/57185685939750000:ℝ)]]
theorem cell3_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 1 6) := by
 have heq : (-orderedLow cell3 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_1_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_1_6_g]
def cell3_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(2227746588409385732983/1871024146851116400:ℝ), (372017560191445006459/155918678904259700:ℝ), (91254748536495245525/74840965874044656:ℝ)]]
theorem cell3_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 1 6 ν := by
 have heq : mixedLowHigh cell3 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_1_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_1_6_g]
def cell3_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(23019976/20449:ℝ), (46216700/20449:ℝ), (23687500/20449:ℝ)]]
theorem cell3_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 6 false ν := by
 have heq : naturalFloor cell3 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_1_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_1_6_g]
def cell3_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(7395403393672/6898408803:ℝ), (1652572766100/766489867:ℝ), (7643313312500/6898408803:ℝ)]]
theorem cell3_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 1 6 true ν := by
 have heq : naturalFloor cell3 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_1_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_1_6_g]
def cell3_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(23019976/20449:ℝ), (46216700/20449:ℝ), (23687500/20449:ℝ)]]
theorem cell3_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_1_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_1_6_g]
def cell3_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(116490406640625/418161601:ℝ), (221203226210000/418161601:ℝ), (103283127734375/418161601:ℝ)],
  ![(703113640448750/1254484803:ℝ), (2075944227933945000/1949051222261:ℝ), (2911863919407031250/5847153666783:ℝ)],
  ![(352927574609375/1254484803:ℝ), (1042762874665625000/1949051222261:ℝ), (1464528493408203125/5847153666783:ℝ)]]
theorem cell3_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 1 6 b ν := by
 have heq : pairedCleared cell3 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_1_6_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_1_6_g]
theorem cell3_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_1_6 hb hν
def cell3_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(69885792407773801/57185685939750000:ℝ)]]
theorem cell3_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 2 1) := by
 have heq : (-orderedLow cell3 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_2_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_2_1_g]
def cell3_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(468126262336981488/1559186789042597:ℝ), (2783173150467964550/4677560367127791:ℝ), (1397504604925531250/4677560367127791:ℝ)]]
theorem cell3_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 2 1 ν := by
 have heq : mixedLowHigh cell3 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_2_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_2_1_g]
def cell3_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(14423113/61347:ℝ), (28755850/61347:ℝ), (4859375/20449:ℝ)]]
theorem cell3_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 1 false ν := by
 have heq : naturalFloor cell3 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_2_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_2_1_g]
def cell3_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(14423113/61347:ℝ), (28755850/61347:ℝ), (4859375/20449:ℝ)]]
theorem cell3_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 1 true ν := by
 have heq : naturalFloor cell3 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_2_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_2_1_g]
def cell3_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(14423113/61347:ℝ), (28755850/61347:ℝ), (4859375/20449:ℝ)]]
theorem cell3_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_2_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_2_1_g]
def cell3_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(9047073828125/114044073:ℝ), (17328575836250/114044073:ℝ), (2738838671875/38014691:ℝ)],
  ![(6552398995000/38014691:ℝ), (58573627968855000/177186474751:ℝ), (27837158443750000/177186474751:ℝ)],
  ![(952741015625/10367643:ℝ), (93777965077343750/531559424253:ℝ), (14881888916015625/177186474751:ℝ)]]
theorem cell3_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 2 1 b ν := by
 have heq : pairedCleared cell3 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_2_1_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_2_1_g]
theorem cell3_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_2_1 hb hν
def cell3_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(2968705908932/1143713718795:ℝ)]]
theorem cell3_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 2 2) := by
 have heq : (-orderedLow cell3 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_2_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_2_2_g]
def cell3_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(4110852412780746428/4677560367127791:ℝ), (2818717440127949700/1559186789042597:ℝ), (4382720390540125000/4677560367127791:ℝ)]]
theorem cell3_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 2 2 ν := by
 have heq : mixedLowHigh cell3 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_2_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_2_2_g]
def cell3_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1476022/1859:ℝ), (3054900/1859:ℝ), (1593750/1859:ℝ)]]
theorem cell3_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 2 false ν := by
 have heq : naturalFloor cell3 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_2_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_2_2_g]
def cell3_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(5662405754974/6898408803:ℝ), (1299458883700/766489867:ℝ), (6087911468750/6898408803:ℝ)]]
theorem cell3_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 2 true ν := by
 have heq : naturalFloor cell3 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_2_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_2_2_g]
def cell3_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(1476022/1859:ℝ), (3054900/1859:ℝ), (1593750/1859:ℝ)]]
theorem cell3_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_2_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_2_2_g]
def cell3_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(277730054687500/1254484803:ℝ), (187239503007500/418161601:ℝ), (282558762500000/1254484803:ℝ)],
  ![(187239503007500/418161601:ℝ), (1762075682226540000/1949051222261:ℝ), (885046126901562500/1949051222261:ℝ)],
  ![(282558762500000/1254484803:ℝ), (885046126901562500/1949051222261:ℝ), (1331877086914062500/5847153666783:ℝ)]]
theorem cell3_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 2 2 b ν := by
 have heq : pairedCleared cell3 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_2_2_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_2_2_g]
theorem cell3_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_2_2 hb hν
def cell3_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(170942826264471199/57185685939750000:ℝ)]]
theorem cell3_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 2 3) := by
 have heq : (-orderedLow cell3 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_2_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_2_3_g]
def cell3_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(2083814215339722782417/1871024146851116400:ℝ), (360981609594920843541/155918678904259700:ℝ), (90816695582461629475/74840965874044656:ℝ)]]
theorem cell3_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 2 3 ν := by
 have heq : mixedLowHigh cell3 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_2_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_2_3_g]
def cell3_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(18528113/20449:ℝ), (39110850/20449:ℝ), (20828125/20449:ℝ)]]
theorem cell3_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 3 false ν := by
 have heq : naturalFloor cell3 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_2_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_2_3_g]
def cell3_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(6342982448711/6898408803:ℝ), (1485933940550/766489867:ℝ), (7113203921875/6898408803:ℝ)]]
theorem cell3_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 3 true ν := by
 have heq : naturalFloor cell3 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_2_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_2_3_g]
def cell3_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(18528113/20449:ℝ), (39110850/20449:ℝ), (20828125/20449:ℝ)]]
theorem cell3_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_2_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_2_3_g]
def cell3_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(113406135546875/418161601:ℝ), (231503634198750/418161601:ℝ), (117382652734375/418161601:ℝ)],
  ![(668896069960000/1254484803:ℝ), (2119984262295675000/1949051222261:ℝ), (3222850161671875000/5847153666783:ℝ)],
  ![(327247971484375/1254484803:ℝ), (1036639591488281250/1949051222261:ℝ), (1575233626708984375/5847153666783:ℝ)]]
theorem cell3_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 2 3 b ν := by
 have heq : pairedCleared cell3 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_2_3_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_2_3_g]
theorem cell3_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_2_3 hb hν
def cell3_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(33149685734837551/14296421484937500:ℝ)]]
theorem cell3_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 2 4) := by
 have heq : (-orderedLow cell3 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_2_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_2_4_g]
def cell3_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(354129640531779846233/467756036712779100:ℝ), (65322322543975217709/38979669726064925:ℝ), (17488893063333089275/18710241468511164:ℝ)]]
theorem cell3_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 2 4 ν := by
 have heq : mixedLowHigh cell3 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_2_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_2_4_g]
def cell3_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(20819984/20449:ℝ), (44617800/20449:ℝ), (24125000/20449:ℝ)]]
theorem cell3_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 4 false ν := by
 have heq : naturalFloor cell3 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_2_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_2_4_g]
def cell3_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(20819984/20449:ℝ), (44617800/20449:ℝ), (24125000/20449:ℝ)]]
theorem cell3_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 4 true ν := by
 have heq : naturalFloor cell3 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_2_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_2_4_g]
def cell3_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(20819984/20449:ℝ), (44617800/20449:ℝ), (24125000/20449:ℝ)]]
theorem cell3_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_2_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_2_4_g]
def cell3_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(240700594531250/1254484803:ℝ), (171077234140000/418161601:ℝ), (269671724218750/1254484803:ℝ)],
  ![(545791099647500/1254484803:ℝ), (1784281858239810000/1949051222261:ℝ), (2783075868420312500/5847153666783:ℝ)],
  ![(101220271093750/418161601:ℝ), (982584638106250000/1949051222261:ℝ), (506627020019531250/1949051222261:ℝ)]]
theorem cell3_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 2 4 b ν := by
 have heq : pairedCleared cell3 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_2_4_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_2_4_g]
theorem cell3_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_2_4 hb hν
def cell3_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(173405693257941403/57185685939750000:ℝ)]]
theorem cell3_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 2 5) := by
 have heq : (-orderedLow cell3 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_2_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_2_5_g]
def cell3_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1855991812354543596149/1871024146851116400:ℝ), (340399155758026744377/155918678904259700:ℝ), (90648741587151986575/74840965874044656:ℝ)]]
theorem cell3_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 2 5 ν := by
 have heq : mixedLowHigh cell3 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_2_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_2_5_g]
def cell3_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1777835/1573:ℝ), (3855750/1573:ℝ), (2109375/1573:ℝ)]]
theorem cell3_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 5 false ν := by
 have heq : naturalFloor cell3 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_2_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_2_5_g]
def cell3_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(7704135836185/6898408803:ℝ), (1858884054250/766489867:ℝ), (9163788828125/6898408803:ℝ)]]
theorem cell3_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 5 true ν := by
 have heq : naturalFloor cell3 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_2_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_2_5_g]
def cell3_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(1777835/1573:ℝ), (3855750/1573:ℝ), (2109375/1573:ℝ)]]
theorem cell3_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_2_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_2_5_g]
def cell3_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(303188946484375/1254484803:ℝ), (215341365331250/418161601:ℝ), (339260919921875/1254484803:ℝ)],
  ![(217656220195000/418161601:ℝ), (2142190438308945000/1949051222261:ℝ), (1116929216462500000/1949051222261:ℝ)],
  ![(348350022265625/1254484803:ℝ), (1134178102692968750/1949051222261:ℝ), (1763237599853515625/5847153666783:ℝ)]]
theorem cell3_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 2 5 b ν := by
 have heq : pairedCleared cell3 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_2_5_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_2_5_g]
theorem cell3_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_2_5 hb hν
def cell3_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(107106321788266301/28592842969875000:ℝ)]]
theorem cell3_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 2 6) := by
 have heq : (-orderedLow cell3 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_2_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_2_6_g]
def cell3_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(104339321026453082153/85046552129596200:ℝ), (19068591879097846269/7087212677466350:ℝ), (5060995950953255275/3401862085183848:ℝ)]]
theorem cell3_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 2 6 ν := by
 have heq : mixedLowHigh cell3 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_2_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_2_6_g]
def cell3_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(25403726/20449:ℝ), (55631700/20449:ℝ), (30718750/20449:ℝ)]]
theorem cell3_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 6 false ν := by
 have heq : naturalFloor cell3 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_2_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_2_6_g]
def cell3_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(8384712529922/6898408803:ℝ), (2045359111100/766489867:ℝ), (10189081281250/6898408803:ℝ)]]
theorem cell3_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 2 6 true ν := by
 have heq : naturalFloor cell3 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_2_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_2_6_g]
def cell3_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(25403726/20449:ℝ), (55631700/20449:ℝ), (30718750/20449:ℝ)]]
theorem cell3_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_2_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_2_6_g]
def cell3_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(121892432812500/418161601:ℝ), (259605496522500/418161601:ℝ), (136283371875000/418161601:ℝ)],
  ![(760146221522500/1254484803:ℝ), (2500099018378080000/1949051222261:ℝ), (3918499430354687500/5847153666783:ℝ)],
  ![(393039231250000/1254484803:ℝ), (1285771567279687500/1949051222261:ℝ), (2006594139648437500/5847153666783:ℝ)]]
theorem cell3_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 2 6 b ν := by
 have heq : pairedCleared cell3 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_2_6_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_2_6_g]
theorem cell3_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_2_6 hb hν
def cell3_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(363351410801369/9530947656625000:ℝ)]]
theorem cell3_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 3 1) := by
 have heq : (-orderedLow cell3 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_3_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_3_1_g]
def cell3_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(1237827107091672703/9355120734255582:ℝ), (2174221934948458000/4677560367127791:ℝ), (3148037245742265625/9355120734255582:ℝ)]]
theorem cell3_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 3 1 ν := by
 have heq : mixedLowHigh cell3 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_3_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_3_1_g]
def cell3_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(11643113/61347:ℝ), (35350850/61347:ℝ), (7984375/20449:ℝ)]]
theorem cell3_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 1 false ν := by
 have heq : naturalFloor cell3 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_3_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_3_1_g]
def cell3_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(1216677301237/6898408803:ℝ), (1265230060550/2299469601:ℝ), (2606606515625/6898408803:ℝ)]]
theorem cell3_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 1 true ν := by
 have heq : naturalFloor cell3 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_3_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_3_1_g]
def cell3_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(2903738/61347:ℝ), (18408350/61347:ℝ), (5250000/20449:ℝ)]]
theorem cell3_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_3_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_3_1_g]
def cell3_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (472093453750/8772621:ℝ), (467094531250/8772621:ℝ)],
  ![(81468453750/2924207:ℝ), (2158094430780000/13629728827:ℝ), (1763313213281250/13629728827:ℝ)],
  ![(76469531250/2924207:ℝ), (4138344913281250/40889186481:ℝ), (3047201171875000/40889186481:ℝ)]]
theorem cell3_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 3 1 b ν := by
 have heq : pairedCleared cell3 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_3_1_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_3_1_g]
theorem cell3_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_3_1 hb hν
def cell3_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(67096375356941267/19061895313250000:ℝ)]]
theorem cell3_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 3 2) := by
 have heq : (-orderedLow cell3 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_3_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_3_2_g]
def cell3_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(4792517404227191428/4677560367127791:ℝ), (9594898601417794100/4677560367127791:ℝ), (4839801680127625000/4677560367127791:ℝ)]]
theorem cell3_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 3 2 ν := by
 have heq : mixedLowHigh cell3 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_3_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_3_2_g]
def cell3_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(4327402/4719:ℝ), (8695900/4719:ℝ), (1468750/1573:ℝ)]]
theorem cell3_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 2 false ν := by
 have heq : naturalFloor cell3 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_3_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_3_2_g]
def cell3_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(6418535469974/6898408803:ℝ), (4297155306100/2299469601:ℝ), (6528117718750/6898408803:ℝ)]]
theorem cell3_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 2 true ν := by
 have heq : naturalFloor cell3 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_3_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_3_2_g]
def cell3_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(4327402/4719:ℝ), (8695900/4719:ℝ), (1468750/1573:ℝ)]]
theorem cell3_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_3_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_3_2_g]
def cell3_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(113406135546875/418161601:ℝ), (668896069960000/1254484803:ℝ), (327247971484375/1254484803:ℝ)],
  ![(231503634198750/418161601:ℝ), (2119984262295675000/1949051222261:ℝ), (1036639591488281250/1949051222261:ℝ)],
  ![(117382652734375/418161601:ℝ), (3222850161671875000/5847153666783:ℝ), (1575233626708984375/5847153666783:ℝ)]]
theorem cell3_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 3 2 b ν := by
 have heq : pairedCleared cell3 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_3_2_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_3_2_g]
theorem cell3_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_3_2 hb hν
def cell3_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(1865590860731/381237906265:ℝ)]]
theorem cell3_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 3 3) := by
 have heq : (-orderedLow cell3 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_3_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_3_3_g]
def cell3_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(2499663676665664464/1559186789042597:ℝ), (5089292590444559550/1559186789042597:ℝ), (2608339155247406250/1559186789042597:ℝ)]]
theorem cell3_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 3 3 ν := by
 have heq : mixedLowHigh cell3 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_3_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_3_3_g]
def cell3_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(30180613/20449:ℝ), (61700850/20449:ℝ), (31765625/20449:ℝ)]]
theorem cell3_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 3 false ν := by
 have heq : naturalFloor cell3 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_3_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_3_3_g]
def cell3_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(3486358863737/2299469601:ℝ), (2372558810550/766489867:ℝ), (3658911203125/2299469601:ℝ)]]
theorem cell3_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 3 true ν := by
 have heq : naturalFloor cell3 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_3_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_3_3_g]
def cell3_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(30180613/20449:ℝ), (61700850/20449:ℝ), (31765625/20449:ℝ)]]
theorem cell3_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_3_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_3_3_g]
def cell3_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(172810216406250/418161601:ℝ), (346666748261250/418161601:ℝ), (173141685937500/418161601:ℝ)],
  ![(346666748261250/418161601:ℝ), (3237750036864810000/1949051222261:ℝ), (1615476975508593750/1949051222261:ℝ)],
  ![(173141685937500/418161601:ℝ), (1615476975508593750/1949051222261:ℝ), (805336126464843750/1949051222261:ℝ)]]
theorem cell3_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 3 3 b ν := by
 have heq : pairedCleared cell3 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_3_3_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_3_3_g]
theorem cell3_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_3_3 hb hν
def cell3_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(100782053309173733/19061895313250000:ℝ)]]
theorem cell3_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 3 4) := by
 have heq : (-orderedLow cell3 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_3_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_3_4_g]
def cell3_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(104214232188673380849/56697701419730800:ℝ), (53458102238780166231/14174425354932700:ℝ), (4421013599566519075/2267908056789232:ℝ)]]
theorem cell3_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 3 4 ν := by
 have heq : mixedLowHigh cell3 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_3_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_3_4_g]
def cell3_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2952044/1859:ℝ), (6109800/1859:ℝ), (3187500/1859:ℝ)]]
theorem cell3_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 4 false ν := by
 have heq : naturalFloor cell3 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_3_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_3_4_g]
def cell3_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(11139653284948/6898408803:ℝ), (2559033867400/766489867:ℝ), (12002026062500/6898408803:ℝ)]]
theorem cell3_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 4 true ν := by
 have heq : naturalFloor cell3 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_3_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_3_4_g]
def cell3_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(2952044/1859:ℝ), (6109800/1859:ℝ), (3187500/1859:ℝ)]]
theorem cell3_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_3_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_3_4_g]
def cell3_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(580919001171875/1254484803:ℝ), (390930879452500/418161601:ℝ), (589014253515625/1254484803:ℝ)],
  ![(1147177805721250/1254484803:ℝ), (3595658616933945000/1949051222261:ℝ), (5414142707492968750/5847153666783:ℝ)],
  ![(564114266796875/1254484803:ℝ), (1767070440095312500/1949051222261:ℝ), (2659364919189453125/5847153666783:ℝ)]]
theorem cell3_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 3 4 b ν := by
 have heq : pairedCleared cell3 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_3_4_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_3_4_g]
theorem cell3_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_3_4 hb hν
def cell3_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(22000173050200017/4765473828312500:ℝ)]]
theorem cell3_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 3 5) := by
 have heq : (-orderedLow cell3 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_3_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_3_5_g]
def cell3_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(230981167417801514211/155918678904259700:ℝ), (122086701301890463959/38979669726064925:ℝ), (10419360454713821425/6236747156170388:ℝ)]]
theorem cell3_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 3 5 ν := by
 have heq : mixedLowHigh cell3 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_3_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_3_5_g]
def cell3_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(34764355/20449:ℝ), (72714750/20449:ℝ), (38359375/20449:ℝ)]]
theorem cell3_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 5 false ν := by
 have heq : naturalFloor cell3 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_3_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_3_5_g]
def cell3_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(11820229978685/6898408803:ℝ), (2745508924250/766489867:ℝ), (13027318515625/6898408803:ℝ)]]
theorem cell3_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 5 true ν := by
 have heq : naturalFloor cell3 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_3_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_3_5_g]
def cell3_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(34764355/20449:ℝ), (72714750/20449:ℝ), (38359375/20449:ℝ)]]
theorem cell3_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_3_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_3_5_g]
def cell3_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(481401189062500/1254484803:ℝ), (330504479393750/418161601:ℝ), (506538019531250/1254484803:ℝ)],
  ![(1024072835408750/1254484803:ℝ), (3259956212878080000/1949051222261:ℝ), (4974368414241406250/5847153666783:ℝ)],
  ![(540527108593750/1254484803:ℝ), (1713015486713281250/1949051222261:ℝ), (2604012352539062500/5847153666783:ℝ)]]
theorem cell3_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 3 5 b ν := by
 have heq : pairedCleared cell3 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_3_5_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_3_5_g]
theorem cell3_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_3_5 hb hν
def cell3_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(101603008973663801/19061895313250000:ℝ)]]
theorem cell3_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 3 6) := by
 have heq : (-orderedLow cell3 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_3_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_3_6_g]
def cell3_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(1070415753080347460583/623674715617038800:ℝ), (567456670789687729377/155918678904259700:ℝ), (48575164930128495525/24946988624681552:ℝ)]]
theorem cell3_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 3 6 ν := by
 have heq : mixedLowHigh cell3 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_3_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_3_6_g]
def cell3_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(37056226/20449:ℝ), (78221700/20449:ℝ), (41656250/20449:ℝ)]]
theorem cell3_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 6 false ν := by
 have heq : naturalFloor cell3 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_3_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_3_6_g]
def cell3_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(37056226/20449:ℝ), (78221700/20449:ℝ), (41656250/20449:ℝ)]]
theorem cell3_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 3 6 true ν := by
 have heq : naturalFloor cell3 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_3_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_3_6_g]
def cell3_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(37056226/20449:ℝ), (78221700/20449:ℝ), (41656250/20449:ℝ)]]
theorem cell3_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_3_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_3_6_g]
def cell3_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(181296513671875/418161601:ℝ), (374768610585000/418161601:ℝ), (192042405078125/418161601:ℝ)],
  ![(377083465448750/418161601:ℝ), (3617864792947215000/1949051222261:ℝ), (1847360065069531250/1949051222261:ℝ)],
  ![(195072105859375/418161601:ℝ), (1864608951300000000/1949051222261:ℝ), (949122964111328125/1949051222261:ℝ)]]
theorem cell3_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 3 6 b ν := by
 have heq : pairedCleared cell3 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_3_6_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_3_6_g]
theorem cell3_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_3_6 hb hν
def cell3_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(18555298361853403/11437137187950000:ℝ)]]
theorem cell3_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 4 1) := by
 have heq : (-orderedLow cell3 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_4_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_4_1_g]
def cell3_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(1953607626296959489/4677560367127791:ℝ), (1526318789484592150/1559186789042597:ℝ), (2644058983625328125/4677560367127791:ℝ)]]
theorem cell3_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 4 1 ν := by
 have heq : mixedLowHigh cell3 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_4_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_4_1_g]
def cell3_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(12223121/20449:ℝ), (27156950/20449:ℝ), (15015625/20449:ℝ)]]
theorem cell3_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 1 false ν := by
 have heq : naturalFloor cell3 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_4_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_4_1_g]
def cell3_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(3938274974987/6898408803:ℝ), (978040056850/766489867:ℝ), (4891679171875/6898408803:ℝ)]]
theorem cell3_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 1 true ν := by
 have heq : naturalFloor cell3 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_4_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_4_1_g]
def cell3_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(492067/1573:ℝ), (1220150/1573:ℝ), (734375/1573:ℝ)]]
theorem cell3_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_4_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_4_1_g]
def cell3_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(62488351953125/1254484803:ℝ), (58228974941250/418161601:ℝ), (111483726953125/1254484803:ℝ)],
  ![(55914120077500/418161601:ℝ), (666516083670675000/1949051222261:ℝ), (403747254085937500/1949051222261:ℝ)],
  ![(102394624609375/1254484803:ℝ), (386498367855468750/1949051222261:ℝ), (679106307373046875/5847153666783:ℝ)]]
theorem cell3_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 4 1 b ν := by
 have heq : pairedCleared cell3 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_4_1_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_4_1_g]
theorem cell3_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_4_1 hb hν
def cell3_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(66791721063929107/28592842969875000:ℝ)]]
theorem cell3_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 4 2) := by
 have heq : (-orderedLow cell3 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_4_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_4_2_g]
def cell3_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(2671368113841388877/3118373578085194:ℝ), (8985947385898287550/4677560367127791:ℝ), (10032631396146453125/9355120734255582:ℝ)]]
theorem cell3_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 4 2 ν := by
 have heq : mixedLowHigh cell3 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_4_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_4_2_g]
def cell3_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(53476226/61347:ℝ), (119641700/61347:ℝ), (22218750/20449:ℝ)]]
theorem cell3_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 2 false ν := by
 have heq : naturalFloor cell3 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_4_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_4_2_g]
def cell3_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(53476226/61347:ℝ), (119641700/61347:ℝ), (22218750/20449:ℝ)]]
theorem cell3_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 2 true ν := by
 have heq : naturalFloor cell3 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_4_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_4_2_g]
def cell3_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(16854367/20449:ℝ), (113994200/61347:ℝ), (63921875/61347:ℝ)]]
theorem cell3_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_4_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_4_2_g]
def cell3_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(240700594531250/1254484803:ℝ), (545791099647500/1254484803:ℝ), (101220271093750/418161601:ℝ)],
  ![(171077234140000/418161601:ℝ), (1784281858239810000/1949051222261:ℝ), (982584638106250000/1949051222261:ℝ)],
  ![(269671724218750/1254484803:ℝ), (2783075868420312500/5847153666783:ℝ), (506627020019531250/1949051222261:ℝ)]]
theorem cell3_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 4 2 b ν := by
 have heq : pairedCleared cell3 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_4_2_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_4_2_g]
theorem cell3_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_4_2 hb hν
def cell3_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(332692459733873801/57185685939750000:ℝ)]]
theorem cell3_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 4 3) := by
 have heq : (-orderedLow cell3 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_4_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_4_3_g]
def cell3_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(8180656021443438392/4677560367127791:ℝ), (16406624052367623650/4677560367127791:ℝ), (2760699585109906250/1559186789042597:ℝ)]]
theorem cell3_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 4 3 ν := by
 have heq : mixedLowHigh cell3 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_4_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_4_3_g]
def cell3_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(98089339/61347:ℝ), (197337550/61347:ℝ), (33328125/20449:ℝ)]]
theorem cell3_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 3 false ν := by
 have heq : naturalFloor cell3 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_4_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_4_3_g]
def cell3_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(11215206306211/6898408803:ℝ), (7516455086650/2299469601:ℝ), (11416939859375/6898408803:ℝ)]]
theorem cell3_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 3 true ν := by
 have heq : naturalFloor cell3 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_4_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_4_3_g]
def cell3_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(98089339/61347:ℝ), (197337550/61347:ℝ), (33328125/20449:ℝ)]]
theorem cell3_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_4_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_4_3_g]
def cell3_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(580919001171875/1254484803:ℝ), (1147177805721250/1254484803:ℝ), (564114266796875/1254484803:ℝ)],
  ![(390930879452500/418161601:ℝ), (3595658616933945000/1949051222261:ℝ), (1767070440095312500/1949051222261:ℝ)],
  ![(589014253515625/1254484803:ℝ), (5414142707492968750/5847153666783:ℝ), (2659364919189453125/5847153666783:ℝ)]]
theorem cell3_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 4 3 b ν := by
 have heq : pairedCleared cell3 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_4_3_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_4_3_g]
theorem cell3_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_4_3 hb hν
def cell3_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(8224839255454/1143713718795:ℝ)]]
theorem cell3_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 4 4) := by
 have heq : (-orderedLow cell3 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_4_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_4_4_g]
def cell3_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(837471511324095412/359812335932907:ℝ), (566143672366243800/119937445310969:ℝ), (866716503149562500/359812335932907:ℝ)]]
theorem cell3_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 4 4 ν := by
 have heq : mixedLowHigh cell3 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_4_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_4_4_g]
def cell3_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(44124984/20449:ℝ), (89797800/20449:ℝ), (46000000/20449:ℝ)]]
theorem cell3_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 4 false ν := by
 have heq : naturalFloor cell3 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_4_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_4_4_g]
def cell3_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(1386886129768/627128073:ℝ), (313241703400/69680897:ℝ), (1442323250000/627128073:ℝ)]]
theorem cell3_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 4 true ν := by
 have heq : naturalFloor cell3 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_4_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_4_4_g]
def cell3_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(44124984/20449:ℝ), (89797800/20449:ℝ), (46000000/20449:ℝ)]]
theorem cell3_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_4_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_4_4_g]
def cell3_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(69011931250000/114044073:ℝ), (46008544865000/38014691:ℝ), (68753759375000/114044073:ℝ)],
  ![(46008544865000/38014691:ℝ), (428493126500280000/177186474751:ℝ), (213264347646875000/177186474751:ℝ)],
  ![(68753759375000/114044073:ℝ), (213264347646875000/177186474751:ℝ), (318194515625000000/531559424253:ℝ)]]
theorem cell3_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 4 4 b ν := by
 have heq : pairedCleared cell3 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_4_4_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_4_4_g]
theorem cell3_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_4_4 hb hν
def cell3_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(433749493590571199/57185685939750000:ℝ)]]
theorem cell3_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 4 5) := by
 have heq : (-orderedLow cell3 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_4_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_4_5_g]
def cell3_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(4794325109112720353617/1871024146851116400:ℝ), (815096639658242813541/155918678904259700:ℝ), (200970201988928629475/74840965874044656:ℝ)]]
theorem cell3_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 4 5 ν := by
 have heq : mixedLowHigh cell3 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_4_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_4_5_g]
def cell3_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(46416855/20449:ℝ), (95304750/20449:ℝ), (49296875/20449:ℝ)]]
theorem cell3_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 5 false ν := by
 have heq : naturalFloor cell3 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_4_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_4_5_g]
def cell3_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(31432591955/13606329:ℝ), (279394907250/58960759:ℝ), (433098671875/176882277:ℝ)]]
theorem cell3_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 5 true ν := by
 have heq : naturalFloor cell3 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_4_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_4_5_g]
def cell3_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(46416855/20449:ℝ), (95304750/20449:ℝ), (49296875/20449:ℝ)]]
theorem cell3_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_4_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_4_5_g]
def cell3_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(821619595703125/1254484803:ℝ), (550358124706250/418161601:ℝ), (825880548828125/1254484803:ℝ)],
  ![(1625459541482500/1254484803:ℝ), (5071332971572215000/1949051222261:ℝ), (7605435253314062500/5847153666783:ℝ)],
  ![(266993520703125/418161601:ℝ), (2497501288702343750/1949051222261:ℝ), (1247832070556640625/1949051222261:ℝ)]]
theorem cell3_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 4 5 b ν := by
 have heq : pairedCleared cell3 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_4_5_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_4_5_g]
theorem cell3_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_4_5 hb hν
def cell3_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(98851352566362551/14296421484937500:ℝ)]]
theorem cell3_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 4 6) := by
 have heq : (-orderedLow cell3 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_4_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_4_6_g]
def cell3_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(1031757363975029239033/467756036712779100:ℝ), (178851080059805710209/38979669726064925:ℝ), (45027269664949839275/18710241468511164:ℝ)]]
theorem cell3_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 4 6 ν := by
 have heq : mixedLowHigh cell3 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_4_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_4_6_g]
def cell3_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(4428066/1859:ℝ), (9164700/1859:ℝ), (4781250/1859:ℝ)]]
theorem cell3_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 6 false ν := by
 have heq : naturalFloor cell3 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_4_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_4_6_g]
def cell3_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(16616900814922/6898408803:ℝ), (3818608851100/766489867:ℝ), (17916140656250/6898408803:ℝ)]]
theorem cell3_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 4 6 true ν := by
 have heq : naturalFloor cell3 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_4_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_4_6_g]
def cell3_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(4428066/1859:ℝ), (9164700/1859:ℝ), (4781250/1859:ℝ)]]
theorem cell3_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_4_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_4_6_g]
def cell3_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(240700594531250/418161601:ℝ), (489931724647500/418161601:ℝ), (247801438281250/418161601:ℝ)],
  ![(1502354571170000/1254484803:ℝ), (4735630567516350000/1949051222261:ℝ), (7165660960062500000/5847153666783:ℝ)],
  ![(777393403906250/1254484803:ℝ), (2443446335320312500/1949051222261:ℝ), (3688143645019531250/5847153666783:ℝ)]]
theorem cell3_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 4 6 b ν := by
 have heq : pairedCleared cell3 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_4_6_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_4_6_g]
theorem cell3_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_4_6 hb hν
def cell3_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(22921609394215727/7148210742468750:ℝ)]]
theorem cell3_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 5 1) := by
 have heq : (-orderedLow cell3 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_5_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_5_1_g]
def cell3_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(2192201132698721751/3118373578085194:ℝ), (6983690801959094900/4677560367127791:ℝ), (7428198688759046875/9355120734255582:ℝ)]]
theorem cell3_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 5 1 ν := by
 have heq : mixedLowHigh cell3 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_5_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_5_1_g]
def cell3_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(61695613/61347:ℝ), (127590850/61347:ℝ), (22046875/20449:ℝ)]]
theorem cell3_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 1 false ν := by
 have heq : naturalFloor cell3 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_5_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_5_1_g]
def cell3_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(201814322689/209042691:ℝ), (418455480050/209042691:ℝ), (217477328125/209042691:ℝ)]]
theorem cell3_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 1 true ν := by
 have heq : naturalFloor cell3 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_5_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_5_1_g]
def cell3_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(35477488/61347:ℝ), (76763350/61347:ℝ), (13843750/20449:ℝ)]]
theorem cell3_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_5_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_5_1_g]
def cell3_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(124976703906250/1254484803:ℝ), (281864485761250/1254484803:ℝ), (52057645312500/418161601:ℝ)],
  ![(100178251268750/418161601:ℝ), (1024424663739810000/1949051222261:ℝ), (555340718672656250/1949051222261:ℝ)],
  ![(171983820312500/1254484803:ℝ), (1727206884533593750/5847153666783:ℝ), (307487615722656250/1949051222261:ℝ)]]
theorem cell3_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 5 1 b ν := by
 have heq : pairedCleared cell3 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_5_1_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_5_1_g]
theorem cell3_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_5_1 hb hν
def cell3_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(44835965094463403/11437137187950000:ℝ)]]
theorem cell3_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 5 2) := by
 have heq : (-orderedLow cell3 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_5_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_5_2_g]
def cell3_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(5341746243513206453/4677560367127791:ℝ), (3796893939801202000/1559186789042597:ℝ), (6086356058827421875/4677560367127791:ℝ)]]
theorem cell3_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 5 2 ν := by
 have heq : mixedLowHigh cell3 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_5_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_5_2_g]
def cell3_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(2012884/1573:ℝ), (4250300/1573:ℝ), (2250000/1573:ℝ)]]
theorem cell3_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 2 false ν := by
 have heq : naturalFloor cell3 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_5_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_5_2_g]
def cell3_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(8734945811224/6898408803:ℝ), (2051139983700/766489867:ℝ), (9780501312500/6898408803:ℝ)]]
theorem cell3_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 2 true ν := by
 have heq : naturalFloor cell3 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_5_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_5_2_g]
def cell3_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(66849976/61347:ℝ), (47723900/20449:ℝ), (76812500/61347:ℝ)]]
theorem cell3_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_5_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_5_2_g]
def cell3_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(303188946484375/1254484803:ℝ), (217656220195000/418161601:ℝ), (348350022265625/1254484803:ℝ)],
  ![(215341365331250/418161601:ℝ), (2142190438308945000/1949051222261:ℝ), (1134178102692968750/1949051222261:ℝ)],
  ![(339260919921875/1254484803:ℝ), (1116929216462500000/1949051222261:ℝ), (1763237599853515625/5847153666783:ℝ)]]
theorem cell3_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 5 2 b ν := by
 have heq : pairedCleared cell3 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_5_2_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_5_2_g]
theorem cell3_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_5_2 hb hν
def cell3_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(132493387895454107/28592842969875000:ℝ)]]
theorem cell3_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 5 3) := by
 have heq : (-orderedLow cell3 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_5_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_5_3_g]
def cell3_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(14790381575956660559/9355120734255582:ℝ), (15797672836848117100/4677560367127791:ℝ), (5639075182183546875/3118373578085194:ℝ)]]
theorem cell3_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 5 3 ν := by
 have heq : mixedLowHigh cell3 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_5_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_5_3_g]
def cell3_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(95309339/61347:ℝ), (203932550/61347:ℝ), (36453125/20449:ℝ)]]
theorem cell3_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 3 false ν := by
 have heq : naturalFloor cell3 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_5_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_5_3_g]
def cell3_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(10810018973711/6898408803:ℝ), (7703829621650/2299469601:ℝ), (12384250796875/6898408803:ℝ)]]
theorem cell3_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 3 true ν := by
 have heq : naturalFloor cell3 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_5_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_5_3_g]
def cell3_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(95309339/61347:ℝ), (203932550/61347:ℝ), (36453125/20449:ℝ)]]
theorem cell3_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_5_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_5_3_g]
def cell3_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(481401189062500/1254484803:ℝ), (1024072835408750/1254484803:ℝ), (540527108593750/1254484803:ℝ)],
  ![(330504479393750/418161601:ℝ), (3259956212878080000/1949051222261:ℝ), (1713015486713281250/1949051222261:ℝ)],
  ![(506538019531250/1254484803:ℝ), (4974368414241406250/5847153666783:ℝ), (2604012352539062500/5847153666783:ℝ)]]
theorem cell3_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 5 3 b ν := by
 have heq : pairedCleared cell3 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_5_3_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_5_3_g]
theorem cell3_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_5_3 hb hν
def cell3_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(464095793396923801/57185685939750000:ℝ)]]
theorem cell3_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 5 4) := by
 have heq : (-orderedLow cell3 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_5_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_5_4_g]
def cell3_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(3856264879553228452/1559186789042597:ℝ), (23218349503317453200/4677560367127791:ℝ), (11724395830531812500/4677560367127791:ℝ)]]
theorem cell3_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 5 4 ν := by
 have heq : mixedLowHigh cell3 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_5_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_5_4_g]
def cell3_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(139922452/61347:ℝ), (281628400/61347:ℝ), (47562500/20449:ℝ)]]
theorem cell3_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 4 false ν := by
 have heq : naturalFloor cell3 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_5_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_5_4_g]
def cell3_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(161736132752/69680897:ℝ), (975977715200/209042691:ℝ), (494114000000/209042691:ℝ)]]
theorem cell3_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 4 true ν := by
 have heq : naturalFloor cell3 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_5_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_5_4_g]
def cell3_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(139922452/61347:ℝ), (281628400/61347:ℝ), (47562500/20449:ℝ)]]
theorem cell3_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_5_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_5_4_g]
def cell3_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(821619595703125/1254484803:ℝ), (1625459541482500/1254484803:ℝ), (266993520703125/418161601:ℝ)],
  ![(550358124706250/418161601:ℝ), (5071332971572215000/1949051222261:ℝ), (2497501288702343750/1949051222261:ℝ)],
  ![(825880548828125/1254484803:ℝ), (7605435253314062500/5847153666783:ℝ), (1247832070556640625/1949051222261:ℝ)]]
theorem cell3_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 5 4 b ν := by
 have heq : pairedCleared cell3 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_5_4_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_5_4_g]
theorem cell3_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_5_4 hb hν
def cell3_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(2170581185743/228742743759:ℝ)]]
theorem cell3_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 5 5) := by
 have heq : (-orderedLow cell3 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_5_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_5_5_g]
def cell3_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(14275268264429487320/4677560367127791:ℝ), (9630442891077779250/1559186789042597:ℝ), (14709611616146406250/4677560367127791:ℝ)]]
theorem cell3_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 5 5 ν := by
 have heq : mixedLowHigh cell3 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_5_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_5_5_g]
def cell3_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(58069355/20449:ℝ), (117894750/20449:ℝ), (60234375/20449:ℝ)]]
theorem cell3_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 5 false ν := by
 have heq : naturalFloor cell3 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_5_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_5_5_g]
def cell3_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(20052418263685/6898408803:ℝ), (4518758664250/766489867:ℝ), (20754377890625/6898408803:ℝ)]]
theorem cell3_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 5 true ν := by
 have heq : naturalFloor cell3 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_5_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_5_5_g]
def cell3_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(58069355/20449:ℝ), (117894750/20449:ℝ), (60234375/20449:ℝ)]]
theorem cell3_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_5_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_5_5_g]
def cell3_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(76910141406250/96498831:ℝ), (51193941443750/32166277:ℝ), (76396742187500/96498831:ℝ)],
  ![(51193941443750/32166277:ℝ), (476084518933950000/149927017097:ℝ), (236641436363281250/149927017097:ℝ)],
  ![(76396742187500/96498831:ℝ), (236641436363281250/149927017097:ℝ), (352636228027343750/449781051291:ℝ)]]
theorem cell3_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 5 5 b ν := by
 have heq : pairedCleared cell3 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_5_5_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_5_5_g]
theorem cell3_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_5_5 hb hν
def cell3_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(565152827253621199/57185685939750000:ℝ)]]
theorem cell3_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 5 6) := by
 have heq : (-orderedLow cell3 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_5_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_5_6_g]
def cell3_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(6149580555999219139217/1871024146851116400:ℝ), (1042154154689903798541/155918678904259700:ℝ), (256046955192162129475/74840965874044656:ℝ)]]
theorem cell3_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 5 6 ν := by
 have heq : mixedLowHigh cell3 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_5_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_5_6_g]
def cell3_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(60361226/20449:ℝ), (123401700/20449:ℝ), (63531250/20449:ℝ)]]
theorem cell3_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 6 false ν := by
 have heq : naturalFloor cell3 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_5_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_5_6_g]
def cell3_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(1884817723402/627128073:ℝ), (38886229100/6334627:ℝ), (1979970031250/627128073:ℝ)]]
theorem cell3_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 5 6 true ν := by
 have heq : naturalFloor cell3 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_5_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_5_6_g]
def cell3_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(60361226/20449:ℝ), (123401700/20449:ℝ), (63531250/20449:ℝ)]]
theorem cell3_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_5_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_5_6_g]
def cell3_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(354106730078125/418161601:ℝ), (709785369960000/418161601:ℝ), (354248948046875/418161601:ℝ)],
  ![(2103741277243750/1254484803:ℝ), (6547007326210485000/1949051222261:ℝ), (9796727799135156250/5847153666783:ℝ)],
  ![(1037846857421875/1254484803:ℝ), (3227932137309375000/1949051222261:ℝ), (4827627504150390625/5847153666783:ℝ)]]
theorem cell3_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 5 6 b ν := by
 have heq : pairedCleared cell3 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_5_6_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_5_6_g]
theorem cell3_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_5_6 hb hν
def cell3_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(117706764047298937/19061895313250000:ℝ)]]
theorem cell3_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 6 1) := by
 have heq : (-orderedLow cell3 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_6_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_6_1_g]
def cell3_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(1477983606079854957151/935512073425558200:ℝ), (737624539274939436869/233878018356389550:ℝ), (59050263972544200925/37420482937022328:ℝ)]]
theorem cell3_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 6 1 ν := by
 have heq : mixedLowHigh cell3 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_6_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_6_1_g]
def cell3_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(86721863/61347:ℝ), (173710850/61347:ℝ), (29078125/20449:ℝ)]]
theorem cell3_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 1 false ν := by
 have heq : naturalFloor cell3 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_6_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_6_1_g]
def cell3_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(9381470322487/6898408803:ℝ), (6271900390550/2299469601:ℝ), (9461824484375/6898408803:ℝ)]]
theorem cell3_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 1 true ν := by
 have heq : naturalFloor cell3 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_6_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_6_1_g]
def cell3_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(51764363/61347:ℝ), (105940850/61347:ℝ), (18140625/20449:ℝ)]]
theorem cell3_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_6_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_6_1_g]
def cell3_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(116490406640625/418161601:ℝ), (703113640448750/1254484803:ℝ), (352927574609375/1254484803:ℝ)],
  ![(221203226210000/418161601:ℝ), (2075944227933945000/1949051222261:ℝ), (1042762874665625000/1949051222261:ℝ)],
  ![(103283127734375/418161601:ℝ), (2911863919407031250/5847153666783:ℝ), (1464528493408203125/5847153666783:ℝ)]]
theorem cell3_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 6 1 b ν := by
 have heq : pairedCleared cell3 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_6_1_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_6_1_g]
theorem cell3_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_6_1 hb hν
def cell3_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(13115675367365659/2382736914156250:ℝ)]]
theorem cell3_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 6 2) := by
 have heq : (-orderedLow cell3 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_6_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_6_2_g]
def cell3_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(13352880632528659181/9355120734255582:ℝ), (13795416252908924450/4677560367127791:ℝ), (14312792839163234375/9355120734255582:ℝ)]]
theorem cell3_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 6 2 ν := by
 have heq : mixedLowHigh cell3 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_6_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_6_2_g]
def cell3_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(103528726/61347:ℝ), (211881700/61347:ℝ), (36281250/20449:ℝ)]]
theorem cell3_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 2 false ν := by
 have heq : naturalFloor cell3 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_6_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_6_2_g]
def cell3_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(11456543484974/6898408803:ℝ), (7822310061100/2299469601:ℝ), (12065573968750/6898408803:ℝ)]]
theorem cell3_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 2 true ν := by
 have heq : naturalFloor cell3 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_6_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_6_2_g]
def cell3_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(83136851/61347:ℝ), (172349200/61347:ℝ), (89703125/61347:ℝ)]]
theorem cell3_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_6_2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_6_2_g]
def cell3_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(121892432812500/418161601:ℝ), (760146221522500/1254484803:ℝ), (393039231250000/1254484803:ℝ)],
  ![(259605496522500/418161601:ℝ), (2500099018378080000/1949051222261:ℝ), (1285771567279687500/1949051222261:ℝ)],
  ![(136283371875000/418161601:ℝ), (3918499430354687500/5847153666783:ℝ), (2006594139648437500/5847153666783:ℝ)]]
theorem cell3_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 6 2 b ν := by
 have heq : pairedCleared cell3 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_6_2_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_6_2_g]
theorem cell3_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_6_2 hb hν
def cell3_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(23705543942357801/3812379062650000:ℝ)]]
theorem cell3_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 6 3) := by
 have heq : (-orderedLow cell3 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_6_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_6_3_g]
def cell3_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(2909961620243151139/1559186789042597:ℝ), (6067469090117811850/1559186789042597:ℝ), (3176217711343171875/1559186789042597:ℝ)]]
theorem cell3_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 6 3 ν := by
 have heq : mixedLowHigh cell3 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_6_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_6_3_g]
def cell3_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(331503/169:ℝ), (688850/169:ℝ), (359375/169:ℝ)]]
theorem cell3_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 3 false ν := by
 have heq : naturalFloor cell3 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_6_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_6_3_g]
def cell3_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(331503/169:ℝ), (688850/169:ℝ), (359375/169:ℝ)]]
theorem cell3_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 3 true ν := by
 have heq : naturalFloor cell3 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_6_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_6_3_g]
def cell3_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(114509339/61347:ℝ), (79585850/20449:ℝ), (124984375/61347:ℝ)]]
theorem cell3_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_6_3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_6_3_g]
def cell3_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(181296513671875/418161601:ℝ), (377083465448750/418161601:ℝ), (195072105859375/418161601:ℝ)],
  ![(374768610585000/418161601:ℝ), (3617864792947215000/1949051222261:ℝ), (1864608951300000000/1949051222261:ℝ)],
  ![(192042405078125/418161601:ℝ), (1847360065069531250/1949051222261:ℝ), (949122964111328125/1949051222261:ℝ)]]
theorem cell3_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 6 3 b ν := by
 have heq : pairedCleared cell3 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_6_3_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_6_3_g]
theorem cell3_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_6_3 hb hν
def cell3_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(66065018242326369/9530947656625000:ℝ)]]
theorem cell3_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 6 4) := by
 have heq : (-orderedLow cell3 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_6_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_6_4_g]
def cell3_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(21566658810389154487/9355120734255582:ℝ), (22609398287797946650/4677560367127791:ℝ), (23801819696954828125/9355120734255582:ℝ)]]
theorem cell3_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 6 4 ν := by
 have heq : mixedLowHigh cell3 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_6_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_6_4_g]
def cell3_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(137142452/61347:ℝ), (288223400/61347:ℝ), (50687500/20449:ℝ)]]
theorem cell3_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 4 false ν := by
 have heq : naturalFloor cell3 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_6_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_6_4_g]
def cell3_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(15606689809948/6898408803:ℝ), (10923129402200/2299469601:ℝ), (17273072937500/6898408803:ℝ)]]
theorem cell3_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 4 true ν := by
 have heq : naturalFloor cell3 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_6_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_6_4_g]
def cell3_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(137142452/61347:ℝ), (288223400/61347:ℝ), (50687500/20449:ℝ)]]
theorem cell3_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_6_4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_6_4_g]
def cell3_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(240700594531250/418161601:ℝ), (1502354571170000/1254484803:ℝ), (777393403906250/1254484803:ℝ)],
  ![(489931724647500/418161601:ℝ), (4735630567516350000/1949051222261:ℝ), (2443446335320312500/1949051222261:ℝ)],
  ![(247801438281250/418161601:ℝ), (7165660960062500000/5847153666783:ℝ), (3688143645019531250/5847153666783:ℝ)]]
theorem cell3_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 6 4 b ν := by
 have heq : pairedCleared cell3 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_6_4_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_6_4_g]
theorem cell3_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_6_4 hb hν
def cell3_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(198499709019991267/19061895313250000:ℝ)]]
theorem cell3_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 6 5) := by
 have heq : (-orderedLow cell3 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_6_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_6_5_g]
def cell3_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(14956933255875932320/4677560367127791:ℝ), (30030074954267282750/4677560367127791:ℝ), (15166692905733906250/4677560367127791:ℝ)]]
theorem cell3_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 6 5 ν := by
 have heq : mixedLowHigh cell3 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_6_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_6_5_g]
def cell3_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(181755565/61347:ℝ), (365919250/61347:ℝ), (61796875/20449:ℝ)]]
theorem cell3_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 5 false ν := by
 have heq : naturalFloor cell3 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_6_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_6_5_g]
def cell3_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(20808547978685/6898408803:ℝ), (13955054647750/2299469601:ℝ), (21194584140625/6898408803:ℝ)]]
theorem cell3_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 5 true ν := by
 have heq : naturalFloor cell3 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_6_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_6_5_g]
def cell3_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(181755565/61347:ℝ), (365919250/61347:ℝ), (61796875/20449:ℝ)]]
theorem cell3_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_6_5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_6_5_g]
def cell3_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(354106730078125/418161601:ℝ), (2103741277243750/1254484803:ℝ), (1037846857421875/1254484803:ℝ)],
  ![(709785369960000/418161601:ℝ), (6547007326210485000/1949051222261:ℝ), (3227932137309375000/1949051222261:ℝ)],
  ![(354248948046875/418161601:ℝ), (9796727799135156250/5847153666783:ℝ), (4827627504150390625/5847153666783:ℝ)]]
theorem cell3_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 6 5 b ν := by
 have heq : pairedCleared cell3 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_6_5_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_6_5_g]
theorem cell3_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_6_5 hb hν
def cell3_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(4493657533992/381237906265:ℝ)]]
theorem cell3_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell3 6 6) := by
 have heq : (-orderedLow cell3 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell3_ordered_6_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordered_6_6_g]
def cell3_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(5887802293881911428/1559186789042597:ℝ), (11901018041394389100/1559186789042597:ℝ), (6050636230449500000/1559186789042597:ℝ)]]
theorem cell3_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell3 6 6 ν := by
 have heq : mixedLowHigh cell3 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_mixed_6_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_mixed_6_6_g]
def cell3_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(72013726/20449:ℝ), (145991700/20449:ℝ), (74468750/20449:ℝ)]]
theorem cell3_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 6 false ν := by
 have heq : naturalFloor cell3 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor0_6_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor0_6_6_g]
def cell3_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(8283029699974/2299469601:ℝ), (5591858591100/766489867:ℝ), (8547733343750/2299469601:ℝ)]]
theorem cell3_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell3 6 6 true ν := by
 have heq : naturalFloor cell3 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_floor1_6_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_floor1_6_6_g]
def cell3_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(72013726/20449:ℝ), (145991700/20449:ℝ), (74468750/20449:ℝ)]]
theorem cell3_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell3_complement_floor_6_6_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement_floor_6_6_g]
def cell3_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(413510810937500/418161601:ℝ), (824948484022500/418161601:ℝ), (410007981250000/418161601:ℝ)],
  ![(824948484022500/418161601:ℝ), (7664773100779620000/1949051222261:ℝ), (3806769521329687500/1949051222261:ℝ)],
  ![(410007981250000/418161601:ℝ), (3806769521329687500/1949051222261:ℝ), (1889467418945312500/1949051222261:ℝ)]]
theorem cell3_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell3 6 6 b ν := by
 have heq : pairedCleared cell3 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell3_paired_cleared_6_6_g (1589/2500:ℝ) (3/4:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_cleared_6_6_g]
theorem cell3_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) : 0 ≤ pairedGap cell3 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell3_paired_cleared_6_6 hb hν
def cell3_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(37082011100293801/57185685939750000:ℝ)]]
theorem cell3_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell3.q/K)+1+17/50*(cell3.q/cell3.priorL)+17/25*(cell3.q/cell3.priorL)*cell3.priorB) := by
 have heq : ((2-17/50-17/25)*(cell3.q/K)+1+17/50*(cell3.q/cell3.priorL)+17/25*(cell3.q/cell3.priorL)*cell3.priorB) = Record12518109.Bernstein.bsum 0 0 (37082011100293801/57185685939750000:ℝ) cell3_increment0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_increment0_g]
def cell3_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(254512318751/508547750000:ℝ)]]
theorem cell3_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell3.q/cell3.priorL)*(1-cell3.priorB)) := by
 have heq : (1+17/25*(cell3.q/cell3.priorL)*(1-cell3.priorB)) = Record12518109.Bernstein.bsum 0 0 (254512318751/508547750000:ℝ) cell3_increment1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_increment1_g]
def cell3_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(1017810831253/2034191000000:ℝ)]]
theorem cell3_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell3.q/cell3.priorL)*(1-cell3.priorB)) := by
 have heq : (1+omega*(cell3.q/cell3.priorL)*(1-cell3.priorB)) = Record12518109.Bernstein.bsum 0 0 (1017810831253/2034191000000:ℝ) cell3_increment2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_increment2_g]
def cell3_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(4822767/40898:ℝ), (14377925/61347:ℝ), (14778325/122694:ℝ)]]
theorem cell3_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (575117/375000:ℝ) cell3_high_increment_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_high_increment_g]
def cell3_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(133758590729/11696828:ℝ), (1089779492663/11696828:ℝ), (1839850571563/11696828:ℝ), (841300003021/11696828:ℝ)]]
theorem cell3_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (133758590729/7812500000:ℝ) cell3_three_gate0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_three_gate0_g]
def cell3_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(2291871/40898:ℝ), (3215079/20449:ℝ), (4301879/40898:ℝ)]]
theorem cell3_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (2291871/3125000:ℝ) cell3_three_gate1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_three_gate1_g]
def cell3_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(1531526529149/13796817606:ℝ), (509014837775/2299469601:ℝ), (1577749767925/13796817606:ℝ)]]
theorem cell3_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell3.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell3.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (20360593511/14056125000:ℝ) cell3_three_gate2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_three_gate2_g]
def cell3_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(321457/674694:ℝ)]]
theorem cell3_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (1-cell3.q/K/3) := by
 have heq : (1-cell3.q/K/3) = Record12518109.Bernstein.bsum 0 0 (321457/674694:ℝ) cell3_paired_margin0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_margin0_g]
def cell3_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(1693603/17478750:ℝ)]]
theorem cell3_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (gamma cell3-13/50) := by
 have heq : (gamma cell3-13/50) = Record12518109.Bernstein.bsum 0 0 (1693603/17478750:ℝ) cell3_paired_margin1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_margin1_g]
def cell3_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(10169/111864:ℝ)]]
theorem cell3_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (cell3.q-gamma cell3) := by
 have heq : (cell3.q-gamma cell3) = Record12518109.Bernstein.bsum 0 0 (10169/111864:ℝ) cell3_paired_margin2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_margin2_g]
def cell3_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(142398341/489405000:ℝ)]]
theorem cell3_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < (min (cell3.q+rho cell3.q) (3/4+rho (3/4))-gamma cell3) := by
 have heq : (min (cell3.q+rho cell3.q) (3/4+rho (3/4))-gamma cell3) = Record12518109.Bernstein.bsum 0 0 (142398341/489405000:ℝ) cell3_paired_margin3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_paired_margin3_g]
theorem cell3_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (1589/2500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell3 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell3_paired_1_1 hb hν
 · exact cell3_paired_1_2 hb hν
 · exact cell3_paired_1_3 hb hν
 · exact cell3_paired_1_4 hb hν
 · exact cell3_paired_1_5 hb hν
 · exact cell3_paired_1_6 hb hν
 · exact cell3_paired_2_1 hb hν
 · exact cell3_paired_2_2 hb hν
 · exact cell3_paired_2_3 hb hν
 · exact cell3_paired_2_4 hb hν
 · exact cell3_paired_2_5 hb hν
 · exact cell3_paired_2_6 hb hν
 · exact cell3_paired_3_1 hb hν
 · exact cell3_paired_3_2 hb hν
 · exact cell3_paired_3_3 hb hν
 · exact cell3_paired_3_4 hb hν
 · exact cell3_paired_3_5 hb hν
 · exact cell3_paired_3_6 hb hν
 · exact cell3_paired_4_1 hb hν
 · exact cell3_paired_4_2 hb hν
 · exact cell3_paired_4_3 hb hν
 · exact cell3_paired_4_4 hb hν
 · exact cell3_paired_4_5 hb hν
 · exact cell3_paired_4_6 hb hν
 · exact cell3_paired_5_1 hb hν
 · exact cell3_paired_5_2 hb hν
 · exact cell3_paired_5_3 hb hν
 · exact cell3_paired_5_4 hb hν
 · exact cell3_paired_5_5 hb hν
 · exact cell3_paired_5_6 hb hν
 · exact cell3_paired_6_1 hb hν
 · exact cell3_paired_6_2 hb hν
 · exact cell3_paired_6_3 hb hν
 · exact cell3_paired_6_4 hb hν
 · exact cell3_paired_6_5 hb hν
 · exact cell3_paired_6_6 hb hν
end
end Record12518109Admission
