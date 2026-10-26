/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell13
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell13_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(222305152543/762475812530:ℝ)]]
theorem cell13_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 1 1) := by
 have heq : (-orderedLow cell13 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_1_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_1_1_g]
def cell13_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(1236350129939937184/10377829541602071:ℝ), (2859720462930653900/10377829541602071:ℝ), (1664881651157125000/10377829541602071:ℝ)]]
theorem cell13_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 1 1 ν := by
 have heq : mixedLowHigh cell13 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_1_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_1_1_g]
def cell13_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(34957684/408321:ℝ), (86074400/408321:ℝ), (52750000/408321:ℝ)]]
theorem cell13_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 1 false ν := by
 have heq : naturalFloor cell13 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_1_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_1_1_g]
def cell13_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(4417776258116/45915288129:ℝ), (10619487355600/45915288129:ℝ), (6385372250000/45915288129:ℝ)]]
theorem cell13_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 1 true ν := by
 have heq : naturalFloor cell13 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_1_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_1_1_g]
def cell13_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(34957684/408321:ℝ), (86074400/408321:ℝ), (52750000/408321:ℝ)]]
theorem cell13_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_1_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_1_1_g]
def cell13_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(3486605150000000/166726039041:ℝ), (7862517092380000/166726039041:ℝ), (4299237425000000/166726039041:ℝ)],
  ![(7862517092380000/166726039041:ℝ), (163053584824011640000/1565390780555949:ℝ), (87841612772900000000/1565390780555949:ℝ)],
  ![(4299237425000000/166726039041:ℝ), (87841612772900000000/1565390780555949:ℝ), (46805170562500000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 1 1 b ν := by
 have heq : pairedCleared cell13 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_1_1_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_1_1_g]
theorem cell13_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_1_1 hb hν
def cell13_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(26077208183077167/38123790626500000:ℝ)]]
theorem cell13_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 1 2) := by
 have heq : (-orderedLow cell13 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_1_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_1_2_g]
def cell13_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(13340953865532922159/43849983978600300:ℝ), (29755613274652016009/43849983978600300:ℝ), (335309185618957925/876999679572006:ℝ)]]
theorem cell13_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 1 2 ν := by
 have heq : mixedLowHigh cell13 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_1_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_1_2_g]
def cell13_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(69915368/408321:ℝ), (172148800/408321:ℝ), (105500000/408321:ℝ)]]
theorem cell13_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 2 false ν := by
 have heq : naturalFloor cell13 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_1_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_1_2_g]
def cell13_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(69915368/408321:ℝ), (172148800/408321:ℝ), (105500000/408321:ℝ)]]
theorem cell13_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 2 true ν := by
 have heq : naturalFloor cell13 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_1_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_1_2_g]
def cell13_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(69915368/408321:ℝ), (172148800/408321:ℝ), (105500000/408321:ℝ)]]
theorem cell13_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_1_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_1_2_g]
def cell13_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(9177043325000000/166726039041:ℝ), (19982710959760000/166726039041:ℝ), (10652318600000000/166726039041:ℝ)],
  ![(17524861517380000/166726039041:ℝ), (358754237634417460000/1565390780555949:ℝ), (191431714706225000000/1565390780555949:ℝ)],
  ![(8271143675000000/166726039041:ℝ), (169745765362475000000/1565390780555949:ℝ), (90746193343750000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 1 2 b ν := by
 have heq : pairedCleared cell13 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_1_2_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_1_2_g]
theorem cell13_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_1_2 hb hν
def cell13_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(54379567232833/9530947656625000:ℝ)]]
theorem cell13_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 1 3) := by
 have heq : (-orderedLow cell13 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_1_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_1_3_g]
def cell13_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(7515190854656846011/778337215620155325:ℝ), (120530849003576848361/778337215620155325:ℝ), (4894228189454474650/31133488624806213:ℝ)]]
theorem cell13_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 1 3 ν := by
 have heq : mixedLowHigh cell13 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_1_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_1_3_g]
def cell13_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(34957684/136107:ℝ), (86074400/136107:ℝ), (52750000/136107:ℝ)]]
theorem cell13_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 3 false ν := by
 have heq : naturalFloor cell13 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_1_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_1_3_g]
def cell13_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(11306050174348/45915288129:ℝ), (28096433466800/45915288129:ℝ), (17341366750000/45915288129:ℝ)]]
theorem cell13_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 3 true ν := by
 have heq : naturalFloor cell13 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_1_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_1_3_g]
def cell13_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(34957684/136107:ℝ), (86074400/136107:ℝ), (52750000/136107:ℝ)]]
theorem cell13_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_1_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_1_3_g]
def cell13_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (1763066420000/86972373:ℝ), (1643075000000/86972373:ℝ)],
  ![(30289199260000/782751357:ℝ), (837238141508560000/7349252490873:ℝ), (533264130350000000/7349252490873:ℝ)],
  ![(29929225000000/782751357:ℝ), (681727692850000000/7349252490873:ℝ), (391272875000000000/7349252490873:ℝ)]]
theorem cell13_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 1 3 b ν := by
 have heq : pairedCleared cell13 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_1_3_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_1_3_g]
theorem cell13_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_1_3 hb hν
def cell13_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(27379081825338499/38123790626500000:ℝ)]]
theorem cell13_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 1 4) := by
 have heq : (-orderedLow cell13 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_1_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_1_4_g]
def cell13_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(202121149629827900711/1037782954160207100:ℝ), (578951933211801453361/1037782954160207100:ℝ), (7868706216970737325/20755659083204142:ℝ)]]
theorem cell13_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 1 4 ν := by
 have heq : mixedLowHigh cell13 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_1_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_1_4_g]
def cell13_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(139830736/408321:ℝ), (344297600/408321:ℝ), (211000000/408321:ℝ)]]
theorem cell13_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 4 false ν := by
 have heq : naturalFloor cell13 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_1_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_1_4_g]
def cell13_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(14750187132464/45915288129:ℝ), (36834906522400/45915288129:ℝ), (22819364000000/45915288129:ℝ)]]
theorem cell13_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 4 true ν := by
 have heq : naturalFloor cell13 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_1_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_1_4_g]
def cell13_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(139830736/408321:ℝ), (344297600/408321:ℝ), (211000000/408321:ℝ)]]
theorem cell13_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_1_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_1_4_g]
def cell13_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(1896812725000000/55575346347:ℝ), (5166664064840000/55575346347:ℝ), (3167618650000000/55575346347:ℝ)],
  ![(5371314622460000/55575346347:ℝ), (124677458983909700000/521796926851983:ℝ), (72391787232625000000/521796926851983:ℝ)],
  ![(3448943725000000/55575346347:ℝ), (75704050388875000000/521796926851983:ℝ), (42427381718750000000/521796926851983:ℝ)]]
theorem cell13_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 1 4 b ν := by
 have heq : pairedCleared cell13 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_1_4_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_1_4_g]
theorem cell13_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_1_4 hb hν
def cell13_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(27270322690872833/19061895313250000:ℝ)]]
theorem cell13_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 1 5) := by
 have heq : (-orderedLow cell13 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_1_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_1_5_g]
def cell13_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(591333067180170010111/1556674431240310650:ℝ), (1495794101628250663361/1556674431240310650:ℝ), (18711890461457737325/31133488624806213:ℝ)]]
theorem cell13_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 1 5 ν := by
 have heq : mixedLowHigh cell13 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_1_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_1_5_g]
def cell13_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(174788420/408321:ℝ), (430372000/408321:ℝ), (263750000/408321:ℝ)]]
theorem cell13_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 5 false ν := by
 have heq : naturalFloor cell13 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_1_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_1_5_g]
def cell13_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(2021591565620/5101698681:ℝ), (5063708842000/5101698681:ℝ), (3144151250000/5101698681:ℝ)]]
theorem cell13_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 5 true ν := by
 have heq : naturalFloor cell13 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_1_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_1_5_g]
def cell13_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(174788420/408321:ℝ), (430372000/408321:ℝ), (263750000/408321:ℝ)]]
theorem cell13_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_1_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_1_5_g]
def cell13_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(3793625450000000/55575346347:ℝ), (9206728687300000/55575346347:ℝ), (5285312375000000/55575346347:ℝ)],
  ![(8592096097460000/55575346347:ℝ), (189911009920711640000/521796926851983:ℝ), (106921821210400000000/521796926851983:ℝ)],
  ![(1590970825000000/18525115449:ℝ), (34335144861800000000/173932308950661:ℝ), (6341598812500000000/57977436316887:ℝ)]]
theorem cell13_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 1 5 b ν := by
 have heq : pairedCleared cell13 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_1_5_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_1_5_g]
theorem cell13_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_1_5 hb hν
def cell13_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(187744715879258837/38123790626500000:ℝ)]]
theorem cell13_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 1 6) := by
 have heq : (-orderedLow cell13 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_1_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_1_6_g]
def cell13_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(988783089657483779437/1037782954160207100:ℝ), (1976749479616701097787/1037782954160207100:ℝ), (20257463617181245775/20755659083204142:ℝ)]]
theorem cell13_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 1 6 ν := by
 have heq : mixedLowHigh cell13 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_1_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_1_6_g]
def cell13_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(368096104/408321:ℝ), (737296400/408321:ℝ), (379000000/408321:ℝ)]]
theorem cell13_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 6 false ν := by
 have heq : naturalFloor cell13 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_1_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_1_6_g]
def cell13_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(39444760198696/45915288129:ℝ), (79146214283600/45915288129:ℝ), (40803421000000/45915288129:ℝ)]]
theorem cell13_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 1 6 true ν := by
 have heq : naturalFloor cell13 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_1_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_1_6_g]
def cell13_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(368096104/408321:ℝ), (737296400/408321:ℝ), (379000000/408321:ℝ)]]
theorem cell13_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_1_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_1_6_g]
def cell13_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(31938796025000000/166726039041:ℝ), (60475986429280000/166726039041:ℝ), (28077143300000000/166726039041:ℝ)],
  ![(64161739217380000/166726039041:ℝ), (1141556848876040740000/1565390780555949:ℝ), (530797484939525000000/1565390780555949:ℝ)],
  ![(32146268675000000/166726039041:ℝ), (572357013220775000000/1565390780555949:ℝ), (266510284468750000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 1 6 b ν := by
 have heq : pairedCleared cell13 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_1_6_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_1_6_g]
theorem cell13_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_1_6 hb hν
def cell13_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(46154831137402833/38123790626500000:ℝ)]]
theorem cell13_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 2 1) := by
 have heq : (-orderedLow cell13 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_2_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_2_1_g]
def cell13_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(7472871010489001552/31133488624806213:ℝ), (14769541938798651700/31133488624806213:ℝ), (7421204882808875000/31133488624806213:ℝ)]]
theorem cell13_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 2 1 ν := by
 have heq : mixedLowHigh cell13 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_2_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_2_1_g]
def cell13_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(76997684/408321:ℝ), (153114400/408321:ℝ), (77750000/408321:ℝ)]]
theorem cell13_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 1 false ν := by
 have heq : naturalFloor cell13 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_2_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_2_1_g]
def cell13_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(76997684/408321:ℝ), (153114400/408321:ℝ), (77750000/408321:ℝ)]]
theorem cell13_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 1 true ν := by
 have heq : naturalFloor cell13 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_2_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_2_1_g]
def cell13_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(76997684/408321:ℝ), (153114400/408321:ℝ), (77750000/408321:ℝ)]]
theorem cell13_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_2_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_2_1_g]
def cell13_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(9177043325000000/166726039041:ℝ), (17524861517380000/166726039041:ℝ), (8271143675000000/166726039041:ℝ)],
  ![(19982710959760000/166726039041:ℝ), (358754237634417460000/1565390780555949:ℝ), (169745765362475000000/1565390780555949:ℝ)],
  ![(10652318600000000/166726039041:ℝ), (191431714706225000000/1565390780555949:ℝ), (90746193343750000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 2 1 b ν := by
 have heq : pairedCleared cell13 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_2_1_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_2_1_g]
theorem cell13_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_2_1 hb hν
def cell13_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(984780965073/381237906265:ℝ)]]
theorem cell13_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 2 2) := by
 have heq : (-orderedLow cell13 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_2_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_2_2_g]
def cell13_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(21735871587327963104/31133488624806213:ℝ), (44819420304547263400/31133488624806213:ℝ), (23332616626217750000/31133488624806213:ℝ)]]
theorem cell13_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 2 2 ν := by
 have heq : mixedLowHigh cell13 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_2_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_2_2_g]
def cell13_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(85898456/136107:ℝ), (178309600/136107:ℝ), (93500000/136107:ℝ)]]
theorem cell13_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 2 false ν := by
 have heq : naturalFloor cell13 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_2_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_2_2_g]
def cell13_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(29951225736232/45915288129:ℝ), (62033222931200/45915288129:ℝ), (32449319500000/45915288129:ℝ)]]
theorem cell13_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 2 true ν := by
 have heq : naturalFloor cell13 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_2_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_2_2_g]
def cell13_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(85898456/136107:ℝ), (178309600/136107:ℝ), (93500000/136107:ℝ)]]
theorem cell13_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_2_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_2_2_g]
def cell13_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(8201291500000000/55575346347:ℝ), (16595482794920000/55575346347:ℝ), (8343074950000000/55575346347:ℝ)],
  ![(16595482794920000/55575346347:ℝ), (314649053940607760000/521796926851983:ℝ), (157906866598600000000/521796926851983:ℝ)],
  ![(8343074950000000/55575346347:ℝ), (157906866598600000000/521796926851983:ℝ), (79126467875000000000/521796926851983:ℝ)]]
theorem cell13_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 2 2 b ν := by
 have heq : pairedCleared cell13 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_2_2_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_2_2_g]
theorem cell13_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_2_2 hb hν
def cell13_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(113440047063227167/38123790626500000:ℝ)]]
theorem cell13_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 2 3) := by
 have heq : (-orderedLow cell13 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_2_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_2_3_g]
def cell13_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(2749889844203652628489/3113348862480621300:ℝ), (5736674434075823306639/3113348862480621300:ℝ), (60482895524438762675/62266977249612426:ℝ)]]
theorem cell13_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 2 3 ν := by
 have heq : mixedLowHigh cell13 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_2_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_2_3_g]
def cell13_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(292653052/408321:ℝ), (621003200/408321:ℝ), (333250000/408321:ℝ)]]
theorem cell13_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 3 false ν := by
 have heq : naturalFloor cell13 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_2_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_2_3_g]
def cell13_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(33395362694348/45915288129:ℝ), (70771695986800/45915288129:ℝ), (37927316750000/45915288129:ℝ)]]
theorem cell13_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 3 true ν := by
 have heq : naturalFloor cell13 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_2_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_2_3_g]
def cell13_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(292653052/408321:ℝ), (621003200/408321:ℝ), (333250000/408321:ℝ)]]
theorem cell13_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_2_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_2_3_g]
def cell13_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(10098104225000000/55575346347:ℝ), (20635547417380000/55575346347:ℝ), (10460768675000000/55575346347:ℝ)],
  ![(19816264269920000/55575346347:ℝ), (379882604877409700000/521796926851983:ℝ), (192436900576375000000/521796926851983:ℝ)],
  ![(3222347900000000/18525115449:ℝ), (61736083598375000000/173932308950661:ℝ), (31257825156250000000/173932308950661:ℝ)]]
theorem cell13_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 2 3 b ν := by
 have heq : pairedCleared cell13 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_2_3_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_2_3_g]
theorem cell13_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_2_3 hb hν
def cell13_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(21895089287270333/9530947656625000:ℝ)]]
theorem cell13_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 2 4) := by
 have heq : (-orderedLow cell13 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_2_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_2_4_g]
def cell13_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(717035556795556549/1218055110516675:ℝ), (1606474682155648499/1218055110516675:ℝ), (36357120285134350/48722204420667:ℝ)]]
theorem cell13_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 2 4 ν := by
 have heq : mixedLowHigh cell13 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_2_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_2_4_g]
def cell13_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(327610736/408321:ℝ), (707077600/408321:ℝ), (386000000/408321:ℝ)]]
theorem cell13_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 4 false ν := by
 have heq : naturalFloor cell13 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_2_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_2_4_g]
def cell13_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(327610736/408321:ℝ), (707077600/408321:ℝ), (386000000/408321:ℝ)]]
theorem cell13_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 4 true ν := by
 have heq : naturalFloor cell13 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_2_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_2_4_g]
def cell13_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(327610736/408321:ℝ), (707077600/408321:ℝ), (386000000/408321:ℝ)]]
theorem cell13_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_2_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_2_4_g]
def cell13_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(21117269350000000/166726039041:ℝ), (45303729619520000/166726039041:ℝ), (23879762200000000/166726039041:ℝ)],
  ![(48375530734760000/166726039041:ℝ), (959225301139134920000/1565390780555949:ℝ), (499464246787450000000/1565390780555949:ℝ)],
  ![(27104912350000000/166726039041:ℝ), (531086985599950000000/1565390780555949:ℝ), (273915355437500000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 2 4 b ν := by
 have heq : pairedCleared cell13 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_2_4_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_2_4_g]
theorem cell13_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_2_4 hb hν
def cell13_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(114741920705488499/38123790626500000:ℝ)]]
theorem cell13_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 2 5) := by
 have heq : (-orderedLow cell13 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_2_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_2_5_g]
def cell13_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(2409045568640298857333/3113348862480621300:ℝ), (5360881691210934530083/3113348862480621300:ℝ), (60282061996404961975/62266977249612426:ℝ)]]
theorem cell13_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 2 5 ν := by
 have heq : mixedLowHigh cell13 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_2_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_2_5_g]
def cell13_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(13428460/15123:ℝ), (9792000/5041:ℝ), (16250000/15123:ℝ)]]
theorem cell13_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 5 false ν := by
 have heq : naturalFloor cell13 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_2_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_2_5_g]
def cell13_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(40283636610580/45915288129:ℝ), (88248642098000/45915288129:ℝ), (48883311250000/45915288129:ℝ)]]
theorem cell13_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 5 true ν := by
 have heq : naturalFloor cell13 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_2_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_2_5_g]
def cell13_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(13428460/15123:ℝ), (9792000/5041:ℝ), (16250000/15123:ℝ)]]
theorem cell13_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_2_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_2_5_g]
def cell13_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(26807707525000000/166726039041:ℝ), (57423923486900000/166726039041:ℝ), (30232843375000000/166726039041:ℝ)],
  ![(58037875159760000/166726039041:ℝ), (1154925953949540740000/1565390780555949:ℝ), (603054348720775000000/1565390780555949:ℝ)],
  ![(31076818600000000/166726039041:ℝ), (612991138189525000000/1565390780555949:ℝ), (317856378218750000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 2 5 b ν := by
 have heq : pairedCleared cell13 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_2_5_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_2_5_g]
theorem cell13_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_2_5 hb hν
def cell13_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(70951742130947833/19061895313250000:ℝ)]]
theorem cell13_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 2 6) := by
 have heq : (-orderedLow cell13 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_2_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_2_6_g]
def cell13_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1492674127055577587711/1556674431240310650:ℝ), (3307807047416015748361/1556674431240310650:ℝ), (37049862134204112325/31133488624806213:ℝ)]]
theorem cell13_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 2 6 ν := by
 have heq : mixedLowHigh cell13 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_2_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_2_6_g]
def cell13_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(397526104/408321:ℝ), (879226400/408321:ℝ), (491500000/408321:ℝ)]]
theorem cell13_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 6 false ν := by
 have heq : naturalFloor cell13 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_2_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_2_6_g]
def cell13_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(43727773568696/45915288129:ℝ), (96987115153600/45915288129:ℝ), (54361308500000/45915288129:ℝ)]]
theorem cell13_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 2 6 true ν := by
 have heq : naturalFloor cell13 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_2_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_2_6_g]
def cell13_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(397526104/408321:ℝ), (879226400/408321:ℝ), (491500000/408321:ℝ)]]
theorem cell13_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_2_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_2_6_g]
def cell13_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(32498145700000000/166726039041:ℝ), (69544117354280000/166726039041:ℝ), (36585924550000000/166726039041:ℝ)],
  ![(67700219584760000/166726039041:ℝ), (1350626606759946560000/1565390780555949:ℝ), (706644450654100000000/1565390780555949:ℝ)],
  ![(35048724850000000/166726039041:ℝ), (694895290779100000000/1565390780555949:ℝ), (361797401000000000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 2 6 b ν := by
 have heq : pairedCleared cell13 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_2_6_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_2_6_g]
theorem cell13_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_2_6 hb hν
def cell13_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(156799760019831/19061895313250000:ℝ)]]
theorem cell13_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 3 1) := by
 have heq : (-orderedLow cell13 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_3_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_3_1_g]
def cell13_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(890246995876428284/10377829541602071:ℝ), (403615298636530000/1153092171289119:ℝ), (2783802010018750000/10377829541602071:ℝ)]]
theorem cell13_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 3 1 ν := by
 have heq : mixedLowHigh cell13 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_3_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_3_1_g]
def cell13_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(54577684/408321:ℝ), (180694400/408321:ℝ), (127750000/408321:ℝ)]]
theorem cell13_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 1 false ν := by
 have heq : naturalFloor cell13 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_3_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_3_1_g]
def cell13_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(5650386338116/45915288129:ℝ), (19378397435600/45915288129:ℝ), (13911672250000/45915288129:ℝ)]]
theorem cell13_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 1 true ν := by
 have heq : naturalFloor cell13 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_3_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_3_1_g]
def cell13_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(282692/15123:ℝ), (29999800/136107:ℝ), (28000000/136107:ℝ)]]
theorem cell13_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_3_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_3_1_g]
def cell13_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (30289199260000/782751357:ℝ), (29929225000000/782751357:ℝ)],
  ![(1763066420000/86972373:ℝ), (837238141508560000/7349252490873:ℝ), (681727692850000000/7349252490873:ℝ)],
  ![(1643075000000/86972373:ℝ), (533264130350000000/7349252490873:ℝ), (391272875000000000/7349252490873:ℝ)]]
theorem cell13_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 3 1 b ν := by
 have heq : pairedCleared cell13 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_3_1_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_3_1_g]
theorem cell13_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_3_1 hb hν
def cell13_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(133517670017552833/38123790626500000:ℝ)]]
theorem cell13_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 3 2) := by
 have heq : (-orderedLow cell13 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_3_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_3_2_g]
def cell13_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(25499692207997153104/31133488624806213:ℝ), (51009800854553953400/31133488624806213:ℝ), (25759176555555250000/31133488624806213:ℝ)]]
theorem cell13_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 3 2 ν := by
 have heq : mixedLowHigh cell13 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_3_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_3_2_g]
def cell13_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(299735368/408321:ℝ), (601968800/408321:ℝ), (305500000/408321:ℝ)]]
theorem cell13_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 2 false ν := by
 have heq : naturalFloor cell13 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_3_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_3_2_g]
def cell13_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(34191762046232/45915288129:ℝ), (68631296741200/45915288129:ℝ), (34806857000000/45915288129:ℝ)]]
theorem cell13_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 2 true ν := by
 have heq : naturalFloor cell13 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_3_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_3_2_g]
def cell13_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(299735368/408321:ℝ), (601968800/408321:ℝ), (305500000/408321:ℝ)]]
theorem cell13_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_3_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_3_2_g]
def cell13_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(10098104225000000/55575346347:ℝ), (19816264269920000/55575346347:ℝ), (3222347900000000/18525115449:ℝ)],
  ![(20635547417380000/55575346347:ℝ), (379882604877409700000/521796926851983:ℝ), (61736083598375000000/173932308950661:ℝ)],
  ![(10460768675000000/55575346347:ℝ), (192436900576375000000/521796926851983:ℝ), (31257825156250000000/173932308950661:ℝ)]]
theorem cell13_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 3 2 b ν := by
 have heq : pairedCleared cell13 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_3_2_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_3_2_g]
theorem cell13_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_3_2 hb hν
def cell13_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(3716818707749/762475812530:ℝ)]]
theorem cell13_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 3 3) := by
 have heq : (-orderedLow cell13 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_3_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_3_3_g]
def cell13_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(39762692784836114656/31133488624806213:ℝ), (81059679220302565100/31133488624806213:ℝ), (41670588298964125000/31133488624806213:ℝ)]]
theorem cell13_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 3 3 ν := by
 have heq : mixedLowHigh cell13 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_3_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_3_3_g]
def cell13_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(480433052/408321:ℝ), (983783200/408321:ℝ), (508250000/408321:ℝ)]]
theorem cell13_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 3 false ν := by
 have heq : naturalFloor cell13 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_3_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_3_3_g]
def cell13_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(18494891738116/15305096043:ℝ), (37815652835600/15305096043:ℝ), (19504422250000/15305096043:ℝ)]]
theorem cell13_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 3 true ν := by
 have heq : naturalFloor cell13 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_3_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_3_3_g]
def cell13_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(480433052/408321:ℝ), (983783200/408321:ℝ), (508250000/408321:ℝ)]]
theorem cell13_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_3_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_3_3_g]
def cell13_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(45721143850000000/166726039041:ℝ), (91710379677140000/166726039041:ℝ), (45759212275000000/166726039041:ℝ)],
  ![(91710379677140000/166726039041:ℝ), (1724840738819634920000/1565390780555949:ℝ), (859599586818700000000/1565390780555949:ℝ)],
  ![(45759212275000000/166726039041:ℝ), (859599586818700000000/1565390780555949:ℝ), (427953636687500000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 3 3 b ν := by
 have heq : pairedCleared cell13 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_3_3_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_3_3_g]
theorem cell13_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_3_3 hb hν
def cell13_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(200802885943377167/38123790626500000:ℝ)]]
theorem cell13_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 3 4) := by
 have heq : (-orderedLow cell13 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_3_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_3_4_g]
def cell13_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(1517523987984822594563/1037782954160207100:ℝ), (3120233441883784492213/1037782954160207100:ℝ), (32386279623310504225/20755659083204142:ℝ)]]
theorem cell13_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 3 4 ν := by
 have heq : mixedLowHigh cell13 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_3_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_3_4_g]
def cell13_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(171796912/136107:ℝ), (356619200/136107:ℝ), (187000000/136107:ℝ)]]
theorem cell13_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 4 false ν := by
 have heq : naturalFloor cell13 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_3_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_3_4_g]
def cell13_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(58928812172464/45915288129:ℝ), (122185431562400/45915288129:ℝ), (63991264000000/45915288129:ℝ)]]
theorem cell13_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 4 true ν := by
 have heq : naturalFloor cell13 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_3_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_3_4_g]
def cell13_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(171796912/136107:ℝ), (356619200/136107:ℝ), (187000000/136107:ℝ)]]
theorem cell13_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_3_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_3_4_g]
def cell13_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(51411582025000000/166726039041:ℝ), (103830573544520000/166726039041:ℝ), (52112293450000000/166726039041:ℝ)],
  ![(101372724102140000/166726039041:ℝ), (1920541391630040740000/1565390780555949:ℝ), (963189688752025000000/1565390780555949:ℝ)],
  ![(49731118525000000/166726039041:ℝ), (941503739408275000000/1565390780555949:ℝ), (471894659468750000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 3 4 b ν := by
 have heq : pairedCleared cell13 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_3_4_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_3_4_g]
theorem cell13_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_3_4 hb hν
def cell13_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(43735799007307833/9530947656625000:ℝ)]]
theorem cell13_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 3 5) := by
 have heq : (-orderedLow cell13 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_3_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_3_5_g]
def cell13_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(908856250730064423611/778337215620155325:ℝ), (1932543794791341933361/778337215620155325:ℝ), (41570171534947224650/31133488624806213:ℝ)]]
theorem cell13_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 3 5 ν := by
 have heq : mixedLowHigh cell13 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_3_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_3_5_g]
def cell13_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(550348420/408321:ℝ), (1155932000/408321:ℝ), (613750000/408321:ℝ)]]
theorem cell13_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 5 false ν := by
 have heq : naturalFloor cell13 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_3_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_3_5_g]
def cell13_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(62372949130580/45915288129:ℝ), (130923904618000/45915288129:ℝ), (69469261250000/45915288129:ℝ)]]
theorem cell13_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 5 true ν := by
 have heq : naturalFloor cell13 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_3_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_3_5_g]
def cell13_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(550348420/408321:ℝ), (1155932000/408321:ℝ), (613750000/408321:ℝ)]]
theorem cell13_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_3_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_3_5_g]
def cell13_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(42234538700000000/166726039041:ℝ), (87227660911900000/166726039041:ℝ), (44609749625000000/166726039041:ℝ)],
  ![(90299462027140000/166726039041:ℝ), (1740118878136946560000/1565390780555949:ℝ), (885343233810350000000/1565390780555949:ℝ)],
  ![(47834899775000000/166726039041:ℝ), (916965972622850000000/1565390780555949:ℝ), (464489588500000000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 3 5 b ν := by
 have heq : pairedCleared cell13 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_3_5_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_3_5_g]
theorem cell13_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_3_5 hb hν
def cell13_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(202104759585638499/38123790626500000:ℝ)]]
theorem cell13_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 3 6) := by
 have heq : (-orderedLow cell13 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_3_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_3_6_g]
def cell13_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(4211727688391114012533/3113348862480621300:ℝ), (8984907582786464700083/3113348862480621300:ℝ), (96958005341897711975/62266977249612426:ℝ)]]
theorem cell13_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 3 6 ν := by
 have heq : mixedLowHigh cell13 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_3_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_3_6_g]
def cell13_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(585306104/408321:ℝ), (1242006400/408321:ℝ), (666500000/408321:ℝ)]]
theorem cell13_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 6 false ν := by
 have heq : naturalFloor cell13 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_3_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_3_6_g]
def cell13_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(585306104/408321:ℝ), (1242006400/408321:ℝ), (666500000/408321:ℝ)]]
theorem cell13_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 3 6 true ν := by
 have heq : naturalFloor cell13 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_3_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_3_6_g]
def cell13_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(585306104/408321:ℝ), (1242006400/408321:ℝ), (666500000/408321:ℝ)]]
theorem cell13_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_3_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_3_6_g]
def cell13_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(47924976875000000/166726039041:ℝ), (99347854779280000/166726039041:ℝ), (50962830800000000/166726039041:ℝ)],
  ![(99961806452140000/166726039041:ℝ), (1935819530947352380000/1565390780555949:ℝ), (988933335743675000000/1565390780555949:ℝ)],
  ![(51806806025000000/166726039041:ℝ), (998870125212425000000/1565390780555949:ℝ), (508430611281250000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 3 6 b ν := by
 have heq : pairedCleared cell13 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_3_6_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_3_6_g]
theorem cell13_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_3_6 hb hν
def cell13_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(12102974968756499/7624758125300000:ℝ)]]
theorem cell13_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 4 1) := by
 have heq : (-orderedLow cell13 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_4_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_4_1_g]
def cell13_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(3314138485394039384/10377829541602071:ℝ), (7954987502433006100/10377829541602071:ℝ), (4682360335205375000/10377829541602071:ℝ)]]
theorem cell13_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 4 1 ν := by
 have heq : mixedLowHigh cell13 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_4_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_4_1_g]
def cell13_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(190507684/408321:ℝ), (429124400/408321:ℝ), (240250000/408321:ℝ)]]
theorem cell13_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 1 false ν := by
 have heq : naturalFloor cell13 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_4_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_4_1_g]
def cell13_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(20448759258116/45915288129:ℝ), (46373595355600/45915288129:ℝ), (26108497250000/45915288129:ℝ)]]
theorem cell13_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 1 true ν := by
 have heq : naturalFloor cell13 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_4_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_4_1_g]
def cell13_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(96617684/408321:ℝ), (247734400/408321:ℝ), (152750000/408321:ℝ)]]
theorem cell13_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_4_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_4_1_g]
def cell13_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(1896812725000000/55575346347:ℝ), (5371314622460000/55575346347:ℝ), (3448943725000000/55575346347:ℝ)],
  ![(5166664064840000/55575346347:ℝ), (124677458983909700000/521796926851983:ℝ), (75704050388875000000/521796926851983:ℝ)],
  ![(3167618650000000/55575346347:ℝ), (72391787232625000000/521796926851983:ℝ), (42427381718750000000/521796926851983:ℝ)]]
theorem cell13_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 4 1 b ν := by
 have heq : pairedCleared cell13 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_4_1_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_4_1_g]
theorem cell13_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_4_1 hb hν
def cell13_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(43838219200094831/19061895313250000:ℝ)]]
theorem cell13_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 4 2) := by
 have heq : (-orderedLow cell13 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_4_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_4_2_g]
def cell13_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(20697562185137436404/31133488624806213:ℝ), (47137871978941611700/31133488624806213:ℝ), (26689377702802625000/31133488624806213:ℝ)]]
theorem cell13_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 4 2 ν := by
 have heq : mixedLowHigh cell13 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_4_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_4_2_g]
def cell13_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(92438456/136107:ℝ), (209849600/136107:ℝ), (39500000/45369:ℝ)]]
theorem cell13_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 2 false ν := by
 have heq : naturalFloor cell13 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_4_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_4_2_g]
def cell13_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(92438456/136107:ℝ), (209849600/136107:ℝ), (39500000/45369:ℝ)]]
theorem cell13_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 2 true ν := by
 have heq : naturalFloor cell13 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_4_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_4_2_g]
def cell13_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(785001104/1224963:ℝ), (1797951400/1224963:ℝ), (1022750000/1224963:ℝ)]]
theorem cell13_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_4_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_4_2_g]
def cell13_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(21117269350000000/166726039041:ℝ), (48375530734760000/166726039041:ℝ), (27104912350000000/166726039041:ℝ)],
  ![(45303729619520000/166726039041:ℝ), (959225301139134920000/1565390780555949:ℝ), (531086985599950000000/1565390780555949:ℝ)],
  ![(23879762200000000/166726039041:ℝ), (499464246787450000000/1565390780555949:ℝ), (273915355437500000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 4 2 b ν := by
 have heq : pairedCleared cell13 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_4_2_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_4_2_g]
theorem cell13_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_4_2 hb hν
def cell13_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(220880508897702833/38123790626500000:ℝ)]]
theorem cell13_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 4 3) := by
 have heq : (-orderedLow cell13 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_4_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_4_3_g]
def cell13_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(4836279267278367184/3459276513867357:ℝ), (29083353256769751700/10377829541602071:ℝ), (14699049409433875000/10377829541602071:ℝ)]]
theorem cell13_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 4 3 ν := by
 have heq : mixedLowHigh cell13 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_4_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_4_3_g]
def cell13_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(174157684/136107:ℝ), (350274400/136107:ℝ), (19750000/15123:ℝ)]]
theorem cell13_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 3 false ν := by
 have heq : naturalFloor cell13 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_4_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_4_3_g]
def cell13_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(59725211524348/45915288129:ℝ), (120045032316800/45915288129:ℝ), (60870804250000/45915288129:ℝ)]]
theorem cell13_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 3 true ν := by
 have heq : naturalFloor cell13 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_4_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_4_3_g]
def cell13_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(174157684/136107:ℝ), (350274400/136107:ℝ), (19750000/15123:ℝ)]]
theorem cell13_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_4_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_4_3_g]
def cell13_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(51411582025000000/166726039041:ℝ), (101372724102140000/166726039041:ℝ), (49731118525000000/166726039041:ℝ)],
  ![(103830573544520000/166726039041:ℝ), (1920541391630040740000/1565390780555949:ℝ), (941503739408275000000/1565390780555949:ℝ)],
  ![(52112293450000000/166726039041:ℝ), (963189688752025000000/1565390780555949:ℝ), (471894659468750000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 4 3 b ν := by
 have heq : pairedCleared cell13 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_4_3_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_4_3_g]
theorem cell13_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_4_3 hb hν
def cell13_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(2732037742676/381237906265:ℝ)]]
theorem cell13_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 4 4) := by
 have heq : (-orderedLow cell13 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_4_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_4_4_g]
def cell13_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(713450789905484768/384364057096373:ℝ), (4344442153187328400/1153092171289119:ℝ), (2222539258211500000/1153092171289119:ℝ)]]
theorem cell13_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 4 4 ν := by
 have heq : mixedLowHigh cell13 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_4_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_4_4_g]
def cell13_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(703170736/408321:ℝ), (1432637600/408321:ℝ), (736000000/408321:ℝ)]]
theorem cell13_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 4 false ν := by
 have heq : naturalFloor cell13 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_4_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_4_4_g]
def cell13_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(81018124692464/45915288129:ℝ), (164860694082400/45915288129:ℝ), (84577214000000/45915288129:ℝ)]]
theorem cell13_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 4 true ν := by
 have heq : naturalFloor cell13 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_4_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_4_4_g]
def cell13_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(703170736/408321:ℝ), (1432637600/408321:ℝ), (736000000/408321:ℝ)]]
theorem cell13_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_4_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_4_4_g]
def cell13_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(66838413200000000/166726039041:ℝ), (133634310969520000/166726039041:ℝ), (66489199700000000/166726039041:ℝ)],
  ![(133634310969520000/166726039041:ℝ), (2505734315817446560000/1565390780555949:ℝ), (1245478573841600000000/1565390780555949:ℝ)],
  ![(66489199700000000/166726039041:ℝ), (1245478573841600000000/1565390780555949:ℝ), (618527869750000000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 4 4 b ν := by
 have heq : pairedCleared cell13 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_4_4_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_4_4_g]
theorem cell13_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_4_4 hb hν
def cell13_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(288165724823527167/38123790626500000:ℝ)]]
theorem cell13_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 4 5) := by
 have heq : (-orderedLow cell13 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_4_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_4_5_g]
def cell13_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(6355254083705282938889/3113348862480621300:ℝ), (12984726217226883646639/3113348862480621300:ℝ), (133834782215424262675/62266977249612426:ℝ)]]
theorem cell13_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 4 5 ν := by
 have heq : mixedLowHigh cell13 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_4_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_4_5_g]
def cell13_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(738128420/408321:ℝ), (1518712000/408321:ℝ), (788750000/408321:ℝ)]]
theorem cell13_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 5 false ν := by
 have heq : naturalFloor cell13 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_4_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_4_5_g]
def cell13_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(28154087216860/15305096043:ℝ), (57866389046000/15305096043:ℝ), (30018403750000/15305096043:ℝ)]]
theorem cell13_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 5 true ν := by
 have heq : naturalFloor cell13 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_4_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_4_5_g]
def cell13_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(738128420/408321:ℝ), (1518712000/408321:ℝ), (788750000/408321:ℝ)]]
theorem cell13_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_4_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_4_5_g]
def cell13_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(72528851375000000/166726039041:ℝ), (145754504836900000/166726039041:ℝ), (72842280875000000/166726039041:ℝ)],
  ![(143296655394520000/166726039041:ℝ), (2701434968627852380000/1565390780555949:ℝ), (1349068675774925000000/1565390780555949:ℝ)],
  ![(70461105950000000/166726039041:ℝ), (1327382726431175000000/1565390780555949:ℝ), (662468892531250000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 4 5 b ν := by
 have heq : pairedCleared cell13 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_4_5_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_4_5_g]
theorem cell13_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_4_5 hb hν
def cell13_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(65576508727345333/9530947656625000:ℝ)]]
theorem cell13_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 4 6) := by
 have heq : (-orderedLow cell13 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_4_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_4_6_g]
def cell13_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(1359526780667768212411/778337215620155325:ℝ), (2838550267685224475861/778337215620155325:ℝ), (59908143207693599650/31133488624806213:ℝ)]]
theorem cell13_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 4 6 ν := by
 have heq : mixedLowHigh cell13 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_4_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_4_6_g]
def cell13_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(85898456/45369:ℝ), (178309600/45369:ℝ), (93500000/45369:ℝ)]]
theorem cell13_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 6 false ν := by
 have heq : naturalFloor cell13 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_4_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_4_6_g]
def cell13_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(87906398608696/45915288129:ℝ), (182337640193600/45915288129:ℝ), (95533208500000/45915288129:ℝ)]]
theorem cell13_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 4 6 true ν := by
 have heq : naturalFloor cell13 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_4_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_4_6_g]
def cell13_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(85898456/45369:ℝ), (178309600/45369:ℝ), (93500000/45369:ℝ)]]
theorem cell13_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_4_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_4_6_g]
def cell13_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(21117269350000000/55575346347:ℝ), (43050530734760000/55575346347:ℝ), (21779912350000000/55575346347:ℝ)],
  ![(44074464439840000/55575346347:ℝ), (840337485044919400000/521796926851983:ℝ), (423740740277750000000/521796926851983:ℝ)],
  ![(7618320800000000/18525115449:ℝ), (144760551071750000000/173932308950661:ℝ), (72784869062500000000/173932308950661:ℝ)]]
theorem cell13_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 4 6 b ν := by
 have heq : pairedCleared cell13 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_4_6_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_4_6_g]
theorem cell13_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_4_6 hb hν
def cell13_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(7544759385470333/2382736914156250:ℝ)]]
theorem cell13_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 5 1) := by
 have heq : (-orderedLow cell13 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_5_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_5_1_g]
def cell13_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(5738029974911650484/10377829541602071:ℝ), (12277437317137242200/10377829541602071:ℝ), (731213184488000000/1153092171289119:ℝ)]]
theorem cell13_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 5 1 ν := by
 have heq : mixedLowHigh cell13 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_5_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_5_1_g]
def cell13_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(326437684/408321:ℝ), (677554400/408321:ℝ), (352750000/408321:ℝ)]]
theorem cell13_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 1 false ν := by
 have heq : naturalFloor cell13 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_5_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_5_1_g]
def cell13_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(11749044059372/15305096043:ℝ), (24456264425200/15305096043:ℝ), (12768440750000/15305096043:ℝ)]]
theorem cell13_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 1 true ν := by
 have heq : naturalFloor cell13 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_5_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_5_1_g]
def cell13_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(185602684/408321:ℝ), (405469400/408321:ℝ), (221500000/408321:ℝ)]]
theorem cell13_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_5_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_5_1_g]
def cell13_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(3793625450000000/55575346347:ℝ), (8592096097460000/55575346347:ℝ), (1590970825000000/18525115449:ℝ)],
  ![(9206728687300000/55575346347:ℝ), (189911009920711640000/521796926851983:ℝ), (34335144861800000000/173932308950661:ℝ)],
  ![(5285312375000000/55575346347:ℝ), (106921821210400000000/521796926851983:ℝ), (6341598812500000000/57977436316887:ℝ)]]
theorem cell13_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 5 1 b ν := by
 have heq : pairedCleared cell13 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_5_1_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_5_1_g]
theorem cell13_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_5_1 hb hν
def cell13_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(29575542744786499/7624758125300000:ℝ)]]
theorem cell13_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 5 2) := by
 have heq : (-orderedLow cell13 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_5_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_5_2_g]
def cell13_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(27969236653690269704/31133488624806213:ℝ), (60105221423054320000/31133488624806213:ℝ), (32385052678362500000/31133488624806213:ℝ)]]
theorem cell13_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 5 2 ν := by
 have heq : mixedLowHigh cell13 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_5_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_5_2_g]
def cell13_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(15305384/15123:ℝ), (97553200/45369:ℝ), (52000000/45369:ℝ)]]
theorem cell13_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 2 false ν := by
 have heq : naturalFloor cell13 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_5_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_5_2_g]
def cell13_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(45982208736232/45915288129:ℝ), (97787330931200/45915288129:ℝ), (52172444500000/45915288129:ℝ)]]
theorem cell13_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 2 true ν := by
 have heq : naturalFloor cell13 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_5_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_5_2_g]
def cell13_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(1051956104/1224963:ℝ), (2271156400/1224963:ℝ), (1229000000/1224963:ℝ)]]
theorem cell13_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_5_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_5_2_g]
def cell13_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(26807707525000000/166726039041:ℝ), (58037875159760000/166726039041:ℝ), (31076818600000000/166726039041:ℝ)],
  ![(57423923486900000/166726039041:ℝ), (1154925953949540740000/1565390780555949:ℝ), (612991138189525000000/1565390780555949:ℝ)],
  ![(30232843375000000/166726039041:ℝ), (603054348720775000000/1565390780555949:ℝ), (317856378218750000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 5 2 b ν := by
 have heq : pairedCleared cell13 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_5_2_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_5_2_g]
theorem cell13_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_5_2 hb hν
def cell13_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(87519638640169831/19061895313250000:ℝ)]]
theorem cell13_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 5 3) := by
 have heq : (-orderedLow cell13 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_5_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_5_3_g]
def cell13_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(38724383382645587956/31133488624806213:ℝ), (83378130894696913400/31133488624806213:ℝ), (45027349375549000000/31133488624806213:ℝ)]]
theorem cell13_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 5 3 ν := by
 have heq : mixedLowHigh cell13 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_5_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_5_3_g]
def cell13_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(500053052/408321:ℝ), (1078403200/408321:ℝ), (583250000/408321:ℝ)]]
theorem cell13_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 3 false ν := by
 have heq : naturalFloor cell13 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_5_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_5_3_g]
def cell13_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(56717285294348/45915288129:ℝ), (122205868586800/45915288129:ℝ), (66039566750000/45915288129:ℝ)]]
theorem cell13_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 3 true ν := by
 have heq : naturalFloor cell13 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_5_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_5_3_g]
def cell13_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(500053052/408321:ℝ), (1078403200/408321:ℝ), (583250000/408321:ℝ)]]
theorem cell13_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_5_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_5_3_g]
def cell13_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(42234538700000000/166726039041:ℝ), (90299462027140000/166726039041:ℝ), (47834899775000000/166726039041:ℝ)],
  ![(87227660911900000/166726039041:ℝ), (1740118878136946560000/1565390780555949:ℝ), (916965972622850000000/1565390780555949:ℝ)],
  ![(44609749625000000/166726039041:ℝ), (885343233810350000000/1565390780555949:ℝ), (464489588500000000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 5 3 b ν := by
 have heq : pairedCleared cell13 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_5_3_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_5_3_g]
theorem cell13_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_5_3 hb hν
def cell13_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(308243347777852833/38123790626500000:ℝ)]]
theorem cell13_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 5 4) := by
 have heq : (-orderedLow cell13 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_5_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_5_4_g]
def cell13_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(61553334603013456208/31133488624806213:ℝ), (123490318686064556800/31133488624806213:ℝ), (62435119901048000000/31133488624806213:ℝ)]]
theorem cell13_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 5 4 ν := by
 have heq : mixedLowHigh cell13 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_5_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_5_4_g]
def cell13_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(745210736/408321:ℝ), (1499677600/408321:ℝ), (761000000/408321:ℝ)]]
theorem cell13_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 4 false ν := by
 have heq : naturalFloor cell13 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_5_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_5_4_g]
def cell13_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(28419553667488/15305096043:ℝ), (57152922630800/15305096043:ℝ), (28978250500000/15305096043:ℝ)]]
theorem cell13_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 4 true ν := by
 have heq : naturalFloor cell13 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_5_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_5_4_g]
def cell13_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(745210736/408321:ℝ), (1499677600/408321:ℝ), (761000000/408321:ℝ)]]
theorem cell13_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_5_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_5_4_g]
def cell13_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(72528851375000000/166726039041:ℝ), (143296655394520000/166726039041:ℝ), (70461105950000000/166726039041:ℝ)],
  ![(145754504836900000/166726039041:ℝ), (2701434968627852380000/1565390780555949:ℝ), (1327382726431175000000/1565390780555949:ℝ)],
  ![(72842280875000000/166726039041:ℝ), (1349068675774925000000/1565390780555949:ℝ), (662468892531250000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 5 4 b ν := by
 have heq : pairedCleared cell13 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_5_4_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_5_4_g]
theorem cell13_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_5_4 hb hν
def cell13_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(1442266452591/152495162506:ℝ)]]
theorem cell13_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 5 5) := by
 have heq : (-orderedLow cell13 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_5_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_5_5_g]
def cell13_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(75816335179852417760/31133488624806213:ℝ), (153540197051813168500/31133488624806213:ℝ), (78346531644456875000/31133488624806213:ℝ)]]
theorem cell13_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 5 5 ν := by
 have heq : mixedLowHigh cell13 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_5_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_5_5_g]
def cell13_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(308636140/136107:ℝ), (627164000/136107:ℝ), (321250000/136107:ℝ)]]
theorem cell13_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 5 false ν := by
 have heq : naturalFloor cell13 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_5_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_5_5_g]
def cell13_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(106551574170580/45915288129:ℝ), (216274429658000/45915288129:ℝ), (110641161250000/45915288129:ℝ)]]
theorem cell13_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 5 true ν := by
 have heq : naturalFloor cell13 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_5_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_5_5_g]
def cell13_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(308636140/136107:ℝ), (627164000/136107:ℝ), (321250000/136107:ℝ)]]
theorem cell13_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_5_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_5_5_g]
def cell13_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(29318560850000000/55575346347:ℝ), (58519414087300000/55575346347:ℝ), (29073062375000000/55575346347:ℝ)],
  ![(58519414087300000/55575346347:ℝ), (1095542630938419400000/521796926851983:ℝ), (543785853621500000000/521796926851983:ℝ)],
  ![(29073062375000000/55575346347:ℝ), (543785853621500000000/521796926851983:ℝ), (269700700937500000000/521796926851983:ℝ)]]
theorem cell13_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 5 5 b ν := by
 have heq : pairedCleared cell13 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_5_5_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_5_5_g]
theorem cell13_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_5_5 hb hν
def cell13_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(375528563703677167/38123790626500000:ℝ)]]
theorem cell13_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 5 6) := by
 have heq : (-orderedLow cell13 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_5_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_5_6_g]
def cell13_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(8157936203456098094089/3113348862480621300:ℝ), (16608752108802413816639/3113348862480621300:ℝ), (170510725560917012675/62266977249612426:ℝ)]]
theorem cell13_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 5 6 ν := by
 have heq : mixedLowHigh cell13 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_5_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_5_6_g]
def cell13_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(960866104/408321:ℝ), (1967566400/408321:ℝ), (1016500000/408321:ℝ)]]
theorem cell13_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 6 false ν := by
 have heq : naturalFloor cell13 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_5_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_5_6_g]
def cell13_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(109995711128696/45915288129:ℝ), (225012902713600/45915288129:ℝ), (116119158500000/45915288129:ℝ)]]
theorem cell13_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 5 6 true ν := by
 have heq : naturalFloor cell13 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_5_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_5_6_g]
def cell13_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(960866104/408321:ℝ), (1967566400/408321:ℝ), (1016500000/408321:ℝ)]]
theorem cell13_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_5_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_5_6_g]
def cell13_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(10405124525000000/18525115449:ℝ), (20853159569920000/18525115449:ℝ), (10396918700000000/18525115449:ℝ)],
  ![(61740195562300000/55575346347:ℝ), (1160776181875221340000/521796926851983:ℝ), (578315887599275000000/521796926851983:ℝ)],
  ![(30397031125000000/55575346347:ℝ), (571087237818025000000/521796926851983:ℝ), (284347708531250000000/521796926851983:ℝ)]]
theorem cell13_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 5 6 b ν := by
 have heq : pairedCleared cell13 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_5_6_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_5_6_g]
theorem cell13_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_5_6 hb hν
def cell13_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(233938678961821163/38123790626500000:ℝ)]]
theorem cell13_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 6 1) := by
 have heq : (-orderedLow cell13 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_6_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_6_1_g]
def cell13_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(219001449212991382363/172963825693367850:ℝ), (1310870614943254366639/518891477080103550:ℝ), (13118836664252012675/10377829541602071:ℝ)]]
theorem cell13_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 6 1 ν := by
 have heq : mixedLowHigh cell13 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_6_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_6_1_g]
def cell13_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(462367684/408321:ℝ), (925984400/408321:ℝ), (465250000/408321:ℝ)]]
theorem cell13_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 1 false ν := by
 have heq : naturalFloor cell13 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_6_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_6_1_g]
def cell13_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(50045505098116/45915288129:ℝ), (100363991195600/45915288129:ℝ), (50502147250000/45915288129:ℝ)]]
theorem cell13_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 1 true ν := by
 have heq : naturalFloor cell13 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_6_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_6_1_g]
def cell13_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(91529228/136107:ℝ), (187734800/136107:ℝ), (10750000/15123:ℝ)]]
theorem cell13_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_6_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_6_1_g]
def cell13_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(31938796025000000/166726039041:ℝ), (64161739217380000/166726039041:ℝ), (32146268675000000/166726039041:ℝ)],
  ![(60475986429280000/166726039041:ℝ), (1141556848876040740000/1565390780555949:ℝ), (572357013220775000000/1565390780555949:ℝ)],
  ![(28077143300000000/166726039041:ℝ), (530797484939525000000/1565390780555949:ℝ), (266510284468750000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 6 1 b ν := by
 have heq : pairedCleared cell13 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_6_1_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_6_1_g]
theorem cell13_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_6_1 hb hν
def cell13_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(6502468407739854/1191368457078125:ℝ)]]
theorem cell13_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 6 2) := by
 have heq : (-orderedLow cell13 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_6_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_6_2_g]
def cell13_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(35240911122243103004/31133488624806213:ℝ), (73072570867167028300/31133488624806213:ℝ), (38080727653922375000/31133488624806213:ℝ)]]
theorem cell13_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 6 2 ν := by
 have heq : mixedLowHigh cell13 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_6_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_6_2_g]
def cell13_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(183058456/136107:ℝ), (375469600/136107:ℝ), (21500000/15123:ℝ)]]
theorem cell13_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 2 false ν := by
 have heq : naturalFloor cell13 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_6_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_6_2_g]
def cell13_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(60780581656232/45915288129:ℝ), (124782528851200/45915288129:ℝ), (64369269500000/45915288129:ℝ)]]
theorem cell13_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 2 true ν := by
 have heq : naturalFloor cell13 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_6_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_6_2_g]
def cell13_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(1318911104/1224963:ℝ), (2744361400/1224963:ℝ), (1435250000/1224963:ℝ)]]
theorem cell13_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_6_2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_6_2_g]
def cell13_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(32498145700000000/166726039041:ℝ), (67700219584760000/166726039041:ℝ), (35048724850000000/166726039041:ℝ)],
  ![(69544117354280000/166726039041:ℝ), (1350626606759946560000/1565390780555949:ℝ), (694895290779100000000/1565390780555949:ℝ)],
  ![(36585924550000000/166726039041:ℝ), (706644450654100000000/1565390780555949:ℝ), (361797401000000000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 6 2 b ν := by
 have heq : pairedCleared cell13 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_6_2_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_6_2_g]
theorem cell13_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_6_2 hb hν
def cell13_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(47048110520816499/7624758125300000:ℝ)]]
theorem cell13_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 6 3) := by
 have heq : (-orderedLow cell13 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_6_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_6_3_g]
def cell13_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(45996057851198421256/31133488624806213:ℝ), (96345480338809621700/31133488624806213:ℝ), (50723024351108875000/31133488624806213:ℝ)]]
theorem cell13_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 6 3 ν := by
 have heq : mixedLowHigh cell13 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_6_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_6_3_g]
def cell13_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(635983052/408321:ℝ), (1326833200/408321:ℝ), (695750000/408321:ℝ)]]
theorem cell13_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 3 false ν := by
 have heq : naturalFloor cell13 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_6_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_6_3_g]
def cell13_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(635983052/408321:ℝ), (1326833200/408321:ℝ), (695750000/408321:ℝ)]]
theorem cell13_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 3 true ν := by
 have heq : naturalFloor cell13 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_6_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_6_3_g]
def cell13_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(1814059156/1224963:ℝ), (3799109600/1224963:ℝ), (1999750000/1224963:ℝ)]]
theorem cell13_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_6_3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_6_3_g]
def cell13_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(47924976875000000/166726039041:ℝ), (99961806452140000/166726039041:ℝ), (51806806025000000/166726039041:ℝ)],
  ![(99347854779280000/166726039041:ℝ), (1935819530947352380000/1565390780555949:ℝ), (998870125212425000000/1565390780555949:ℝ)],
  ![(50962830800000000/166726039041:ℝ), (988933335743675000000/1565390780555949:ℝ), (508430611281250000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 6 3 b ν := by
 have heq : pairedCleared cell13 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_6_3_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_6_3_g]
theorem cell13_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_6_3 hb hν
def cell13_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(131201058080244831/19061895313250000:ℝ)]]
theorem cell13_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 6 4) := by
 have heq : (-orderedLow cell13 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_6_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_6_4_g]
def cell13_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(18917068193384579836/10377829541602071:ℝ), (39872796603484071700/10377829541602071:ℝ), (7040591227588375000/3459276513867357:ℝ)]]
theorem cell13_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 6 4 ν := by
 have heq : mixedLowHigh cell13 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_6_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_6_4_g]
def cell13_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(722790736/408321:ℝ), (1527257600/408321:ℝ), (811000000/408321:ℝ)]]
theorem cell13_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 4 false ν := by
 have heq : naturalFloor cell13 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_6_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_6_4_g]
def cell13_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(82250734772464/45915288129:ℝ), (173619604162400/45915288129:ℝ), (92103514000000/45915288129:ℝ)]]
theorem cell13_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 4 true ν := by
 have heq : naturalFloor cell13 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_6_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_6_4_g]
def cell13_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(722790736/408321:ℝ), (1527257600/408321:ℝ), (811000000/408321:ℝ)]]
theorem cell13_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_6_4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_6_4_g]
def cell13_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(21117269350000000/55575346347:ℝ), (44074464439840000/55575346347:ℝ), (7618320800000000/18525115449:ℝ)],
  ![(43050530734760000/55575346347:ℝ), (840337485044919400000/521796926851983:ℝ), (144760551071750000000/173932308950661:ℝ)],
  ![(21779912350000000/55575346347:ℝ), (423740740277750000000/521796926851983:ℝ), (72784869062500000000/173932308950661:ℝ)]]
theorem cell13_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 6 4 b ν := by
 have heq : pairedCleared cell13 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_6_4_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_6_4_g]
theorem cell13_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_6_4 hb hν
def cell13_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(395606186658002833/38123790626500000:ℝ)]]
theorem cell13_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 6 5) := by
 have heq : (-orderedLow cell13 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_6_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_6_5_g]
def cell13_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(79580155800521607760/31133488624806213:ℝ), (159730577601819858500/31133488624806213:ℝ), (80773091573794375000/31133488624806213:ℝ)]]
theorem cell13_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 6 5 ν := by
 have heq : mixedLowHigh cell13 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_6_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_6_5_g]
def cell13_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(967948420/408321:ℝ), (1948532000/408321:ℝ), (988750000/408321:ℝ)]]
theorem cell13_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 5 false ν := by
 have heq : naturalFloor cell13 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_6_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_6_5_g]
def cell13_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(110792110480580/45915288129:ℝ), (222872503468000/45915288129:ℝ), (112998698750000/45915288129:ℝ)]]
theorem cell13_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 5 true ν := by
 have heq : naturalFloor cell13 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_6_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_6_5_g]
def cell13_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(967948420/408321:ℝ), (1948532000/408321:ℝ), (988750000/408321:ℝ)]]
theorem cell13_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_6_5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_6_5_g]
def cell13_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(10405124525000000/18525115449:ℝ), (61740195562300000/55575346347:ℝ), (30397031125000000/55575346347:ℝ)],
  ![(20853159569920000/18525115449:ℝ), (1160776181875221340000/521796926851983:ℝ), (571087237818025000000/521796926851983:ℝ)],
  ![(10396918700000000/18525115449:ℝ), (578315887599275000000/521796926851983:ℝ), (284347708531250000000/521796926851983:ℝ)]]
theorem cell13_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 6 5 b ν := by
 have heq : pairedCleared cell13 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_6_5_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_6_5_g]
theorem cell13_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_6_5 hb hν
def cell13_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(4479294520279/381237906265:ℝ)]]
theorem cell13_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell13 6 6) := by
 have heq : (-orderedLow cell13 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell13_ordered_6_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordered_6_6_g]
def cell13_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(93843156377360569312/31133488624806213:ℝ), (189780455967568470200/31133488624806213:ℝ), (96684503317203250000/31133488624806213:ℝ)]]
theorem cell13_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell13 6 6 ν := by
 have heq : mixedLowHigh cell13 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_mixed_6_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_mixed_6_6_g]
def cell13_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(1148646104/408321:ℝ), (2330346400/408321:ℝ), (1191500000/408321:ℝ)]]
theorem cell13_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 6 false ν := by
 have heq : naturalFloor cell13 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor0_6_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor0_6_6_g]
def cell13_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(14676113738744/5101698681:ℝ), (29743129470400/5101698681:ℝ), (15189456500000/5101698681:ℝ)]]
theorem cell13_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell13 6 6 true ν := by
 have heq : naturalFloor cell13 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_floor1_6_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_floor1_6_6_g]
def cell13_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(1148646104/408321:ℝ), (2330346400/408321:ℝ), (1191500000/408321:ℝ)]]
theorem cell13_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell13_complement_floor_6_6_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement_floor_6_6_g]
def cell13_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(109072951900000000/166726039041:ℝ), (217482173554280000/166726039041:ℝ), (107949174550000000/166726039041:ℝ)],
  ![(217482173554280000/166726039041:ℝ), (4067521469813069840000/1565390780555949:ℝ), (2017236547887400000000/1565390780555949:ℝ)],
  ![(107949174550000000/166726039041:ℝ), (2017236547887400000000/1565390780555949:ℝ), (999676335875000000000/1565390780555949:ℝ)]]
theorem cell13_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell13 6 6 b ν := by
 have heq : pairedCleared cell13 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) cell13_paired_cleared_6_6_g (3111/5000:ℝ) (3/4:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_cleared_6_6_g]
theorem cell13_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) : 0 ≤ pairedGap cell13 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact cell13_paired_cleared_6_6 hb hν
def cell13_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(24602025804907833/38123790626500000:ℝ)]]
theorem cell13_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell13.q/K)+1+17/50*(cell13.q/cell13.priorL)+17/25*(cell13.q/cell13.priorL)*cell13.priorB) := by
 have heq : ((2-17/50-17/25)*(cell13.q/K)+1+17/50*(cell13.q/cell13.priorL)+17/25*(cell13.q/cell13.priorL)*cell13.priorB) = Record12518109.Bernstein.bsum 0 0 (24602025804907833/38123790626500000:ℝ) cell13_increment0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_increment0_g]
def cell13_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(509014583549/1017095500000:ℝ)]]
theorem cell13_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell13.q/cell13.priorL)*(1-cell13.priorB)) := by
 have heq : (1+17/25*(cell13.q/cell13.priorL)*(1-cell13.priorB)) = Record12518109.Bernstein.bsum 0 0 (509014583549/1017095500000:ℝ) cell13_increment1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_increment1_g]
def cell13_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(2035591500647/4068382000000:ℝ)]]
theorem cell13_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell13.q/cell13.priorL)*(1-cell13.priorB)) := by
 have heq : (1+omega*(cell13.q/cell13.priorL)*(1-cell13.priorB)) = Record12518109.Bernstein.bsum 0 0 (2035591500647/4068382000000:ℝ) cell13_increment2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_increment2_g]
def cell13_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(38719084/408321:ℝ), (76557200/408321:ℝ), (39471400/408321:ℝ)]]
theorem cell13_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (191393/125000:ℝ) cell13_high_increment_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_high_increment_g]
def cell13_three_gate0_g : Fin 1 → Fin 4 → ℝ := ![![(166918956338/28990791:ℝ), (1836013777586/28990791:ℝ), (3341023880986/28990791:ℝ), (1566518543662/28990791:ℝ)]]
theorem cell13_three_gate0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) := by
 have heq : (39/50*d ν*cc ν-3*ν*w ν*cc ν-32*ν*(w ν)^2) = Record12518109.Bernstein.bsum 0 3 (751135303521/62500000000:ℝ) cell13_three_gate0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_three_gate0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_three_gate0_g]
def cell13_three_gate1_g : Fin 1 → Fin 3 → ℝ := ![![(17478842/408321:ℝ), (51116716/408321:ℝ), (35271158/408321:ℝ)]]
theorem cell13_three_gate1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν) := by
 have heq : (etaD ν) = Record12518109.Bernstein.bsum 0 2 (8739421/12500000:ℝ) cell13_three_gate1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_three_gate1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_three_gate1_g]
def cell13_three_gate2_g : Fin 1 → Fin 3 → ℝ := ![![(4102229414216/45915288129:ℝ), (8138527007800/45915288129:ℝ), (4219958746100/45915288129:ℝ)]]
theorem cell13_three_gate2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν-cell13.q/K*d ν/3) := by
 have heq : (etaD ν+rr ν-cell13.q/K*d ν/3) = Record12518109.Bernstein.bsum 0 2 (40692635039/28112250000:ℝ) cell13_three_gate2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_three_gate2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_three_gate2_g]
def cell13_paired_margin0_g : Fin 1 → Fin 1 → ℝ := ![![(53632/112449:ℝ)]]
theorem cell13_paired_margin0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (1-cell13.q/K/3) := by
 have heq : (1-cell13.q/K/3) = Record12518109.Bernstein.bsum 0 0 (53632/112449:ℝ) cell13_paired_margin0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_margin0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_margin0_g]
def cell13_paired_margin1_g : Fin 1 → Fin 1 → ℝ := ![![(7719729/93890000:ℝ)]]
theorem cell13_paired_margin1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (gamma cell13-13/50) := by
 have heq : (gamma cell13-13/50) = Record12518109.Bernstein.bsum 0 0 (7719729/93890000:ℝ) cell13_paired_margin1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_margin1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_margin1_g]
def cell13_paired_margin2_g : Fin 1 → Fin 1 → ℝ := ![![(7427/75112:ℝ)]]
theorem cell13_paired_margin2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (cell13.q-gamma cell13) := by
 have heq : (cell13.q-gamma cell13) = Record12518109.Bernstein.bsum 0 0 (7427/75112:ℝ) cell13_paired_margin2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_margin2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_margin2_g]
def cell13_paired_margin3_g : Fin 1 → Fin 1 → ℝ := ![![(200873247/657230000:ℝ)]]
theorem cell13_paired_margin3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < (min (cell13.q+rho cell13.q) (3/4+rho (3/4))-gamma cell13) := by
 have heq : (min (cell13.q+rho cell13.q) (3/4+rho (3/4))-gamma cell13) = Record12518109.Bernstein.bsum 0 0 (200873247/657230000:ℝ) cell13_paired_margin3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_paired_margin3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_paired_margin3_g]
theorem cell13_paired_all {b ν : ℝ} (hb : b ∈ Set.Icc (3111/5000:ℝ) (3/4)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell13 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact cell13_paired_1_1 hb hν
 · exact cell13_paired_1_2 hb hν
 · exact cell13_paired_1_3 hb hν
 · exact cell13_paired_1_4 hb hν
 · exact cell13_paired_1_5 hb hν
 · exact cell13_paired_1_6 hb hν
 · exact cell13_paired_2_1 hb hν
 · exact cell13_paired_2_2 hb hν
 · exact cell13_paired_2_3 hb hν
 · exact cell13_paired_2_4 hb hν
 · exact cell13_paired_2_5 hb hν
 · exact cell13_paired_2_6 hb hν
 · exact cell13_paired_3_1 hb hν
 · exact cell13_paired_3_2 hb hν
 · exact cell13_paired_3_3 hb hν
 · exact cell13_paired_3_4 hb hν
 · exact cell13_paired_3_5 hb hν
 · exact cell13_paired_3_6 hb hν
 · exact cell13_paired_4_1 hb hν
 · exact cell13_paired_4_2 hb hν
 · exact cell13_paired_4_3 hb hν
 · exact cell13_paired_4_4 hb hν
 · exact cell13_paired_4_5 hb hν
 · exact cell13_paired_4_6 hb hν
 · exact cell13_paired_5_1 hb hν
 · exact cell13_paired_5_2 hb hν
 · exact cell13_paired_5_3 hb hν
 · exact cell13_paired_5_4 hb hν
 · exact cell13_paired_5_5 hb hν
 · exact cell13_paired_5_6 hb hν
 · exact cell13_paired_6_1 hb hν
 · exact cell13_paired_6_2 hb hν
 · exact cell13_paired_6_3 hb hν
 · exact cell13_paired_6_4 hb hν
 · exact cell13_paired_6_5 hb hν
 · exact cell13_paired_6_6 hb hν
end
end Record12518109Admission
