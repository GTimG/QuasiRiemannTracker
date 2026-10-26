/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.All
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission
def additional0_floor0_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(118519/81:ℝ), (250070/81:ℝ), (131875/81:ℝ)]]
theorem additional0_floor0_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 1 false ν := by
 have heq : naturalFloor cell0 1 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_1_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_1_1_g]
def additional0_floor1_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(14655680531/9108369:ℝ), (30750021430/9108369:ℝ), (16130774375/9108369:ℝ)]]
theorem additional0_floor1_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 1 true ν := by
 have heq : naturalFloor cell0 1 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_1_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_1_1_g]
def additional0_complement_floor_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(118519/81:ℝ), (250070/81:ℝ), (131875/81:ℝ)]]
theorem additional0_complement_floor_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 1 ν := by
 have heq : complementaryFloor 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_1_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_1_1_g]
def additional0_paired_cleared_1_1_g : Fin 3 → Fin 3 → ℝ := ![![(8343968750/6561:ℝ), (18314010250/6561:ℝ), (9933875000/6561:ℝ)],
  ![(18314010250/6561:ℝ), (35551422244000/5858973:ℝ), (19133068718750/5858973:ℝ)],
  ![(9933875000/6561:ℝ), (19133068718750/5858973:ℝ), (10230472656250/5858973:ℝ)]]
theorem additional0_paired_cleared_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 1 1 b ν := by
 have heq : pairedCleared cell0 1 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_1_1_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_1_1_g]
theorem additional0_paired_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 1 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_1_1 hb hν
def additional0_floor0_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(237038/81:ℝ), (500140/81:ℝ), (263750/81:ℝ)]]
theorem additional0_floor0_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 2 false ν := by
 have heq : naturalFloor cell0 1 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_1_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_1_2_g]
def additional0_floor1_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(237038/81:ℝ), (500140/81:ℝ), (263750/81:ℝ)]]
theorem additional0_floor1_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 2 true ν := by
 have heq : naturalFloor cell0 1 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_1_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_1_2_g]
def additional0_complement_floor_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(237038/81:ℝ), (500140/81:ℝ), (263750/81:ℝ)]]
theorem additional0_complement_floor_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 2 ν := by
 have heq : complementaryFloor 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_1_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_1_2_g]
def additional0_paired_cleared_1_2_g : Fin 3 → Fin 3 → ℝ := ![![(29148078125/6561:ℝ), (61297145500/6561:ℝ), (32076734375/6561:ℝ)],
  ![(57159135250/6561:ℝ), (107401855366000/5858973:ℝ), (56230862843750/5858973:ℝ)],
  ![(27974890625/6561:ℝ), (52599562062500/5858973:ℝ), (27554693359375/5858973:ℝ)]]
theorem additional0_paired_cleared_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 1 2 b ν := by
 have heq : pairedCleared cell0 1 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_1_2_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_1_2_g]
theorem additional0_paired_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 1 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_1_2 hb hν
def additional0_floor0_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(118519/27:ℝ), (250070/27:ℝ), (131875/27:ℝ)]]
theorem additional0_floor0_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 3 false ν := by
 have heq : naturalFloor cell0 1 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_1_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_1_3_g]
def additional0_floor1_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(38653691593/9108369:ℝ), (81730464290/9108369:ℝ), (43186073125/9108369:ℝ)]]
theorem additional0_floor1_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 3 true ν := by
 have heq : naturalFloor cell0 1 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_1_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_1_3_g]
def additional0_complement_floor_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(118519/27:ℝ), (250070/27:ℝ), (131875/27:ℝ)]]
theorem additional0_complement_floor_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 3 ν := by
 have heq : complementaryFloor 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_1_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_1_3_g]
def additional0_paired_cleared_1_3_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (199362250/243:ℝ), (195343750/243:ℝ)],
  ![(3723086750/2187:ℝ), (9754669496000/1952991:ℝ), (6366010656250/1952991:ℝ)],
  ![(3711031250/2187:ℝ), (8131080968750/1952991:ℝ), (4785484375000/1952991:ℝ)]]
theorem additional0_paired_cleared_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 1 3 b ν := by
 have heq : pairedCleared cell0 1 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_1_3_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_1_3_g]
theorem additional0_paired_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 1 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_1_3 hb hν
def additional0_floor0_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(474076/81:ℝ), (1000280/81:ℝ), (527500/81:ℝ)]]
theorem additional0_floor0_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 4 false ν := by
 have heq : naturalFloor cell0 1 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_1_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_1_4_g]
def additional0_floor1_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(50652697124/9108369:ℝ), (107220685720/9108369:ℝ), (56713722500/9108369:ℝ)]]
theorem additional0_floor1_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 4 true ν := by
 have heq : naturalFloor cell0 1 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_1_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_1_4_g]
def additional0_complement_floor_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(474076/81:ℝ), (1000280/81:ℝ), (527500/81:ℝ)]]
theorem additional0_complement_floor_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 4 ν := by
 have heq : complementaryFloor 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_1_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_1_4_g]
def additional0_paired_cleared_1_4_g : Fin 3 → Fin 3 → ℝ := ![![(6934703125/2187:ℝ), (16121972000/2187:ℝ), (9139046875/2187:ℝ)],
  ![(16671461750/2187:ℝ), (33704813870000/1952991:ℝ), (18731942031250/1952991:ℝ)],
  ![(9724703125/2187:ℝ), (19286578750000/1952991:ℝ), (10560224609375/1952991:ℝ)]]
theorem additional0_paired_cleared_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 1 4 b ν := by
 have heq : pairedCleared cell0 1 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_1_4_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_1_4_g]
theorem additional0_paired_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 1 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_1_4 hb hν
def additional0_floor0_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(592595/81:ℝ), (1250350/81:ℝ), (659375/81:ℝ)]]
theorem additional0_floor0_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 5 false ν := by
 have heq : naturalFloor cell0 1 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_1_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_1_5_g]
def additional0_floor1_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(6961300295/1012041:ℝ), (14745656350/1012041:ℝ), (7804596875/1012041:ℝ)]]
theorem additional0_floor1_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 5 true ν := by
 have heq : naturalFloor cell0 1 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_1_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_1_5_g]
def additional0_complement_floor_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(592595/81:ℝ), (1250350/81:ℝ), (659375/81:ℝ)]]
theorem additional0_complement_floor_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 5 ν := by
 have heq : complementaryFloor 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_1_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_1_5_g]
def additional0_paired_cleared_1_5_g : Fin 3 → Fin 3 → ℝ := ![![(13869406250/2187:ℝ), (30449683750/2187:ℝ), (16520000000/2187:ℝ)],
  ![(29619836750/2187:ℝ), (57654958244000/1952991:ℝ), (31097873406250/1952991:ℝ)],
  ![(5246125000/729:ℝ), (10147358843750/650997:ℝ), (1814996093750/216999:ℝ)]]
theorem additional0_paired_cleared_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 1 5 b ν := by
 have heq : pairedCleared cell0 1 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_1_5_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_1_5_g]
theorem additional0_paired_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 1 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_1_5 hb hν
def additional0_floor0_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(934864/81:ℝ), (1880420/81:ℝ), (947500/81:ℝ)]]
theorem additional0_floor0_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 6 false ν := by
 have heq : naturalFloor cell0 1 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_1_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_1_6_g]
def additional0_floor1_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(99811171936/9108369:ℝ), (200931748580/9108369:ℝ), (101339177500/9108369:ℝ)]]
theorem additional0_floor1_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 1 6 true ν := by
 have heq : naturalFloor cell0 1 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_1_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_1_6_g]
def additional0_complement_floor_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(934864/81:ℝ), (1880420/81:ℝ), (947500/81:ℝ)]]
theorem additional0_complement_floor_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 1 6 ν := by
 have heq : complementaryFloor 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_1_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_1_6_g]
def additional0_paired_cleared_1_6_g : Fin 3 → Fin 3 → ℝ := ![![(112364515625/6561:ℝ), (219167186500/6561:ℝ), (106585671875/6561:ℝ)],
  ![(226602135250/6561:ℝ), (394803587854000/5858973:ℝ), (192064226843750/5858973:ℝ)],
  ![(114201453125/6561:ℝ), (199023347937500/5858973:ℝ), (96851576171875/5858973:ℝ)]]
theorem additional0_paired_cleared_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 1 6 b ν := by
 have heq : pairedCleared cell0 1 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_1_6_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_1_6_g]
theorem additional0_paired_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 1 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_1_6 hb hν
def additional0_floor0_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(193019/81:ℝ), (387070/81:ℝ), (194375/81:ℝ)]]
theorem additional0_floor0_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 1 false ν := by
 have heq : naturalFloor cell0 2 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_2_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_2_1_g]
def additional0_floor1_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(193019/81:ℝ), (387070/81:ℝ), (194375/81:ℝ)]]
theorem additional0_floor1_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 1 true ν := by
 have heq : naturalFloor cell0 2 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_2_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_2_1_g]
def additional0_complement_floor_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(193019/81:ℝ), (387070/81:ℝ), (194375/81:ℝ)]]
theorem additional0_complement_floor_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 1 ν := by
 have heq : complementaryFloor 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_2_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_2_1_g]
def additional0_paired_cleared_2_1_g : Fin 3 → Fin 3 → ℝ := ![![(29148078125/6561:ℝ), (57159135250/6561:ℝ), (27974890625/6561:ℝ)],
  ![(61297145500/6561:ℝ), (107401855366000/5858973:ℝ), (52599562062500/5858973:ℝ)],
  ![(32076734375/6561:ℝ), (56230862843750/5858973:ℝ), (27554693359375/5858973:ℝ)]]
theorem additional0_paired_cleared_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 2 1 b ν := by
 have heq : pairedCleared cell0 2 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_2_1_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_2_1_g]
theorem additional0_paired_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 2 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_2_1 hb hν
def additional0_floor0_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(227846/27:ℝ), (461380/27:ℝ), (233750/27:ℝ)]]
theorem additional0_floor0_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 2 false ν := by
 have heq : naturalFloor cell0 2 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_2_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_2_2_g]
def additional0_floor1_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(79519839562/9108369:ℝ), (160904958860/9108369:ℝ), (81457986250/9108369:ℝ)]]
theorem additional0_floor1_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 2 true ν := by
 have heq : naturalFloor cell0 2 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_2_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_2_2_g]
def additional0_complement_floor_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(227846/27:ℝ), (461380/27:ℝ), (233750/27:ℝ)]]
theorem additional0_complement_floor_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 2 ν := by
 have heq : complementaryFloor 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_2_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_2_2_g]
def additional0_paired_cleared_2_2_g : Fin 3 → Fin 3 → ℝ := ![![(38789687500/2187:ℝ), (77993673500/2187:ℝ), (39179875000/2187:ℝ)],
  ![(77993673500/2187:ℝ), (140007649496000/1952991:ℝ), (70316670812500/1952991:ℝ)],
  ![(39179875000/2187:ℝ), (70316670812500/1952991:ℝ), (35307945312500/1952991:ℝ)]]
theorem additional0_paired_cleared_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 2 2 b ν := by
 have heq : pairedCleared cell0 2 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_2_2_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_2_2_g]
theorem additional0_paired_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 2 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_2_2 hb hν
def additional0_floor0_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(802057/81:ℝ), (1634210/81:ℝ), (833125/81:ℝ)]]
theorem additional0_floor0_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 3 false ν := by
 have heq : naturalFloor cell0 2 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_2_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_2_3_g]
def additional0_floor1_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(91518845093/9108369:ℝ), (186395180290/9108369:ℝ), (94985635625/9108369:ℝ)]]
theorem additional0_floor1_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 3 true ν := by
 have heq : naturalFloor cell0 2 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_2_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_2_3_g]
def additional0_complement_floor_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(802057/81:ℝ), (1634210/81:ℝ), (833125/81:ℝ)]]
theorem additional0_complement_floor_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 3 ν := by
 have heq : complementaryFloor 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_2_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_2_3_g]
def additional0_paired_cleared_2_3_g : Fin 3 → Fin 3 → ℝ := ![![(45724390625/2187:ℝ), (92321385250/2187:ℝ), (46560828125/2187:ℝ)],
  ![(90942048500/2187:ℝ), (163957793870000/1952991:ℝ), (82682602187500/1952991:ℝ)],
  ![(15064515625/729:ℝ), (27157389531250/650997:ℝ), (13694228515625/650997:ℝ)]]
theorem additional0_paired_cleared_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 2 3 b ν := by
 have heq : pairedCleared cell0 2 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_2_3_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_2_3_g]
theorem additional0_paired_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 2 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_2_3 hb hν
def additional0_floor0_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(920576/81:ℝ), (1884280/81:ℝ), (965000/81:ℝ)]]
theorem additional0_floor0_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 4 false ν := by
 have heq : naturalFloor cell0 2 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_2_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_2_4_g]
def additional0_floor1_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(920576/81:ℝ), (1884280/81:ℝ), (965000/81:ℝ)]]
theorem additional0_floor1_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 4 true ν := by
 have heq : naturalFloor cell0 2 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_2_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_2_4_g]
def additional0_complement_floor_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(920576/81:ℝ), (1884280/81:ℝ), (965000/81:ℝ)]]
theorem additional0_complement_floor_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 4 ν := by
 have heq : complementaryFloor 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_2_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_2_4_g]
def additional0_paired_cleared_2_4_g : Fin 3 → Fin 3 → ℝ := ![![(108025093750/6561:ℝ), (221049791000/6561:ℝ), (112880031250/6561:ℝ)],
  ![(226836270500/6561:ℝ), (413735534732000/5858973:ℝ), (210914975687500/5858973:ℝ)],
  ![(118738843750/6561:ℝ), (216210186625000/5858973:ℝ), (110049816406250/5858973:ℝ)]]
theorem additional0_paired_cleared_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 2 4 b ν := by
 have heq : pairedCleared cell0 2 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_2_4_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_2_4_g]
theorem additional0_paired_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 2 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_2_4 hb hν
def additional0_floor0_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(38485/3:ℝ), (26350:ℝ), (40625/3:ℝ)]]
theorem additional0_floor0_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 5 false ν := by
 have heq : naturalFloor cell0 2 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_2_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_2_5_g]
def additional0_floor1_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(115516856155/9108369:ℝ), (237375623150/9108369:ℝ), (122040934375/9108369:ℝ)]]
theorem additional0_floor1_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 5 true ν := by
 have heq : naturalFloor cell0 2 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_2_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_2_5_g]
def additional0_complement_floor_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(38485/3:ℝ), (26350:ℝ), (40625/3:ℝ)]]
theorem additional0_complement_floor_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 5 ν := by
 have heq : complementaryFloor 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_2_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_2_5_g]
def additional0_paired_cleared_2_5_g : Fin 3 → Fin 3 → ℝ := ![![(128829203125/6561:ℝ), (264032926250/6561:ℝ), (135022890625/6561:ℝ)],
  ![(265681395500/6561:ℝ), (485585967854000/5858973:ℝ), (248012769812500/5858973:ℝ)],
  ![(136779859375/6561:ℝ), (249676679968750/5858973:ℝ), (127374037109375/5858973:ℝ)]]
theorem additional0_paired_cleared_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 2 5 b ν := by
 have heq : pairedCleared cell0 2 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_2_5_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_2_5_g]
theorem additional0_paired_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 2 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_2_5 hb hν
def additional0_floor0_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1157614/81:ℝ), (2384420/81:ℝ), (1228750/81:ℝ)]]
theorem additional0_floor0_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 6 false ν := by
 have heq : naturalFloor cell0 2 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_2_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_2_6_g]
def additional0_floor1_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(127515861686/9108369:ℝ), (262865844580/9108369:ℝ), (135568583750/9108369:ℝ)]]
theorem additional0_floor1_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 2 6 true ν := by
 have heq : naturalFloor cell0 2 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_2_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_2_6_g]
def additional0_complement_floor_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(1157614/81:ℝ), (2384420/81:ℝ), (1228750/81:ℝ)]]
theorem additional0_complement_floor_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 2 6 ν := by
 have heq : complementaryFloor 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_2_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_2_6_g]
def additional0_paired_cleared_2_6_g : Fin 3 → Fin 3 → ℝ := ![![(149633312500/6561:ℝ), (307016061500/6561:ℝ), (157165750000/6561:ℝ)],
  ![(304526520500/6561:ℝ), (557436400976000/5858973:ℝ), (285110563937500/5858973:ℝ)],
  ![(154820875000/6561:ℝ), (283143173312500/5858973:ℝ), (144698257812500/5858973:ℝ)]]
theorem additional0_paired_cleared_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 2 6 b ν := by
 have heq : pairedCleared cell0 2 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_2_6_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_2_6_g]
theorem additional0_paired_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 2 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_2_6 hb hν
def additional0_floor0_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(267019/81:ℝ), (586070/81:ℝ), (319375/81:ℝ)]]
theorem additional0_floor0_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 1 false ν := by
 have heq : naturalFloor cell0 3 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_3_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_3_1_g]
def additional0_floor1_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(28697682031/9108369:ℝ), (63273085430/9108369:ℝ), (34611836875/9108369:ℝ)]]
theorem additional0_floor1_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 1 true ν := by
 have heq : naturalFloor cell0 3 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_3_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_3_1_g]
def additional0_complement_floor_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(17266/9:ℝ), (121690/27:ℝ), (70000/27:ℝ)]]
theorem additional0_complement_floor_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 1 ν := by
 have heq : complementaryFloor 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_3_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_3_1_g]
def additional0_paired_cleared_3_1_g : Fin 3 → Fin 3 → ℝ := ![![(0:ℝ), (3723086750/2187:ℝ), (3711031250/2187:ℝ)],
  ![(199362250/243:ℝ), (9754669496000/1952991:ℝ), (8131080968750/1952991:ℝ)],
  ![(195343750/243:ℝ), (6366010656250/1952991:ℝ), (4785484375000/1952991:ℝ)]]
theorem additional0_paired_cleared_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 3 1 b ν := by
 have heq : pairedCleared cell0 3 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_3_1_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_3_1_g]
theorem additional0_paired_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 3 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_3_1 hb hν
def additional0_floor0_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(758038/81:ℝ), (1521140/81:ℝ), (763750/81:ℝ)]]
theorem additional0_floor0_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 2 false ν := by
 have heq : naturalFloor cell0 3 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_3_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_3_2_g]
def additional0_floor1_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(86568952562/9108369:ℝ), (173680571860/9108369:ℝ), (87184486250/9108369:ℝ)]]
theorem additional0_floor1_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 2 true ν := by
 have heq : naturalFloor cell0 3 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_3_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_3_2_g]
def additional0_complement_floor_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(758038/81:ℝ), (1521140/81:ℝ), (763750/81:ℝ)]]
theorem additional0_complement_floor_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 2 ν := by
 have heq : complementaryFloor 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_3_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_3_2_g]
def additional0_paired_cleared_3_2_g : Fin 3 → Fin 3 → ℝ := ![![(45724390625/2187:ℝ), (90942048500/2187:ℝ), (15064515625/729:ℝ)],
  ![(92321385250/2187:ℝ), (163957793870000/1952991:ℝ), (27157389531250/650997:ℝ)],
  ![(46560828125/2187:ℝ), (82682602187500/1952991:ℝ), (13694228515625/650997:ℝ)]]
theorem additional0_paired_cleared_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 3 2 b ν := by
 have heq : pairedCleared cell0 3 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_3_2_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_3_2_g]
theorem additional0_paired_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 3 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_3_2 hb hν
def additional0_floor0_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1248557/81:ℝ), (2518210/81:ℝ), (1270625/81:ℝ)]]
theorem additional0_floor0_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 3 false ν := by
 have heq : naturalFloor cell0 3 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_3_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_3_3_g]
def additional0_floor1_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(48127999531/3036123:ℝ), (97019965430/3036123:ℝ), (48928399375/3036123:ℝ)]]
theorem additional0_floor1_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 3 true ν := by
 have heq : naturalFloor cell0 3 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_3_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_3_3_g]
def additional0_complement_floor_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(1248557/81:ℝ), (2518210/81:ℝ), (1270625/81:ℝ)]]
theorem additional0_complement_floor_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 3 ν := by
 have heq : complementaryFloor 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_3_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_3_3_g]
def additional0_paired_cleared_3_3_g : Fin 3 → Fin 3 → ℝ := ![![(224394156250/6561:ℝ), (449648030750/6561:ℝ), (225145375000/6561:ℝ)],
  ![(449648030750/6561:ℝ), (804494474732000/5858973:ℝ), (402766956156250/5858973:ℝ)],
  ![(225145375000/6561:ℝ), (402766956156250/5858973:ℝ), (201617199218750/5858973:ℝ)]]
theorem additional0_paired_cleared_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 3 3 b ν := by
 have heq : pairedCleared cell0 3 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_3_3_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_3_3_g]
theorem additional0_paired_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 3 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_3_3 hb hν
def additional0_floor0_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(455692/27:ℝ), (922760/27:ℝ), (467500/27:ℝ)]]
theorem additional0_floor0_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 4 false ν := by
 have heq : naturalFloor cell0 3 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_3_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_3_4_g]
def additional0_floor1_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(156383004124/9108369:ℝ), (316550117720/9108369:ℝ), (160312847500/9108369:ℝ)]]
theorem additional0_floor1_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 4 true ν := by
 have heq : naturalFloor cell0 3 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_3_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_3_4_g]
def additional0_complement_floor_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(455692/27:ℝ), (922760/27:ℝ), (467500/27:ℝ)]]
theorem additional0_complement_floor_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 4 ν := by
 have heq : complementaryFloor 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_3_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_3_4_g]
def additional0_paired_cleared_3_4_g : Fin 3 → Fin 3 → ℝ := ![![(245198265625/6561:ℝ), (492631166000/6561:ℝ), (247288234375/6561:ℝ)],
  ![(488493155750/6561:ℝ), (876344907854000/5858973:ℝ), (439864750281250/5858973:ℝ)],
  ![(243186390625/6561:ℝ), (436233449500000/5858973:ℝ), (218941419921875/5858973:ℝ)]]
theorem additional0_paired_cleared_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 3 4 b ν := by
 have heq : pairedCleared cell0 3 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_3_4_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_3_4_g]
theorem additional0_paired_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 3 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_3_4 hb hν
def additional0_floor0_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(1485595/81:ℝ), (3018350/81:ℝ), (1534375/81:ℝ)]]
theorem additional0_floor0_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 5 false ν := by
 have heq : naturalFloor cell0 3 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_3_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_3_5_g]
def additional0_floor1_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(168382009655/9108369:ℝ), (342040339150/9108369:ℝ), (173840496875/9108369:ℝ)]]
theorem additional0_floor1_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 5 true ν := by
 have heq : naturalFloor cell0 3 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_3_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_3_5_g]
def additional0_complement_floor_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(1485595/81:ℝ), (3018350/81:ℝ), (1534375/81:ℝ)]]
theorem additional0_complement_floor_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 5 ν := by
 have heq : complementaryFloor 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_3_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_3_5_g]
def additional0_paired_cleared_3_5_g : Fin 3 → Fin 3 → ℝ := ![![(216050187500/6561:ℝ), (436716801250/6561:ℝ), (220485781250/6561:ℝ)],
  ![(442503280750/6561:ℝ), (798207060976000/5858973:ℝ), (402731919406250/5858973:ℝ)],
  ![(226344593750/6561:ℝ), (408027130343750/5858973:ℝ), (205743179687500/5858973:ℝ)]]
theorem additional0_paired_cleared_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 3 5 b ν := by
 have heq : pairedCleared cell0 3 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_3_5_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_3_5_g]
theorem additional0_paired_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 3 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_3_5 hb hν
def additional0_floor0_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(1604114/81:ℝ), (3268420/81:ℝ), (1666250/81:ℝ)]]
theorem additional0_floor0_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 6 false ν := by
 have heq : naturalFloor cell0 3 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_3_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_3_6_g]
def additional0_floor1_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(1604114/81:ℝ), (3268420/81:ℝ), (1666250/81:ℝ)]]
theorem additional0_floor1_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 3 6 true ν := by
 have heq : naturalFloor cell0 3 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_3_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_3_6_g]
def additional0_complement_floor_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(1604114/81:ℝ), (3268420/81:ℝ), (1666250/81:ℝ)]]
theorem additional0_complement_floor_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 3 6 ν := by
 have heq : complementaryFloor 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_3_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_3_6_g]
def additional0_paired_cleared_3_6_g : Fin 3 → Fin 3 → ℝ := ![![(236854296875/6561:ℝ), (479699936500/6561:ℝ), (242628640625/6561:ℝ)],
  ![(481348405750/6561:ℝ), (870057494098000/5858973:ℝ), (439829713531250/5858973:ℝ)],
  ![(244385609375/6561:ℝ), (441493623687500/5858973:ℝ), (223067400390625/5858973:ℝ)]]
theorem additional0_paired_cleared_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 3 6 b ν := by
 have heq : pairedCleared cell0 3 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_3_6_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_3_6_g]
theorem additional0_paired_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 3 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_3_6 hb hν
def additional0_floor0_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(564769/81:ℝ), (1165070/81:ℝ), (600625/81:ℝ)]]
theorem additional0_floor0_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 1 false ν := by
 have heq : naturalFloor cell0 4 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_4_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_4_1_g]
def additional0_floor1_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(60851034281/9108369:ℝ), (125751156430/9108369:ℝ), (64936555625/9108369:ℝ)]]
theorem additional0_floor1_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 1 true ν := by
 have heq : naturalFloor cell0 4 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_4_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_4_1_g]
def additional0_complement_floor_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(341519/81:ℝ), (723070/81:ℝ), (381875/81:ℝ)]]
theorem additional0_complement_floor_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 1 ν := by
 have heq : complementaryFloor 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_4_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_4_1_g]
def additional0_paired_cleared_4_1_g : Fin 3 → Fin 3 → ℝ := ![![(6934703125/2187:ℝ), (16671461750/2187:ℝ), (9724703125/2187:ℝ)],
  ![(16121972000/2187:ℝ), (33704813870000/1952991:ℝ), (19286578750000/1952991:ℝ)],
  ![(9139046875/2187:ℝ), (18731942031250/1952991:ℝ), (10560224609375/1952991:ℝ)]]
theorem additional0_paired_cleared_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 4 1 b ν := by
 have heq : pairedCleared cell0 4 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_4_1_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_4_1_g]
theorem additional0_paired_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 4 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_4_1 hb hν
def additional0_floor0_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(277346/27:ℝ), (573380/27:ℝ), (98750/9:ℝ)]]
theorem additional0_floor0_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 2 false ν := by
 have heq : naturalFloor cell0 4 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_4_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_4_2_g]
def additional0_floor1_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(277346/27:ℝ), (573380/27:ℝ), (98750/9:ℝ)]]
theorem additional0_floor1_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 2 true ν := by
 have heq : naturalFloor cell0 4 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_4_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_4_2_g]
def additional0_complement_floor_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(2384489/243:ℝ), (4939420/243:ℝ), (2556875/243:ℝ)]]
theorem additional0_complement_floor_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 2 ν := by
 have heq : complementaryFloor 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_4_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_4_2_g]
def additional0_paired_cleared_4_2_g : Fin 3 → Fin 3 → ℝ := ![![(108025093750/6561:ℝ), (226836270500/6561:ℝ), (118738843750/6561:ℝ)],
  ![(221049791000/6561:ℝ), (413735534732000/5858973:ℝ), (216210186625000/5858973:ℝ)],
  ![(112880031250/6561:ℝ), (210914975687500/5858973:ℝ), (110049816406250/5858973:ℝ)]]
theorem additional0_paired_cleared_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 4 2 b ν := by
 have heq : pairedCleared cell0 4 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_4_2_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_4_2_g]
theorem additional0_paired_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 4 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_4_2 hb hν
def additional0_floor0_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(441019/27:ℝ), (885070/27:ℝ), (49375/3:ℝ)]]
theorem additional0_floor0_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 3 false ν := by
 have heq : naturalFloor cell0 4 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_4_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_4_3_g]
def additional0_floor1_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(151433111593/9108369:ℝ), (303835509290/9108369:ℝ), (152511698125/9108369:ℝ)]]
theorem additional0_floor1_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 3 true ν := by
 have heq : naturalFloor cell0 4 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_4_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_4_3_g]
def additional0_complement_floor_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(441019/27:ℝ), (885070/27:ℝ), (49375/3:ℝ)]]
theorem additional0_complement_floor_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 3 ν := by
 have heq : complementaryFloor 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_4_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_4_3_g]
def additional0_paired_cleared_4_3_g : Fin 3 → Fin 3 → ℝ := ![![(245198265625/6561:ℝ), (488493155750/6561:ℝ), (243186390625/6561:ℝ)],
  ![(492631166000/6561:ℝ), (876344907854000/5858973:ℝ), (436233449500000/5858973:ℝ)],
  ![(247288234375/6561:ℝ), (439864750281250/5858973:ℝ), (218941419921875/5858973:ℝ)]]
theorem additional0_paired_cleared_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 4 3 b ν := by
 have heq : pairedCleared cell0 4 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_4_3_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_4_3_g]
theorem additional0_paired_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 4 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_4_3 hb hν
def additional0_floor0_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(1813576/81:ℝ), (3652280/81:ℝ), (1840000/81:ℝ)]]
theorem additional0_floor0_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 4 false ν := by
 have heq : naturalFloor cell0 4 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_4_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_4_4_g]
def additional0_floor1_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(209248157624/9108369:ℝ), (421214833720/9108369:ℝ), (212112410000/9108369:ℝ)]]
theorem additional0_floor1_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 4 true ν := by
 have heq : naturalFloor cell0 4 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_4_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_4_4_g]
def additional0_complement_floor_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(1813576/81:ℝ), (3652280/81:ℝ), (1840000/81:ℝ)]]
theorem additional0_complement_floor_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 4 ν := by
 have heq : complementaryFloor 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_4_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_4_4_g]
def additional0_paired_cleared_4_4_g : Fin 3 → Fin 3 → ℝ := ![![(332419250000/6561:ℝ), (665315041000/6561:ℝ), (332751125000/6561:ℝ)],
  ![(665315041000/6561:ℝ), (1188966000976000/5858973:ℝ), (594583899875000/5858973:ℝ)],
  ![(332751125000/6561:ℝ), (594583899875000/5858973:ℝ), (297310562500000/5858973:ℝ)]]
theorem additional0_paired_cleared_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 4 4 b ν := by
 have heq : pairedCleared cell0 4 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_4_4_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_4_4_g]
theorem additional0_paired_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 4 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_4_4 hb hν
def additional0_floor0_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(1932095/81:ℝ), (3902350/81:ℝ), (1971875/81:ℝ)]]
theorem additional0_floor0_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 5 false ν := by
 have heq : naturalFloor cell0 4 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_4_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_4_5_g]
def additional0_floor1_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(73749054385/3036123:ℝ), (148901685050/3036123:ℝ), (75213353125/3036123:ℝ)]]
theorem additional0_floor1_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 5 true ν := by
 have heq : naturalFloor cell0 4 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_4_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_4_5_g]
def additional0_complement_floor_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(1932095/81:ℝ), (3902350/81:ℝ), (1971875/81:ℝ)]]
theorem additional0_complement_floor_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 5 ν := by
 have heq : complementaryFloor 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_4_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_4_5_g]
def additional0_paired_cleared_4_5_g : Fin 3 → Fin 3 → ℝ := ![![(353223359375/6561:ℝ), (708298176250/6561:ℝ), (354893984375/6561:ℝ)],
  ![(704160166000/6561:ℝ), (1260816434098000/5858973:ℝ), (631681694000000/5858973:ℝ)],
  ![(350792140625/6561:ℝ), (628050393218750/5858973:ℝ), (314634783203125/5858973:ℝ)]]
theorem additional0_paired_cleared_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 4 5 b ν := by
 have heq : pairedCleared cell0 4 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_4_5_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_4_5_g]
theorem additional0_paired_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 4 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_4_5 hb hν
def additional0_floor0_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(227846/9:ℝ), (461380/9:ℝ), (233750/9:ℝ)]]
theorem additional0_floor0_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 6 false ν := by
 have heq : naturalFloor cell0 4 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_4_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_4_6_g]
def additional0_floor1_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(233246168686/9108369:ℝ), (472195276580/9108369:ℝ), (239167708750/9108369:ℝ)]]
theorem additional0_floor1_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 4 6 true ν := by
 have heq : naturalFloor cell0 4 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_4_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_4_6_g]
def additional0_complement_floor_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(227846/9:ℝ), (461380/9:ℝ), (233750/9:ℝ)]]
theorem additional0_complement_floor_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 4 6 ν := by
 have heq : complementaryFloor 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_4_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_4_6_g]
def additional0_paired_cleared_4_6_g : Fin 3 → Fin 3 → ℝ := ![![(108025093750/2187:ℝ), (217461270500/2187:ℝ), (109363843750/2187:ℝ)],
  ![(219390097000/2187:ℝ), (394226195740000/1952991:ℝ), (198182954375000/1952991:ℝ)],
  ![(458093750/9:ℝ), (22216447187500/216999:ℝ), (11164316406250/216999:ℝ)]]
theorem additional0_paired_cleared_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 4 6 b ν := by
 have heq : pairedCleared cell0 4 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_4_6_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_4_6_g]
theorem additional0_paired_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 4 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_4_6 hb hν
def additional0_floor0_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(862519/81:ℝ), (1744070/81:ℝ), (881875/81:ℝ)]]
theorem additional0_floor0_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 1 false ν := by
 have heq : naturalFloor cell0 5 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_5_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_5_1_g]
def additional0_floor1_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(31001462177/3036123:ℝ), (62743075810/3036123:ℝ), (31753758125/3036123:ℝ)]]
theorem additional0_floor1_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 1 true ν := by
 have heq : naturalFloor cell0 5 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_5_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_5_1_g]
def additional0_complement_floor_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(527644/81:ℝ), (1081070/81:ℝ), (553750/81:ℝ)]]
theorem additional0_complement_floor_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 1 ν := by
 have heq : complementaryFloor 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_5_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_5_1_g]
def additional0_paired_cleared_5_1_g : Fin 3 → Fin 3 → ℝ := ![![(13869406250/2187:ℝ), (29619836750/2187:ℝ), (5246125000/729:ℝ)],
  ![(30449683750/2187:ℝ), (57654958244000/1952991:ℝ), (10147358843750/650997:ℝ)],
  ![(16520000000/2187:ℝ), (31097873406250/1952991:ℝ), (1814996093750/216999:ℝ)]]
theorem additional0_paired_cleared_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 5 1 b ν := by
 have heq : pairedCleared cell0 5 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_5_1_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_5_1_g]
theorem additional0_paired_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 5 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_5_1 hb hν
def additional0_floor0_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(13948:ℝ), (255460/9:ℝ), (130000/9:ℝ)]]
theorem additional0_floor0_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 2 false ν := by
 have heq : naturalFloor cell0 5 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_5_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_5_2_g]
def additional0_floor1_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(125715193312/9108369:ℝ), (255906093860/9108369:ℝ), (130263767500/9108369:ℝ)]]
theorem additional0_floor1_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 2 true ν := by
 have heq : naturalFloor cell0 5 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_5_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_5_2_g]
def additional0_complement_floor_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(2942864/243:ℝ), (6013420/243:ℝ), (3072500/243:ℝ)]]
theorem additional0_complement_floor_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 2 ν := by
 have heq : complementaryFloor 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_5_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_5_2_g]
def additional0_paired_cleared_5_2_g : Fin 3 → Fin 3 → ℝ := ![![(128829203125/6561:ℝ), (265681395500/6561:ℝ), (136779859375/6561:ℝ)],
  ![(264032926250/6561:ℝ), (485585967854000/5858973:ℝ), (249676679968750/5858973:ℝ)],
  ![(135022890625/6561:ℝ), (248012769812500/5858973:ℝ), (127374037109375/5858973:ℝ)]]
theorem additional0_paired_cleared_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 5 2 b ν := by
 have heq : pairedCleared cell0 5 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_5_2_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_5_2_g]
theorem additional0_paired_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 5 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_5_2 hb hν
def additional0_floor0_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(1397057/81:ℝ), (2854210/81:ℝ), (1458125/81:ℝ)]]
theorem additional0_floor0_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 3 false ν := by
 have heq : naturalFloor cell0 5 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_5_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_5_3_g]
def additional0_floor1_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(158426000093/9108369:ℝ), (323582960290/9108369:ℝ), (165266260625/9108369:ℝ)]]
theorem additional0_floor1_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 3 true ν := by
 have heq : naturalFloor cell0 5 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_5_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_5_3_g]
def additional0_complement_floor_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(1397057/81:ℝ), (2854210/81:ℝ), (1458125/81:ℝ)]]
theorem additional0_complement_floor_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 3 ν := by
 have heq : complementaryFloor 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_5_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_5_3_g]
def additional0_paired_cleared_5_3_g : Fin 3 → Fin 3 → ℝ := ![![(216050187500/6561:ℝ), (442503280750/6561:ℝ), (226344593750/6561:ℝ)],
  ![(436716801250/6561:ℝ), (798207060976000/5858973:ℝ), (408027130343750/5858973:ℝ)],
  ![(220485781250/6561:ℝ), (402731919406250/5858973:ℝ), (205743179687500/5858973:ℝ)]]
theorem additional0_paired_cleared_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 5 3 b ν := by
 have heq : pairedCleared cell0 5 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_5_3_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_5_3_g]
theorem additional0_paired_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 5 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_5_3 hb hν
def additional0_floor0_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(1888076/81:ℝ), (3789280/81:ℝ), (1902500/81:ℝ)]]
theorem additional0_floor0_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 4 false ν := by
 have heq : naturalFloor cell0 5 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_5_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_5_4_g]
def additional0_floor1_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(72099090208/3036123:ℝ), (144663482240/3036123:ℝ), (72612970000/3036123:ℝ)]]
theorem additional0_floor1_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 4 true ν := by
 have heq : naturalFloor cell0 5 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_5_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_5_4_g]
def additional0_complement_floor_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(1888076/81:ℝ), (3789280/81:ℝ), (1902500/81:ℝ)]]
theorem additional0_complement_floor_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 4 ν := by
 have heq : complementaryFloor 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_5_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_5_4_g]
def additional0_paired_cleared_5_4_g : Fin 3 → Fin 3 → ℝ := ![![(353223359375/6561:ℝ), (704160166000/6561:ℝ), (350792140625/6561:ℝ)],
  ![(708298176250/6561:ℝ), (1260816434098000/5858973:ℝ), (628050393218750/5858973:ℝ)],
  ![(354893984375/6561:ℝ), (631681694000000/5858973:ℝ), (314634783203125/5858973:ℝ)]]
theorem additional0_paired_cleared_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 5 4 b ν := by
 have heq : pairedCleared cell0 5 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_5_4_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_5_4_g]
theorem additional0_paired_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 5 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_5_4 hb hν
def additional0_floor0_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(792865/27:ℝ), (1595450/27:ℝ), (803125/27:ℝ)]]
theorem additional0_floor0_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 5 false ν := by
 have heq : naturalFloor cell0 5 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_5_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_5_5_g]
def additional0_floor1_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(274112316655/9108369:ℝ), (551369771150/9108369:ℝ), (277439621875/9108369:ℝ)]]
theorem additional0_floor1_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 5 true ν := by
 have heq : naturalFloor cell0 5 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_5_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_5_5_g]
def additional0_complement_floor_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(792865/27:ℝ), (1595450/27:ℝ), (803125/27:ℝ)]]
theorem additional0_complement_floor_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 5 ν := by
 have heq : complementaryFloor 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_5_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_5_5_g]
def additional0_paired_cleared_5_5_g : Fin 3 → Fin 3 → ℝ := ![![(146814781250/2187:ℝ), (293660683750/2187:ℝ), (146785625000/2187:ℝ)],
  ![(293660683750/2187:ℝ), (524479175740000/1952991:ℝ), (262133614531250/1952991:ℝ)],
  ![(146785625000/2187:ℝ), (262133614531250/1952991:ℝ), (131001308593750/1952991:ℝ)]]
theorem additional0_paired_cleared_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 5 5 b ν := by
 have heq : pairedCleared cell0 5 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_5_5_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_5_5_g]
theorem additional0_paired_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 5 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_5_5 hb hν
def additional0_floor0_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(2497114/81:ℝ), (5036420/81:ℝ), (2541250/81:ℝ)]]
theorem additional0_floor0_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 6 false ν := by
 have heq : naturalFloor cell0 5 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_5_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_5_6_g]
def additional0_floor1_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(286111322186/9108369:ℝ), (576859992580/9108369:ℝ), (290967271250/9108369:ℝ)]]
theorem additional0_floor1_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 5 6 true ν := by
 have heq : naturalFloor cell0 5 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_5_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_5_6_g]
def additional0_complement_floor_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(2497114/81:ℝ), (5036420/81:ℝ), (2541250/81:ℝ)]]
theorem additional0_complement_floor_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 5 6 ν := by
 have heq : complementaryFloor 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_5_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_5_6_g]
def additional0_paired_cleared_5_6_g : Fin 3 → Fin 3 → ℝ := ![![(51249828125/729:ℝ), (102662798500/729:ℝ), (51388859375/729:ℝ)],
  ![(306609058750/2187:ℝ), (548429320114000/1952991:ℝ), (274499545906250/1952991:ℝ)],
  ![(152799296875/2187:ℝ), (273289112312500/1952991:ℝ), (136776048828125/1952991:ℝ)]]
theorem additional0_paired_cleared_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 5 6 b ν := by
 have heq : pairedCleared cell0 5 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_5_6_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_5_6_g]
theorem additional0_paired_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 5 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_5_6 hb hν
def additional0_floor0_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(1160269/81:ℝ), (2323070/81:ℝ), (1163125/81:ℝ)]]
theorem additional0_floor0_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 1 false ν := by
 have heq : naturalFloor cell0 6 1 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_6_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_6_1_g]
def additional0_floor1_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(125157738781/9108369:ℝ), (250707298430/9108369:ℝ), (125585993125/9108369:ℝ)]]
theorem additional0_floor1_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 1 true ν := by
 have heq : naturalFloor cell0 6 1 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_6_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_6_1_g]
def additional0_complement_floor_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(237923/27:ℝ), (479690/27:ℝ), (26875/3:ℝ)]]
theorem additional0_complement_floor_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 1 ν := by
 have heq : complementaryFloor 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_6_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_6_1_g]
def additional0_paired_cleared_6_1_g : Fin 3 → Fin 3 → ℝ := ![![(112364515625/6561:ℝ), (226602135250/6561:ℝ), (114201453125/6561:ℝ)],
  ![(219167186500/6561:ℝ), (394803587854000/5858973:ℝ), (199023347937500/5858973:ℝ)],
  ![(106585671875/6561:ℝ), (192064226843750/5858973:ℝ), (96851576171875/5858973:ℝ)]]
theorem additional0_paired_cleared_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 6 1 b ν := by
 have heq : pairedCleared cell0 6 1 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_6_1_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_6_1_g]
theorem additional0_paired_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 6 1 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_6_1 hb hν
def additional0_floor0_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(475846/27:ℝ), (959380/27:ℝ), (53750/3:ℝ)]]
theorem additional0_floor0_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 2 false ν := by
 have heq : naturalFloor cell0 6 2 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_6_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_6_2_g]
def additional0_floor1_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(157868545562/9108369:ℝ), (318384164860/9108369:ℝ), (160588486250/9108369:ℝ)]]
theorem additional0_floor1_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 2 true ν := by
 have heq : naturalFloor cell0 6 2 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_6_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_6_2_g]
def additional0_complement_floor_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(3501239/243:ℝ), (7087420/243:ℝ), (3588125/243:ℝ)]]
theorem additional0_complement_floor_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 2 ν := by
 have heq : complementaryFloor 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_6_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_6_2_g]
def additional0_paired_cleared_6_2_g : Fin 3 → Fin 3 → ℝ := ![![(149633312500/6561:ℝ), (304526520500/6561:ℝ), (154820875000/6561:ℝ)],
  ![(307016061500/6561:ℝ), (557436400976000/5858973:ℝ), (283143173312500/5858973:ℝ)],
  ![(157165750000/6561:ℝ), (285110563937500/5858973:ℝ), (144698257812500/5858973:ℝ)]]
theorem additional0_paired_cleared_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 6 2 b ν := by
 have heq : pairedCleared cell0 6 2 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_6_2_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_6_2_g]
theorem additional0_paired_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 6 2 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_6_2 hb hν
def additional0_floor0_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(1694807/81:ℝ), (3433210/81:ℝ), (1739375/81:ℝ)]]
theorem additional0_floor0_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 3 false ν := by
 have heq : naturalFloor cell0 6 3 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_6_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_6_3_g]
def additional0_floor1_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(1694807/81:ℝ), (3433210/81:ℝ), (1739375/81:ℝ)]]
theorem additional0_floor1_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 3 true ν := by
 have heq : naturalFloor cell0 6 3 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_6_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_6_3_g]
def additional0_complement_floor_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(4861171/243:ℝ), (9857630/243:ℝ), (4999375/243:ℝ)]]
theorem additional0_complement_floor_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 3 ν := by
 have heq : complementaryFloor 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_6_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_6_3_g]
def additional0_paired_cleared_6_3_g : Fin 3 → Fin 3 → ℝ := ![![(236854296875/6561:ℝ), (481348405750/6561:ℝ), (244385609375/6561:ℝ)],
  ![(479699936500/6561:ℝ), (870057494098000/5858973:ℝ), (441493623687500/5858973:ℝ)],
  ![(242628640625/6561:ℝ), (439829713531250/5858973:ℝ), (223067400390625/5858973:ℝ)]]
theorem additional0_paired_cleared_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 6 3 b ν := by
 have heq : pairedCleared cell0 6 3 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_6_3_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_6_3_g]
theorem additional0_paired_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 6 3 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_6_3 hb hν
def additional0_floor0_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(1962076/81:ℝ), (3988280/81:ℝ), (2027500/81:ℝ)]]
theorem additional0_floor0_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 4 false ν := by
 have heq : naturalFloor cell0 6 4 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_6_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_6_4_g]
def additional0_floor1_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(223290159124/9108369:ℝ), (453737897720/9108369:ℝ), (230593472500/9108369:ℝ)]]
theorem additional0_floor1_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 4 true ν := by
 have heq : naturalFloor cell0 6 4 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_6_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_6_4_g]
def additional0_complement_floor_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(1962076/81:ℝ), (3988280/81:ℝ), (2027500/81:ℝ)]]
theorem additional0_complement_floor_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 4 ν := by
 have heq : complementaryFloor 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_6_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_6_4_g]
def additional0_paired_cleared_6_4_g : Fin 3 → Fin 3 → ℝ := ![![(108025093750/2187:ℝ), (219390097000/2187:ℝ), (458093750/9:ℝ)],
  ![(217461270500/2187:ℝ), (394226195740000/1952991:ℝ), (22216447187500/216999:ℝ)],
  ![(109363843750/2187:ℝ), (198182954375000/1952991:ℝ), (11164316406250/216999:ℝ)]]
theorem additional0_paired_cleared_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 6 4 b ν := by
 have heq : pairedCleared cell0 6 4 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_6_4_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_6_4_g]
theorem additional0_paired_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 6 4 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_6_4 hb hν
def additional0_floor0_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(2453095/81:ℝ), (4923350/81:ℝ), (2471875/81:ℝ)]]
theorem additional0_floor0_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 5 false ν := by
 have heq : naturalFloor cell0 6 5 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_6_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_6_5_g]
def additional0_floor1_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(281161429655/9108369:ℝ), (564145384150/9108369:ℝ), (283166121875/9108369:ℝ)]]
theorem additional0_floor1_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 5 true ν := by
 have heq : naturalFloor cell0 6 5 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_6_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_6_5_g]
def additional0_complement_floor_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(2453095/81:ℝ), (4923350/81:ℝ), (2471875/81:ℝ)]]
theorem additional0_complement_floor_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 5 ν := by
 have heq : complementaryFloor 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_6_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_6_5_g]
def additional0_paired_cleared_6_5_g : Fin 3 → Fin 3 → ℝ := ![![(51249828125/729:ℝ), (306609058750/2187:ℝ), (152799296875/2187:ℝ)],
  ![(102662798500/729:ℝ), (548429320114000/1952991:ℝ), (273289112312500/1952991:ℝ)],
  ![(51388859375/729:ℝ), (274499545906250/1952991:ℝ), (136776048828125/1952991:ℝ)]]
theorem additional0_paired_cleared_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 6 5 b ν := by
 have heq : pairedCleared cell0 6 5 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_6_5_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_6_5_g]
theorem additional0_paired_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 6 5 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_6_5 hb hν
def additional0_floor0_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(2943614/81:ℝ), (5920420/81:ℝ), (2978750/81:ℝ)]]
theorem additional0_floor0_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 6 false ν := by
 have heq : naturalFloor cell0 6 6 false ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor0_6_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor0_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor0_6_6_g]
def additional0_floor1_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(37664052854/1012041:ℝ), (75724967620/1012041:ℝ), (38085203750/1012041:ℝ)]]
theorem additional0_floor1_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ naturalFloor cell0 6 6 true ν := by
 have heq : naturalFloor cell0 6 6 true ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_floor1_6_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_floor1_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_floor1_6_6_g]
def additional0_complement_floor_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(2943614/81:ℝ), (5920420/81:ℝ), (2978750/81:ℝ)]]
theorem additional0_complement_floor_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ complementaryFloor 6 6 ν := by
 have heq : complementaryFloor 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) additional0_complement_floor_6_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_complement_floor_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_complement_floor_6_6_g]
def additional0_paired_cleared_6_6_g : Fin 3 → Fin 3 → ℝ := ![![(548469437500/6561:ℝ), (1096649061500/6561:ℝ), (547962625000/6561:ℝ)],
  ![(1096649061500/6561:ℝ), (1957909053464000/5858973:ℝ), (978217787312500/5858973:ℝ)],
  ![(547962625000/6561:ℝ), (978217787312500/5858973:ℝ), (488697289062500/5858973:ℝ)]]
theorem additional0_paired_cleared_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ pairedCleared cell0 6 6 b ν := by
 have heq : pairedCleared cell0 6 6 b ν = Record12518109.Bernstein.bsum 2 2 (0:ℝ) additional0_paired_cleared_6_6_g (357/500:ℝ) (3/4:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, additional0_paired_cleared_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [additional0_paired_cleared_6_6_g]
theorem additional0_paired_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) : 0 ≤ pairedGap cell0 6 6 b ν := by
 apply pairedGap_nonneg_of_cleared (by dsimp [d]; linarith [hb.2]) (by dsimp [d]; linarith [hν.2])
 exact additional0_paired_cleared_6_6 hb hν
theorem additional0_floor0_base {ν : ℝ} (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ naturalFloor cell0 (i.val+1) (j.val+1) false ν := by
 fin_cases i <;> fin_cases j
 · exact additional0_floor0_1_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_1_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_1_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_1_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_1_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_1_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_2_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_2_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_2_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_2_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_2_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_2_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_3_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_3_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_3_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_3_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_3_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_3_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_4_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_4_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_4_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_4_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_4_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_4_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_5_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_5_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_5_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_5_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_5_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_5_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_6_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_6_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_6_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_6_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_6_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor0_6_6 (b:=(39/2000:ℝ)) (by norm_num) hν
theorem additional0_floor1_base {ν : ℝ} (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ naturalFloor cell0 (i.val+1) (j.val+1) true ν := by
 fin_cases i <;> fin_cases j
 · exact additional0_floor1_1_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_1_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_1_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_1_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_1_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_1_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_2_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_2_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_2_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_2_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_2_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_2_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_3_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_3_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_3_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_3_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_3_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_3_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_4_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_4_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_4_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_4_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_4_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_4_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_5_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_5_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_5_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_5_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_5_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_5_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_6_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_6_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_6_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_6_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_6_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_floor1_6_6 (b:=(39/2000:ℝ)) (by norm_num) hν
theorem additional0_complement_base {ν : ℝ} (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ complementaryFloor (i.val+1) (j.val+1) ν := by
 fin_cases i <;> fin_cases j
 · exact additional0_complement_floor_1_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_1_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_1_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_1_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_1_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_1_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_2_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_2_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_2_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_2_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_2_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_2_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_3_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_3_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_3_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_3_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_3_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_3_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_4_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_4_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_4_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_4_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_4_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_4_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_5_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_5_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_5_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_5_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_5_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_5_6 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_6_1 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_6_2 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_6_3 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_6_4 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_6_5 (b:=(39/2000:ℝ)) (by norm_num) hν
 · exact additional0_complement_floor_6_6 (b:=(39/2000:ℝ)) (by norm_num) hν
theorem additional0_paired_base {b ν : ℝ} (hb : b ∈ Set.Icc (357/500:ℝ) (3/4)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4)) (i j : Fin 6) : 0 ≤ pairedGap cell0 (i.val+1) (j.val+1) b ν := by
 fin_cases i <;> fin_cases j
 · exact additional0_paired_1_1 hb hν
 · exact additional0_paired_1_2 hb hν
 · exact additional0_paired_1_3 hb hν
 · exact additional0_paired_1_4 hb hν
 · exact additional0_paired_1_5 hb hν
 · exact additional0_paired_1_6 hb hν
 · exact additional0_paired_2_1 hb hν
 · exact additional0_paired_2_2 hb hν
 · exact additional0_paired_2_3 hb hν
 · exact additional0_paired_2_4 hb hν
 · exact additional0_paired_2_5 hb hν
 · exact additional0_paired_2_6 hb hν
 · exact additional0_paired_3_1 hb hν
 · exact additional0_paired_3_2 hb hν
 · exact additional0_paired_3_3 hb hν
 · exact additional0_paired_3_4 hb hν
 · exact additional0_paired_3_5 hb hν
 · exact additional0_paired_3_6 hb hν
 · exact additional0_paired_4_1 hb hν
 · exact additional0_paired_4_2 hb hν
 · exact additional0_paired_4_3 hb hν
 · exact additional0_paired_4_4 hb hν
 · exact additional0_paired_4_5 hb hν
 · exact additional0_paired_4_6 hb hν
 · exact additional0_paired_5_1 hb hν
 · exact additional0_paired_5_2 hb hν
 · exact additional0_paired_5_3 hb hν
 · exact additional0_paired_5_4 hb hν
 · exact additional0_paired_5_5 hb hν
 · exact additional0_paired_5_6 hb hν
 · exact additional0_paired_6_1 hb hν
 · exact additional0_paired_6_2 hb hν
 · exact additional0_paired_6_3 hb hν
 · exact additional0_paired_6_4 hb hν
 · exact additional0_paired_6_5 hb hν
 · exact additional0_paired_6_6 hb hν
end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.additional0_floor0_base
#print axioms QRH.Record12518109Source.additional0_floor1_base
#print axioms QRH.Record12518109Source.additional0_complement_base
#print axioms QRH.Record12518109Source.additional0_paired_base
