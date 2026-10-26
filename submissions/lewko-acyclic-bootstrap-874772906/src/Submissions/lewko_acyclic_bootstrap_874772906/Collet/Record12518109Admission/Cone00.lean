/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell00
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell0_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(52839362821/164184948233:ℝ)]]
theorem cell0_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 1 1) := by
 have heq : (-orderedLow cell0 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_1_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_1_1_g]
def cell0_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(8452409918173684/4432993602291:ℝ), (17578409729355770/4432993602291:ℝ), (9143731785591250/4432993602291:ℝ)]]
theorem cell0_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 1 1 ν := by
 have heq : mixedLowHigh cell0 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_1_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_1_1_g]
def cell0_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(29444587329375549/41046237058250000:ℝ)]]
theorem cell0_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 1 2) := by
 have heq : (-orderedLow cell0 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_1_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_1_2_g]
def cell0_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(120936807233668303771/26597961613746000:ℝ), (31195434633948643987/3324745201718250:ℝ), (1030715628246646529/212783692909968:ℝ)]]
theorem cell0_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 1 2 ν := by
 have heq : mixedLowHigh cell0 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_1_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_1_2_g]
def cell0_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(664872476798201/10261559264562500:ℝ)]]
theorem cell0_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 1 3) := by
 have heq : (-orderedLow cell0 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_1_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_1_3_g]
def cell0_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(10180218663234505979/6649490403436500:ℝ), (5988267856949870776/1662372600859125:ℝ), (110821173195249721/53195923227492:ℝ)]]
theorem cell0_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 1 3 ν := by
 have heq : mixedLowHigh cell0 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_1_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_1_3_g]
def cell0_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(32029032389958353/41046237058250000:ℝ)]]
theorem cell0_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 1 4) := by
 have heq : (-orderedLow cell0 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_1_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_1_4_g]
def cell0_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(36981074125854741229/8865987204582000:ℝ), (9996054350277186013/1108248400572750:ℝ), (345033731773088471/70927897636656:ℝ)]]
theorem cell0_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 1 4 ν := by
 have heq : mixedLowHigh cell0 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_1_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_1_4_g]
def cell0_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(30699287436361951/20523118529125000:ℝ)]]
theorem cell0_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 1 5) := by
 have heq : (-orderedLow cell0 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_1_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_1_5_g]
def cell0_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(90582785051095211729/13298980806873000:ℝ), (23999895193881687263/1662372600859125:ℝ), (813458848928765971/106391846454984:ℝ)]]
theorem cell0_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 1 5 ν := by
 have heq : mixedLowHigh cell0 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_1_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_1_5_g]
def cell0_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(203077397165386039/41046237058250000:ℝ)]]
theorem cell0_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 1 6) := by
 have heq : (-orderedLow cell0 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_1_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_1_6_g]
def cell0_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(108286894053694707743/8865987204582000:ℝ), (27202995935610063671/1108248400572750:ℝ), (876398856992766157/70927897636656:ℝ)]]
theorem cell0_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 1 6 ν := by
 have heq : mixedLowHigh cell0 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_1_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_1_6_g]
def cell0_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(52052096585789451/41046237058250000:ℝ)]]
theorem cell0_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 2 1) := by
 have heq : (-orderedLow cell0 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_2_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_2_1_g]
def cell0_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(40636160958044552/13298980806873:ℝ), (81261451448028310/13298980806873:ℝ), (40678486413211250/13298980806873:ℝ)]]
theorem cell0_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 2 1 ν := by
 have heq : mixedLowHigh cell0 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_2_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_2_1_g]
def cell0_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(434048622108/164184948233:ℝ)]]
theorem cell0_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 2 2) := by
 have heq : (-orderedLow cell0 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_2_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_2_2_g]
def cell0_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(124023038895076604/13298980806873:ℝ), (250609952614106620/13298980806873:ℝ), (126693305565485000/13298980806873:ℝ)]]
theorem cell0_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 2 2 ν := by
 have heq : mixedLowHigh cell0 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_2_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_2_2_g]
def cell0_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(124746902151125549/41046237058250000:ℝ)]]
theorem cell0_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 2 3) := by
 have heq : (-orderedLow cell0 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_2_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_2_3_g]
def cell0_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(318268425514779407771/26597961613746000:ℝ), (80664115490458471487/3324745201718250:ℝ), (2618909391586026529/212783692909968:ℝ)]]
theorem cell0_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 2 3 ν := by
 have heq : mixedLowHigh cell0 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_2_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_2_3_g]
def cell0_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(24490451182235701/10261559264562500:ℝ)]]
theorem cell0_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 2 4) := by
 have heq : (-orderedLow cell0 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_2_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_2_4_g]
def cell0_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(2204189749389343777/246277422349500:ℝ), (1137874380933510538/61569355587375:ℝ), (6269995234939441/656739792932:ℝ)]]
theorem cell0_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 2 4 ν := by
 have heq : mixedLowHigh cell0 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_2_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_2_4_g]
def cell0_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(127331347211708353/41046237058250000:ℝ)]]
theorem cell0_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 2 5) := by
 have heq : (-orderedLow cell0 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_2_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_2_5_g]
def cell0_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(308274840658675327687/26597961613746000:ℝ), (79456843907341385539/3324745201718250:ℝ), (2623294958658645413/212783692909968:ℝ)]]
theorem cell0_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 2 5 ν := by
 have heq : mixedLowHigh cell0 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_2_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_2_5_g]
def cell0_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(78350444847236951/20523118529125000:ℝ)]]
theorem cell0_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 2 6) := by
 have heq : (-orderedLow cell0 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_2_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_2_6_g]
def cell0_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(189248594191650763729/13298980806873000:ℝ), (48734235622136601013/1662372600859125:ℝ), (1607555730598455971/106391846454984:ℝ)]]
theorem cell0_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 2 6 ν := by
 have heq : mixedLowHigh cell0 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_2_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_2_6_g]
def cell0_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(2837794557438657/20523118529125000:ℝ)]]
theorem cell0_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 3 1) := by
 have heq : (-orderedLow cell0 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_3_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_3_1_g]
def cell0_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(24759541296008503/8865987204582:ℝ), (9217396607528050/1477664534097:ℝ), (30580302297978125/8865987204582:ℝ)]]
theorem cell0_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 3 1 ν := by
 have heq : mixedLowHigh cell0 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_3_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_3_1_g]
def cell0_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(147354411407539451/41046237058250000:ℝ)]]
theorem cell0_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 3 2) := by
 have heq : (-orderedLow cell0 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_3_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_3_2_g]
def cell0_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(139301970098600104/13298980806873:ℝ), (279136174874067620/13298980806873:ℝ), (139940596621922500/13298980806873:ℝ)]]
theorem cell0_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 3 2 ν := by
 have heq : mixedLowHigh cell0 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_3_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_3_2_g]
def cell0_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(815257881395/164184948233:ℝ)]]
theorem cell0_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 3 3) := by
 have heq : (-orderedLow cell0 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_3_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_3_3_g]
def cell0_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(222688848035632156/13298980806873:ℝ), (448484676040145930/13298980806873:ℝ), (225955415774196250/13298980806873:ℝ)]]
theorem cell0_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 3 3 ν := by
 have heq : mixedLowHigh cell0 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_3_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_3_3_g]
def cell0_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(220049216972875549/41046237058250000:ℝ)]]
theorem cell0_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 3 4) := by
 have heq : (-orderedLow cell0 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_3_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_3_4_g]
def cell0_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(171866681265296837257/8865987204582000:ℝ), (43377598782322766329/1108248400572750:ℝ), (1402367718308468843/70927897636656:ℝ)]]
theorem cell0_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 3 4 ν := by
 have heq : mixedLowHigh cell0 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_3_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_3_4_g]
def cell0_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(48316029887673201/10261559264562500:ℝ)]]
theorem cell0_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 3 5) := by
 have heq : (-orderedLow cell0 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_3_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_3_5_g]
def cell0_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(108846027803790057979/6649490403436500:ℝ), (55456948713459698276/1662372600859125:ℝ), (904918054864939721/53195923227492:ℝ)]]
theorem cell0_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 3 5 ν := by
 have heq : mixedLowHigh cell0 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_3_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_3_5_g]
def cell0_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(222633662033458353/41046237058250000:ℝ)]]
theorem cell0_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 3 6) := by
 have heq : (-orderedLow cell0 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_3_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_3_6_g]
def cell0_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(505606458939786431687/26597961613746000:ℝ), (128925524763851213039/3324745201718250:ℝ), (4211488721998025413/212783692909968:ℝ)]]
theorem cell0_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 3 6 ν := by
 have heq : mixedLowHigh cell0 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_3_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_3_6_g]
def cell0_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(14321672290772353/8209247411650000:ℝ)]]
theorem cell0_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 4 1) := by
 have heq : (-orderedLow cell0 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_4_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_4_1_g]
def cell0_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(23459615032371569/4432993602291:ℝ), (49013989272005530/4432993602291:ℝ), (25572106214043125/4432993602291:ℝ)]]
theorem cell0_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 4 1 ν := by
 have heq : mixedLowHigh cell0 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_4_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_4_1_g]
def cell0_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(50488951968313657/20523118529125000:ℝ)]]
theorem cell0_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 4 2) := by
 have heq : (-orderedLow cell0 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_4_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_4_2_g]
def cell0_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(271610242169136613/26597961613746:ℝ), (280831292893791760/13298980806873:ℝ), (290265127311356875/26597961613746:ℝ)]]
theorem cell0_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 4 2 ν := by
 have heq : mixedLowHigh cell0 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_4_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_4_2_g]
def cell0_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(242656726229289451/41046237058250000:ℝ)]]
theorem cell0_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 4 3) := by
 have heq : (-orderedLow cell0 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_4_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_4_3_g]
def cell0_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(26440864359906184/1477664534097:ℝ), (159003632766702310/4432993602291:ℝ), (79734235610211250/4432993602291:ℝ)]]
theorem cell0_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 4 3 ν := by
 have heq : mixedLowHigh cell0 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_4_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_4_3_g]
def cell0_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(1196467140682/164184948233:ℝ)]]
theorem cell0_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 4 4) := by
 have heq : (-orderedLow cell0 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_4_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_4_4_g]
def cell0_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(11902024339858804/492554844699:ℝ), (7979745672422040/164184948233:ℝ), (12045093554922500/492554844699:ℝ)]]
theorem cell0_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 4 4 ν := by
 have heq : mixedLowHigh cell0 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_4_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_4_4_g]
def cell0_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(315351531794625549/41046237058250000:ℝ)]]
theorem cell0_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 4 5) := by
 have heq : (-orderedLow cell0 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_4_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_4_5_g]
def cell0_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(712931662077001615771/26597961613746000:ℝ), (179601477203478126487/3324745201718250:ℝ), (5795296918264786529/212783692909968:ℝ)]]
theorem cell0_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 4 5 ν := by
 have heq : mixedLowHigh cell0 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_4_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_4_5_g]
def cell0_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(72141608593110701/10261559264562500:ℝ)]]
theorem cell0_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 4 6) := by
 have heq : (-orderedLow cell0 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_4_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_4_6_g]
def cell0_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(158178932374067833979/6649490403436500:ℝ), (80191289141714612026/1662372600859125:ℝ), (1301966495699784721/53195923227492:ℝ)]]
theorem cell0_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 4 6 ν := by
 have heq : mixedLowHigh cell0 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_4_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_4_6_g]
def cell0_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(17192641724105777/5130779632281250:ℝ)]]
theorem cell0_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 5 1) := by
 have heq : (-orderedLow cell0 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_5_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_5_1_g]
def cell0_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(69078918833477773/8865987204582:ℝ), (70375788721426910/4432993602291:ℝ), (23902707519398125/2955329068194:ℝ)]]
theorem cell0_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 5 1 ν := by
 have heq : mixedLowHigh cell0 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_5_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_5_1_g]
def cell0_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(33382135255122353/8209247411650000:ℝ)]]
theorem cell0_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 5 2) := by
 have heq : (-orderedLow cell0 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_5_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_5_2_g]
def cell0_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(169044654237670259/13298980806873:ℝ), (344916691242055900/13298980806873:ℝ), (175978428850840625/13298980806873:ℝ)]]
theorem cell0_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 5 2 ν := by
 have heq : mixedLowHigh cell0 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_5_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_5_2_g]
def cell0_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(98140109379188657/20523118529125000:ℝ)]]
theorem cell0_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 5 3) := by
 have heq : (-orderedLow cell0 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_5_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_5_3_g]
def cell0_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(468941860450247717/26597961613746:ℝ), (478706016319831070/13298980806873:ℝ), (488789347728779375/26597961613746:ℝ)]]
theorem cell0_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 5 3 ν := by
 have heq : mixedLowHigh cell0 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_5_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_5_3_g]
def cell0_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(337959041051039451/41046237058250000:ℝ)]]
theorem cell0_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 5 4) := by
 have heq : (-orderedLow cell0 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_5_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_5_4_g]
def cell0_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(336633588379711208/13298980806873:ℝ), (674885621726146240/13298980806873:ℝ), (338464817039345000/13298980806873:ℝ)]]
theorem cell0_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 5 4 ν := by
 have heq : mixedLowHigh cell0 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_5_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_5_4_g]
def cell0_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(1577676399969/164184948233:ℝ)]]
theorem cell0_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 5 5) := by
 have heq : (-orderedLow cell0 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_5_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_5_5_g]
def cell0_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(420020466316743260/13298980806873:ℝ), (844234122892224550/13298980806873:ℝ), (424479636191618750/13298980806873:ℝ)]]
theorem cell0_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 5 5 ν := by
 have heq : mixedLowHigh cell0 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_5_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_5_5_g]
def cell0_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(410653846616375549/41046237058250000:ℝ)]]
theorem cell0_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 5 6) := by
 have heq : (-orderedLow cell0 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_5_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_5_6_g]
def cell0_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(910263280358112719771/26597961613746000:ℝ), (229070158059987953987/3324745201718250:ℝ), (7383490681604166529/212783692909968:ℝ)]]
theorem cell0_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 5 6 ν := by
 have heq : mixedLowHigh cell0 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_5_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_5_6_g]
def cell0_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(259628546036778961/41046237058250000:ℝ)]]
theorem cell0_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 6 1) := by
 have heq : (-orderedLow cell0 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_6_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_6_1_g]
def cell0_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(23564116839555205757/1477664534097000:ℝ), (17672286230852822737/554124200286375:ℝ), (565629370420529029/35463948818328:ℝ)]]
theorem cell0_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 6 1 ν := by
 have heq : mixedLowHigh cell0 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_6_1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_6_1_g]
def cell0_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(29105431076824527/5130779632281250:ℝ)]]
theorem cell0_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 6 2) := by
 have heq : (-orderedLow cell0 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_6_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_6_2_g]
def cell0_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(404568374781544423/26597961613746:ℝ), (409002089590320040/13298980806873:ℝ), (413648588092005625/26597961613746:ℝ)]]
theorem cell0_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 6 2 ν := by
 have heq : mixedLowHigh cell0 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_6_2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_6_2_g]
def cell0_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(52442598219472353/8209247411650000:ℝ)]]
theorem cell0_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 6 3) := by
 have heq : (-orderedLow cell0 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_6_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_6_3_g]
def cell0_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(267710463378225811/13298980806873:ℝ), (542791414668095210/13298980806873:ℝ), (275240539059551875/13298980806873:ℝ)]]
theorem cell0_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 6 3 ν := by
 have heq : mixedLowHigh cell0 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_6_3_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_6_3_g]
def cell0_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(145791266790063657/20523118529125000:ℝ)]]
theorem cell0_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 6 4) := by
 have heq : (-orderedLow cell0 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_6_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_6_4_g]
def cell0_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(222091159577119607/8865987204582:ℝ), (225526913248623460/4432993602291:ℝ), (76368174238466875/2955329068194:ℝ)]]
theorem cell0_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 6 4 ν := by
 have heq : mixedLowHigh cell0 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_6_4_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_6_4_g]
def cell0_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(433261355872789451/41046237058250000:ℝ)]]
theorem cell0_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 6 5) := by
 have heq : (-orderedLow cell0 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_6_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_6_5_g]
def cell0_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(435299397520266760/13298980806873:ℝ), (872760345152185550/13298980806873:ℝ), (437726927248056250/13298980806873:ℝ)]]
theorem cell0_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 6 5 ν := by
 have heq : mixedLowHigh cell0 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_6_5_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_6_5_g]
def cell0_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(1958885659256/164184948233:ℝ)]]
theorem cell0_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell0 6 6) := by
 have heq : (-orderedLow cell0 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell0_ordered_6_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_ordered_6_6_g]
def cell0_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(518686275457298812/13298980806873:ℝ), (1042108846318263860/13298980806873:ℝ), (523741746400330000/13298980806873:ℝ)]]
theorem cell0_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell0 6 6 ν := by
 have heq : mixedLowHigh cell0 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell0_mixed_6_6_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_mixed_6_6_g]
def cell0_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(27123856127429451/41046237058250000:ℝ)]]
theorem cell0_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell0.q/K)+1+17/50*(cell0.q/cell0.priorL)+17/25*(cell0.q/cell0.priorL)*cell0.priorB) := by
 have heq : ((2-17/50-17/25)*(cell0.q/K)+1+17/50*(cell0.q/cell0.priorL)+17/25*(cell0.q/cell0.priorL)*cell0.priorB) = Record12518109.Bernstein.bsum 0 0 (27123856127429451/41046237058250000:ℝ) cell0_increment0_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_increment0_g]
def cell0_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(547642965703/1095062750000:ℝ)]]
theorem cell0_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell0.q/cell0.priorL)*(1-cell0.priorB)) := by
 have heq : (1+17/25*(cell0.q/cell0.priorL)*(1-cell0.priorB)) = Record12518109.Bernstein.bsum 0 0 (547642965703/1095062750000:ℝ) cell0_increment1_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_increment1_g]
def cell0_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(2190460272109/4380251000000:ℝ)]]
theorem cell0_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell0.q/cell0.priorL)*(1-cell0.priorB)) := by
 have heq : (1+omega*(cell0.q/cell0.priorL)*(1-cell0.priorB)) = Record12518109.Bernstein.bsum 0 0 (2190460272109/4380251000000:ℝ) cell0_increment2_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_increment2_g]
def cell0_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(193019/162:ℝ), (194051/81:ℝ), (195731/162:ℝ)]]
theorem cell0_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (39/2000:ℝ) (3/125:ℝ)) (hν : ν ∈ Set.Icc (357/500:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (193019/125000:ℝ) cell0_high_increment_g (39/2000:ℝ) (3/125:ℝ) (357/500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell0, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell0_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell0_high_increment_g]
end
end Record12518109Admission
