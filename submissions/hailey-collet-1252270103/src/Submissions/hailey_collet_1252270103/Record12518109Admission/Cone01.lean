/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Cell01
import Submissions.hailey_collet_1252270103.Record12518109Admission.Cones
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell1_ordered_1_1_g : Fin 1 → Fin 1 → ℝ := ![![(125301811492/399160027885:ℝ)]]
theorem cell1_ordered_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 1 1) := by
 have heq : (-orderedLow cell1 1 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_1_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_1_1_g]
def cell1_mixed_1_1_g : Fin 1 → Fin 3 → ℝ := ![![(21735447563255216/38079866660229:ℝ), (46618642930301800/38079866660229:ℝ), (25035514833687500/38079866660229:ℝ)]]
theorem cell1_mixed_1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 1 1 ν := by
 have heq : mixedLowHigh cell1 1 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_1_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_1_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_1_1_g]
def cell1_ordered_1_2_g : Fin 1 → Fin 1 → ℝ := ![![(35372047582088293/49895003485625000:ℝ)]]
theorem cell1_ordered_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 1 2) := by
 have heq : (-orderedLow cell1 1 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_1_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_1_2_g]
def cell1_mixed_1_2_g : Fin 1 → Fin 3 → ℝ := ![![(116449155546117364231/84093038874672375:ℝ), (492167366214032502337/168186077749344750:ℝ), (2084916349950340255/1345488621994758:ℝ)]]
theorem cell1_mixed_1_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 1 2 ν := by
 have heq : mixedLowHigh cell1 1 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_1_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_1_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_1_2_g]
def cell1_ordered_1_3_g : Fin 1 → Fin 1 → ℝ := ![![(319970804332416/6236875435703125:ℝ)]]
theorem cell1_ordered_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 1 3) := by
 have heq : (-orderedLow cell1 1 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_1_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_1_3_g]
def cell1_mixed_1_3_g : Fin 1 → Fin 3 → ℝ := ![![(88910681989492607728/252279116624017125:ℝ), (252414155680464054728/252279116624017125:ℝ), (1332246584723677220/2018232932992137:ℝ)]]
theorem cell1_mixed_1_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 1 3 ν := by
 have heq : mixedLowHigh cell1 1 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_1_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_1_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_1_3_g]
def cell1_ordered_1_4_g : Fin 1 → Fin 1 → ℝ := ![![(38235488695647621/49895003485625000:ℝ)]]
theorem cell1_ordered_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 1 4) := by
 have heq : (-orderedLow cell1 1 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_1_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_1_4_g]
def cell1_mixed_1_4_g : Fin 1 → Fin 3 → ℝ := ![![(294260808521278894421/252279116624017125:ℝ), (1363633391176526766467/504558233248034250:ℝ), (6265477646927500205/4036465865984274:ℝ)]]
theorem cell1_mixed_1_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 1 4 ν := by
 have heq : mixedLowHigh cell1 1 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_1_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_1_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_1_4_g]
def cell1_ordered_1_5_g : Fin 1 → Fin 1 → ℝ := ![![(36955605478317957/24947501742812500:ℝ)]]
theorem cell1_ordered_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 1 5) := by
 have heq : (-orderedLow cell1 1 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_1_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_1_5_g]
def cell1_mixed_1_5_g : Fin 1 → Fin 3 → ℝ := ![![(55512326117007242346/28031012958224125:ℝ), (123468803944006967971/28031012958224125:ℝ), (548136784689313665/224248103665793:ℝ)]]
theorem cell1_mixed_1_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 1 5 ν := by
 have heq : mixedLowHigh cell1 1 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_1_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_1_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_1_5_g]
def cell1_ordered_1_6_g : Fin 1 → Fin 1 → ℝ := ![![(246562940034458723/49895003485625000:ℝ)]]
theorem cell1_ordered_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 1 6) := by
 have heq : (-orderedLow cell1 1 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_1_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_1_6_g]
def cell1_mixed_1_6_g : Fin 1 → Fin 3 → ℝ := ![![(979882530790645217807/252279116624017125:ℝ), (3942930261004467830489/504558233248034250:ℝ), (15962196776169041735/4036465865984274:ℝ)]]
theorem cell1_mixed_1_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 1 6 ν := by
 have heq : mixedLowHigh cell1 1 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_1_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_1_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_1_6_g]
def cell1_ordered_2_1_g : Fin 1 → Fin 1 → ℝ := ![![(62509035282749207/49895003485625000:ℝ)]]
theorem cell1_ordered_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 2 1) := by
 have heq : (-orderedLow cell1 2 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_2_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_2_1_g]
def cell1_mixed_2_1_g : Fin 1 → Fin 3 → ℝ := ![![(1968904230949536448/2018232932992137:ℝ), (3930179467734255400/2018232932992137:ℝ), (656449389505562500/672744310997379:ℝ)]]
theorem cell1_mixed_2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 2 1 ν := by
 have heq : mixedLowHigh cell1 2 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_2_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_2_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_2_1_g]
def cell1_ordered_2_2_g : Fin 1 → Fin 1 → ℝ := ![![(1048923678754/399160027885:ℝ)]]
theorem cell1_ordered_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 2 2) := by
 have heq : (-orderedLow cell1 2 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_2_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_2_2_g]
def cell1_mixed_2_2_g : Fin 1 → Fin 3 → ℝ := ![![(5923540574566232896/2018232932992137:ℝ), (12053809527466920800/2018232932992137:ℝ), (6146414816364625000/2018232932992137:ℝ)]]
theorem cell1_mixed_2_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 2 2 ν := by
 have heq : mixedLowHigh cell1 2 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_2_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_2_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_2_2_g]
def cell1_ordered_2_3_g : Fin 1 → Fin 1 → ℝ := ![![(150824780989838293/49895003485625000:ℝ)]]
theorem cell1_ordered_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 2 3) := by
 have heq : (-orderedLow cell1 2 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_2_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_2_3_g]
def cell1_mixed_2_3_g : Fin 1 → Fin 3 → ℝ := ![![(315264232784188466231/84093038874672375:ℝ), (1290752487227442952337/168186077749344750:ℝ), (5297938036736465255/1345488621994758:ℝ)]]
theorem cell1_mixed_2_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 2 3 ν := by
 have heq : mixedLowHigh cell1 2 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_2_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_2_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_2_3_g]
def cell1_ordered_2_4_g : Fin 1 → Fin 1 → ℝ := ![![(14751562480301166/6236875435703125:ℝ)]]
theorem cell1_ordered_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 2 4) := by
 have heq : (-orderedLow cell1 2 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_2_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_2_4_g]
def cell1_mixed_2_4_g : Fin 1 → Fin 3 → ℝ := ![![(685355913703705913728/252279116624017125:ℝ), (1450291837200579729728/252279116624017125:ℝ), (6151779114902864720/2018232932992137:ℝ)]]
theorem cell1_mixed_2_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 2 4 ν := by
 have heq : mixedLowHigh cell1 2 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_2_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_2_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_2_4_g]
def cell1_ordered_2_5_g : Fin 1 → Fin 1 → ℝ := ![![(153688222103397621/49895003485625000:ℝ)]]
theorem cell1_ordered_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 2 5) := by
 have heq : (-orderedLow cell1 2 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_2_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_2_5_g]
def cell1_mixed_2_5_g : Fin 1 → Fin 3 → ℝ := ![![(890706040235492200421/252279116624017125:ℝ), (3759388754216758116467/504558233248034250:ℝ), (15904542707285875205/4036465865984274:ℝ)]]
theorem cell1_mixed_2_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 2 5 ν := by
 have heq : mixedLowHigh cell1 2 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_2_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_2_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_2_5_g]
def cell1_ordered_2_6_g : Fin 1 → Fin 1 → ℝ := ![![(94681972182192957/24947501742812500:ℝ)]]
theorem cell1_ordered_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 2 6) := by
 have heq : (-orderedLow cell1 2 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_2_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_2_6_g]
def cell1_mixed_2_6_g : Fin 1 → Fin 3 → ℝ := ![![(365352055589092829038/84093038874672375:ℝ), (769698972338726128913/84093038874672375:ℝ), (3250921197461003495/672744310997379:ℝ)]]
theorem cell1_mixed_2_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 2 6 ν := by
 have heq : mixedLowHigh cell1 2 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_2_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_2_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_2_6_g]
def cell1_ordered_3_1_g : Fin 1 → Fin 1 → ℝ := ![![(2655019806338199/24947501742812500:ℝ)]]
theorem cell1_ordered_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 3 1) := by
 have heq : (-orderedLow cell1 3 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_3_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_3_1_g]
def cell1_mixed_3_1_g : Fin 1 → Fin 3 → ℝ := ![![(163695094994576172/224248103665793:ℝ), (3685321196704998250/2018232932992137:ℝ), (2220138273485781250/2018232932992137:ℝ)]]
theorem cell1_mixed_3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 3 1 ν := by
 have heq : mixedLowHigh cell1 3 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_3_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_3_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_3_1_g]
def cell1_ordered_3_2_g : Fin 1 → Fin 1 → ℝ := ![![(177961768690499207/49895003485625000:ℝ)]]
theorem cell1_ordered_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 3 2) := by
 have heq : (-orderedLow cell1 3 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_3_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_3_2_g]
def cell1_mixed_3_2_g : Fin 1 → Fin 3 → ℝ := ![![(6740466084663242896/2018232932992137:ℝ), (13513200919895180800/2018232932992137:ℝ), (754320077632875000/224248103665793:ℝ)]]
theorem cell1_mixed_3_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 3 2 ν := by
 have heq : mixedLowHigh cell1 3 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_3_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_3_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_3_2_g]
def cell1_ordered_3_3_g : Fin 1 → Fin 1 → ℝ := ![![(1972545546016/399160027885:ℝ)]]
theorem cell1_ordered_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 3 3) := by
 have heq : (-orderedLow cell1 3 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_3_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_3_3_g]
def cell1_mixed_3_3_g : Fin 1 → Fin 3 → ℝ := ![![(10695102428279939344/2018232932992137:ℝ), (21636830979627846200/2018232932992137:ℝ), (10965947346543812500/2018232932992137:ℝ)]]
theorem cell1_mixed_3_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 3 3 ν := by
 have heq : mixedLowHigh cell1 3 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_3_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_3_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_3_3_g]
def cell1_ordered_3_4_g : Fin 1 → Fin 1 → ℝ := ![![(266277514397588293/49895003485625000:ℝ)]]
theorem cell1_ordered_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 3 4) := by
 have heq : (-orderedLow cell1 3 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_3_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_3_4_g]
def cell1_mixed_3_4_g : Fin 1 → Fin 3 → ℝ := ![![(171359770007419856077/28031012958224125:ℝ), (696445869413617800779/56062025916448250:ℝ), (2836986574507530085/448496207331586:ℝ)]]
theorem cell1_mixed_3_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 3 4 ν := by
 have heq : mixedLowHigh cell1 3 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_3_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_3_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_3_4_g]
def cell1_ordered_3_5_g : Fin 1 → Fin 1 → ℝ := ![![(29183154156269916/6236875435703125:ℝ)]]
theorem cell1_ordered_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 3 5) := by
 have heq : (-orderedLow cell1 3 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_3_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_3_5_g]
def cell1_mixed_3_5_g : Fin 1 → Fin 3 → ℝ := ![![(1281801145417919219728/252279116624017125:ℝ), (2648169518720695404728/252279116624017125:ℝ), (10971311645082052220/2018232932992137:ℝ)]]
theorem cell1_mixed_3_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 3 5 ν := by
 have heq : mixedLowHigh cell1 3 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_3_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_3_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_3_5_g]
def cell1_ordered_3_6_g : Fin 1 → Fin 1 → ℝ := ![![(269140955511147621/49895003485625000:ℝ)]]
theorem cell1_ordered_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 3 6) := by
 have heq : (-orderedLow cell1 3 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_3_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_3_6_g]
def cell1_mixed_3_6_g : Fin 1 → Fin 3 → ℝ := ![![(1487151271949705506421/252279116624017125:ℝ), (6155144117256989466467/504558233248034250:ℝ), (25543607767644250205/4036465865984274:ℝ)]]
theorem cell1_mixed_3_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 3 6 ν := by
 have heq : mixedLowHigh cell1 3 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_3_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_3_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_3_6_g]
def cell1_ordered_4_1_g : Fin 1 → Fin 1 → ℝ := ![![(17017410151887621/9979000697125000:ℝ)]]
theorem cell1_ordered_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 4 1) := by
 have heq : (-orderedLow cell1 4 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_4_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_4_1_g]
def cell1_mixed_4_1_g : Fin 1 → Fin 3 → ℝ := ![![(3176979232599184648/2018232932992137:ℝ), (6887209766462716100/2018232932992137:ℝ), (3718303465595500000/2018232932992137:ℝ)]]
theorem cell1_mixed_4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 4 1 ν := by
 have heq : mixedLowHigh cell1 4 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_4_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_4_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_4_1_g]
def cell1_ordered_4_2_g : Fin 1 → Fin 1 → ℝ := ![![(60381386510213199/24947501742812500:ℝ)]]
theorem cell1_ordered_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 4 2) := by
 have heq : (-orderedLow cell1 4 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_4_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_4_2_g]
def cell1_mixed_4_2_g : Fin 1 → Fin 3 → ℝ := ![![(2081605902888297332/672744310997379:ℝ), (13268342648865923650/2018232932992137:ℝ), (7039670803664968750/2018232932992137:ℝ)]]
theorem cell1_mixed_4_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 4 2 ν := by
 have heq : mixedLowHigh cell1 4 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_4_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_4_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_4_2_g]
def cell1_ordered_4_3_g : Fin 1 → Fin 1 → ℝ := ![![(293414502098249207/49895003485625000:ℝ)]]
theorem cell1_ordered_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 4 3) := by
 have heq : (-orderedLow cell1 4 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_4_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_4_3_g]
def cell1_mixed_4_3_g : Fin 1 → Fin 3 → ℝ := ![![(11512027938376949344/2018232932992137:ℝ), (23096222372056106200/2018232932992137:ℝ), (3869471076291687500/672744310997379:ℝ)]]
theorem cell1_mixed_4_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 4 3 ν := by
 have heq : mixedLowHigh cell1 4 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_4_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_4_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_4_3_g]
def cell1_ordered_4_4_g : Fin 1 → Fin 1 → ℝ := ![![(2896167413278/399160027885:ℝ)]]
theorem cell1_ordered_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 4 4) := by
 have heq : (-orderedLow cell1 4 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_4_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_4_4_g]
def cell1_mixed_4_4_g : Fin 1 → Fin 3 → ℝ := ![![(15466664281993645792/2018232932992137:ℝ), (31219852431788771600/2018232932992137:ℝ), (15785479876723000000/2018232932992137:ℝ)]]
theorem cell1_mixed_4_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 4 4 ν := by
 have heq : mixedLowHigh cell1 4 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_4_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_4_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_4_4_g]
def cell1_ordered_4_5_g : Fin 1 → Fin 1 → ℝ := ![![(381730247805338293/49895003485625000:ℝ)]]
theorem cell1_ordered_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 4 5) := by
 have heq : (-orderedLow cell1 4 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_4_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_4_5_g]
def cell1_mixed_4_5_g : Fin 1 → Fin 3 → ℝ := ![![(712894387260330670231/84093038874672375:ℝ), (2887922729254263852337/168186077749344750:ℝ), (11723981410308715255/1345488621994758:ℝ)]]
theorem cell1_mixed_4_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 4 5 ν := by
 have heq : mixedLowHigh cell1 4 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_4_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_4_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_4_5_g]
def cell1_ordered_4_6_g : Fin 1 → Fin 1 → ℝ := ![![(43614745832238666/6236875435703125:ℝ)]]
theorem cell1_ordered_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 4 6) := by
 have heq : (-orderedLow cell1 4 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_4_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_4_6_g]
def cell1_mixed_4_6_g : Fin 1 → Fin 3 → ℝ := ![![(1878246377132132525728/252279116624017125:ℝ), (3846047200240811079728/252279116624017125:ℝ), (15790844175261239720/2018232932992137:ℝ)]]
theorem cell1_mixed_4_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 4 6 ν := by
 have heq : mixedLowHigh cell1 4 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_4_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_4_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_4_6_g]
def cell1_ordered_5_1_g : Fin 1 → Fin 1 → ℝ := ![![(41216015476549953/12473750871406250:ℝ)]]
theorem cell1_ordered_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 5 1) := by
 have heq : (-orderedLow cell1 5 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_5_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_5_1_g]
def cell1_mixed_5_1_g : Fin 1 → Fin 3 → ℝ := ![![(4880702610247183748/2018232932992137:ℝ), (3363032778740144650/672744310997379:ℝ), (5216468657705218750/2018232932992137:ℝ)]]
theorem cell1_mixed_5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 5 1 ν := by
 have heq : mixedLowHigh cell1 5 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_5_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_5_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_5_1_g]
def cell1_ordered_5_2_g : Fin 1 → Fin 1 → ℝ := ![![(40107956833437621/9979000697125000:ℝ)]]
theorem cell1_ordered_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 5 2) := by
 have heq : (-orderedLow cell1 5 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_5_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_5_2_g]
def cell1_mixed_5_2_g : Fin 1 → Fin 3 → ℝ := ![![(7948541086312891096/2018232932992137:ℝ), (16470231218623641500/2018232932992137:ℝ), (8537835995774687500/2018232932992137:ℝ)]]
theorem cell1_mixed_5_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 5 2 ν := by
 have heq : mixedLowHigh cell1 5 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_5_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_5_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_5_2_g]
def cell1_ordered_5_3_g : Fin 1 → Fin 1 → ℝ := ![![(118107753214088199/24947501742812500:ℝ)]]
theorem cell1_ordered_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 5 3) := by
 have heq : (-orderedLow cell1 5 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_5_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_5_3_g]
def cell1_mixed_5_3_g : Fin 1 → Fin 3 → ℝ := ![![(3672126520792866148/672744310997379:ℝ), (22851364101026849050/2018232932992137:ℝ), (11859203333844156250/2018232932992137:ℝ)]]
theorem cell1_mixed_5_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 5 3 ν := by
 have heq : mixedLowHigh cell1 5 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_5_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_5_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_5_3_g]
def cell1_ordered_5_4_g : Fin 1 → Fin 1 → ℝ := ![![(408867235505999207/49895003485625000:ℝ)]]
theorem cell1_ordered_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 5 4) := by
 have heq : (-orderedLow cell1 5 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_5_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_5_4_g]
def cell1_mixed_5_4_g : Fin 1 → Fin 3 → ℝ := ![![(16283589792090655792/2018232932992137:ℝ), (32679243824217031600/2018232932992137:ℝ), (5475981919684750000/672744310997379:ℝ)]]
theorem cell1_mixed_5_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 5 4 ν := by
 have heq : mixedLowHigh cell1 5 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_5_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_5_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_5_4_g]
def cell1_ordered_5_5_g : Fin 1 → Fin 1 → ℝ := ![![(763957856108/79832005577:ℝ)]]
theorem cell1_ordered_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 5 5) := by
 have heq : (-orderedLow cell1 5 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_5_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_5_5_g]
def cell1_mixed_5_5_g : Fin 1 → Fin 3 → ℝ := ![![(20238226135707352240/2018232932992137:ℝ), (40802873883949697000/2018232932992137:ℝ), (20605012406902187500/2018232932992137:ℝ)]]
theorem cell1_mixed_5_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 5 5 ν := by
 have heq : mixedLowHigh cell1 5 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_5_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_5_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_5_5_g]
def cell1_ordered_5_6_g : Fin 1 → Fin 1 → ℝ := ![![(497182981213088293/49895003485625000:ℝ)]]
theorem cell1_ordered_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 5 6) := by
 have heq : (-orderedLow cell1 5 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_5_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_5_6_g]
def cell1_mixed_5_6_g : Fin 1 → Fin 3 → ℝ := ![![(911709464498401772231/84093038874672375:ℝ), (3686507850267674302337/168186077749344750:ℝ), (14937003097094840255/1345488621994758:ℝ)]]
theorem cell1_mixed_5_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 5 6 ν := by
 have heq : mixedLowHigh cell1 5 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_5_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_5_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_5_6_g]
def cell1_ordered_6_1_g : Fin 1 → Fin 1 → ℝ := ![![(313129076461378777/49895003485625000:ℝ)]]
theorem cell1_ordered_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 6 1) := by
 have heq : (-orderedLow cell1 6 1) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_6_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_6_1_g]
def cell1_mixed_6_1_g : Fin 1 → Fin 3 → ℝ := ![![(429613386555847875886/84093038874672375:ℝ), (2576612796795653002283/252279116624017125:ℝ), (10310254028756843545/2018232932992137:ℝ)]]
theorem cell1_mixed_6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 6 1 ν := by
 have heq : mixedLowHigh cell1 6 1 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_6_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_6_1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_6_1_g]
def cell1_ordered_6_2_g : Fin 1 → Fin 1 → ℝ := ![![(70079198828487453/12473750871406250:ℝ)]]
theorem cell1_ordered_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 6 2) := by
 have heq : (-orderedLow cell1 6 2) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_6_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_6_2_g]
def cell1_mixed_6_2_g : Fin 1 → Fin 3 → ℝ := ![![(9652264463960890196/2018232932992137:ℝ), (6557373262793786450/672744310997379:ℝ), (10036001187884406250/2018232932992137:ℝ)]]
theorem cell1_mixed_6_2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 6 2 ν := by
 have heq : mixedLowHigh cell1 6 2 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_6_2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_6_2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_6_2_g]
def cell1_ordered_6_3_g : Fin 1 → Fin 1 → ℝ := ![![(63198503514987621/9979000697125000:ℝ)]]
theorem cell1_ordered_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 6 3) := by
 have heq : (-orderedLow cell1 6 3) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_6_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_6_3_g]
def cell1_mixed_6_3_g : Fin 1 → Fin 3 → ℝ := ![![(12720102940026597544/2018232932992137:ℝ), (26053252670784566900/2018232932992137:ℝ), (13357368525953875000/2018232932992137:ℝ)]]
theorem cell1_mixed_6_3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 6 3 ν := by
 have heq : mixedLowHigh cell1 6 3 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_6_3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_6_3_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_6_3_g]
def cell1_ordered_6_4_g : Fin 1 → Fin 1 → ℝ := ![![(175834119917963199/24947501742812500:ℝ)]]
theorem cell1_ordered_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 6 4) := by
 have heq : (-orderedLow cell1 6 4) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_6_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_6_4_g]
def cell1_mixed_6_4_g : Fin 1 → Fin 3 → ℝ := ![![(1754215712899144988/224248103665793:ℝ), (32434385553187774450/2018232932992137:ℝ), (16678735864023343750/2018232932992137:ℝ)]]
theorem cell1_mixed_6_4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 6 4 ν := by
 have heq : mixedLowHigh cell1 6 4 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_6_4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_6_4_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_6_4_g]
def cell1_ordered_6_5_g : Fin 1 → Fin 1 → ℝ := ![![(524319968913749207/49895003485625000:ℝ)]]
theorem cell1_ordered_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 6 5) := by
 have heq : (-orderedLow cell1 6 5) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_6_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_6_5_g]
def cell1_mixed_6_5_g : Fin 1 → Fin 3 → ℝ := ![![(21055151645804362240/2018232932992137:ℝ), (42262265276377957000/2018232932992137:ℝ), (2360830921025937500/224248103665793:ℝ)]]
theorem cell1_mixed_6_5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 6 5 ν := by
 have heq : mixedLowHigh cell1 6 5 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_6_5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_6_5_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_6_5_g]
def cell1_ordered_6_6_g : Fin 1 → Fin 1 → ℝ := ![![(4743411147802/399160027885:ℝ)]]
theorem cell1_ordered_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ (-orderedLow cell1 6 6) := by
 have heq : (-orderedLow cell1 6 6) = Record12518109.Bernstein.bsum 0 0 (0:ℝ) cell1_ordered_6_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordered_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordered_6_6_g]
def cell1_mixed_6_6_g : Fin 1 → Fin 3 → ℝ := ![![(25009787989421058688/2018232932992137:ℝ), (50385895336110622400/2018232932992137:ℝ), (25424544937081375000/2018232932992137:ℝ)]]
theorem cell1_mixed_6_6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 ≤ mixedLowHigh cell1 6 6 ν := by
 have heq : mixedLowHigh cell1 6 6 ν = Record12518109.Bernstein.bsum 0 2 (0:ℝ) cell1_mixed_6_6_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_mixed_6_6_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply tensor_nonneg (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_mixed_6_6_g]
def cell1_increment0_g : Fin 1 → Fin 1 → ℝ := ![![(32767480190586707/49895003485625000:ℝ)]]
theorem cell1_increment0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < ((2-17/50-17/25)*(cell1.q/K)+1+17/50*(cell1.q/cell1.priorL)+17/25*(cell1.q/cell1.priorL)*cell1.priorB) := by
 have heq : ((2-17/50-17/25)*(cell1.q/K)+1+17/50*(cell1.q/cell1.priorL)+17/25*(cell1.q/cell1.priorL)*cell1.priorB) = Record12518109.Bernstein.bsum 0 0 (32767480190586707/49895003485625000:ℝ) cell1_increment0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_increment0_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_increment0_g]
def cell1_increment1_g : Fin 1 → Fin 1 → ℝ := ![![(665872169071/1331136875000:ℝ)]]
theorem cell1_increment1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < (1+17/25*(cell1.q/cell1.priorL)*(1-cell1.priorB)) := by
 have heq : (1+17/25*(cell1.q/cell1.priorL)*(1-cell1.priorB)) = Record12518109.Bernstein.bsum 0 0 (665872169071/1331136875000:ℝ) cell1_increment1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_increment1_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_increment1_g]
def cell1_increment2_g : Fin 1 → Fin 1 → ℝ := ![![(2663184944713/5324547500000:ℝ)]]
theorem cell1_increment2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < (1+omega*(cell1.q/cell1.priorL)*(1-cell1.priorB)) := by
 have heq : (1+omega*(cell1.q/cell1.priorL)*(1-cell1.priorB)) = Record12518109.Bernstein.bsum 0 0 (2663184944713/5324547500000:ℝ) cell1_increment2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_increment2_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_increment2_g]
def cell1_high_increment_g : Fin 1 → Fin 3 → ℝ := ![![(9620912/25281:ℝ), (19336376/25281:ℝ), (1090732/2809:ℝ)]]
theorem cell1_high_increment {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < (etaD ν+rr ν) := by
 have heq : (etaD ν+rr ν) = Record12518109.Bernstein.bsum 0 2 (601307/390625:ℝ) cell1_high_increment_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, orderedLow, mixedLowHigh, naturalFloor, complementaryFloor, floorCore, pairedCleared, etaD, localSigma, localB, localR, localL, localO, residue , cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_high_increment_g, Fin.sum_univ_succ] <;> ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_high_increment_g]
end
end Record12518109Admission
