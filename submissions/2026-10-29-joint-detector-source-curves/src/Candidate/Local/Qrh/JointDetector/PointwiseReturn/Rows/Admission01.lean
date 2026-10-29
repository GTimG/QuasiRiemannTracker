/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.PowerAdmissions
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.PointwiseReturn
open QRH.Record1252270103Return
noncomputable section

def admission01_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1:ℝ), (0:ℝ)]]
theorem admission01_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (5/2:ℝ) admission01_00_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_00_coefficients, Fin.sum_univ_succ, admission_power_capP_00] <;> ring
theorem admission01_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
  rw [admission01_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_00_coefficients]

def admission01_01_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
    Record12518109.Bernstein.bsum 0 0 (2:ℝ) admission01_01_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_01_coefficients, Fin.sum_univ_succ, admission_power_capP_01] <;> ring
theorem admission01_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
  rw [admission01_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_01_coefficients]

def admission01_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(619999/5000000:ℝ), (0:ℝ)]]
theorem admission01_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (9380001/10000000:ℝ) admission01_02_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_02_coefficients, Fin.sum_univ_succ, admission_power_capP_02] <;> ring
theorem admission01_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
  rw [admission01_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_02_coefficients]

def admission01_03_coefficients : Fin 2 → Fin 2 → ℝ := ![![(215/9:ℝ), (12:ℝ)],
![(116/9:ℝ), (0:ℝ)]]
theorem admission01_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
    Record12518109.Bernstein.bsum 1 1 (73/48:ℝ) admission01_03_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_03_coefficients, Fin.sum_univ_succ, admission_power_capP_03] <;> ring
theorem admission01_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
  rw [admission01_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_03_coefficients]

def admission01_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(121859997/5000000:ℝ), (24:ℝ), (0:ℝ)],
![(78140003/1250000:ℝ), (14380001/156250:ℝ), (9380001/312500:ℝ)]]
theorem admission01_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (84420009/640000000:ℝ) admission01_04_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_04_coefficients, Fin.sum_univ_succ, admission_power_capP_04] <;> ring
theorem admission01_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
  rw [admission01_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_04_coefficients]

def admission01_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(60131203/1000000:ℝ), (227321509/1875000:ℝ), (227756009/3750000:ℝ)],
![(0:ℝ), (13545997/1875000:ℝ), (25231997/3750000:ℝ)]]
theorem admission01_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (99494391/512000000:ℝ) admission01_05_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_05_coefficients, Fin.sum_univ_succ, admission_power_capP_05] <;> ring
theorem admission01_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
  rw [admission01_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_05_coefficients]

def admission01_06_coefficients : Fin 2 → Fin 3 → ℝ := ![![(147501093337/1665000000:ℝ), (8826681961/104062500:ℝ), (0:ℝ)],
![(67171033579/416250000:ℝ), (11258022479/52031250:ℝ), (137060037/2312500:ℝ)]]
theorem admission01_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
    Record12518109.Bernstein.bsum 1 2 (3935818039/14208000000:ℝ) admission01_06_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_06_coefficients, Fin.sum_univ_succ, admission_power_capP_06] <;> ring
theorem admission01_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
  rw [admission01_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_06_coefficients]

def admission01_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3144073273/15000000:ℝ), (1009560037/2812500:ℝ), (9380001/62500:ℝ)],
![(185313271/3750000:ℝ), (34319989/703125:ℝ), (0:ℝ)]]
theorem admission01_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (34393337/32000000:ℝ) admission01_07_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_07_coefficients, Fin.sum_univ_succ, admission_power_capP_07] <;> ring
theorem admission01_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
  rw [admission01_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_07_coefficients]

def admission01_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (4516602881/45000000:ℝ), (9147544289/45000000:ℝ), (307613429/3000000:ℝ)],
![(216132147/1000000:ℝ), (29224502033/45000000:ℝ), (29693482577/45000000:ℝ), (678173813/3000000:ℝ)]]
theorem admission01_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (650462603/16384000000:ℝ) admission01_08_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_08_coefficients, Fin.sum_univ_succ, admission_power_capP_08] <;> ring
theorem admission01_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
  rw [admission01_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_08_coefficients]

def admission01_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1697948962814134868320997/3750000000000000000000:ℝ), (12523140750007104943515463/11250000000000000000000:ℝ), (1223022612966039855065849/1406250000000000000000:ℝ), (3276488938074470141631/15625000000000000000:ℝ)],
![(144103732217233066401059/937500000000000000000:ℝ), (876606252402011853703921/2812500000000000000000:ℝ), (55362507250039081812593/351562500000000000000:ℝ), (0:ℝ)]]
theorem admission01_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (5731519164381813371007/64000000000000000000000:ℝ) admission01_09_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_09_coefficients, Fin.sum_univ_succ, admission_power_capP_09] <;> ring
theorem admission01_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
  rw [admission01_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_09_coefficients]

def admission01_10_coefficients : Fin 3 → Fin 3 → ℝ := ![![(1619706523/15000000:ℝ), (60940411/468750:ℝ), (6898887/312500:ℝ)],
![(1223679941/5625000:ℝ), (182804996/703125:ℝ), (3282222/78125:ℝ)],
![(228719989/2812500:ℝ), (18448/225:ℝ), (0:ℝ)]]
theorem admission01_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
    Record12518109.Bernstein.bsum 2 2 (26530011/1280000000:ℝ) admission01_10_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_10_coefficients, Fin.sum_univ_succ, admission_power_capP_10] <;> ring
theorem admission01_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
  rw [admission01_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_10_coefficients]

def admission01_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1463859497/9000000:ℝ), (1615459717/5625000:ℝ), (39380001/312500:ℝ)],
![(380059387/11250000:ℝ), (45259927/1406250:ℝ), (0:ℝ)]]
theorem admission01_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (457979971/480000000:ℝ) admission01_11_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_11_coefficients, Fin.sum_univ_succ, admission_power_capP_11] <;> ring
theorem admission01_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
  rw [admission01_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_11_coefficients]

def admission01_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission01_12_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_12_coefficients, Fin.sum_univ_succ, admission_power_capP_12] <;> ring
theorem admission01_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
  rw [admission01_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_12_coefficients]

def admission01_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (263461388040213633877/5000000000000000000000:ℝ) admission01_13_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_13_coefficients, Fin.sum_univ_succ, admission_power_capP_13] <;> ring
theorem admission01_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
  rw [admission01_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_13_coefficients]

def admission01_14_coefficients : Fin 2 → Fin 3 → ℝ := ![![(303091439/15000000:ℝ), (51573011/1875000:ℝ), (479997/62500:ℝ)],
![(48053033/3750000:ℝ), (5813297/468750:ℝ), (0:ℝ)]]
theorem admission01_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
    Record12518109.Bernstein.bsum 1 2 (3893309/32000000:ℝ) admission01_14_coefficients
      (9/32:ℝ) (3/8:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission01_14_coefficients, Fin.sum_univ_succ, admission_power_capP_14] <;> ring
theorem admission01_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
  rw [admission01_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission01_14_coefficients]

theorem admission01_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ)) (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .capP δ p j := by
  fin_cases j
  · exact admission01_00_pos hδ hp
  · exact admission01_01_pos hδ hp
  · exact admission01_02_pos hδ hp
  · exact admission01_03_pos hδ hp
  · exact admission01_04_pos hδ hp
  · exact admission01_05_pos hδ hp
  · exact admission01_06_pos hδ hp
  · exact admission01_07_pos hδ hp
  · exact admission01_08_pos hδ hp
  · exact admission01_09_pos hδ hp
  · exact admission01_10_pos hδ hp
  · exact admission01_11_pos hδ hp
  · exact admission01_12_pos hδ hp
  · exact admission01_13_pos hδ hp
  · exact admission01_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
