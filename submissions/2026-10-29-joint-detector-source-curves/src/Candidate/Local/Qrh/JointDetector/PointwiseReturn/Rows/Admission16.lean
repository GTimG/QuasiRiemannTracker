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

def admission16_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1:ℝ), (0:ℝ)]]
theorem admission16_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (5/2:ℝ) admission16_00_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_00_coefficients, Fin.sum_univ_succ, admission_power_capP_00] <;> ring
theorem admission16_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
  rw [admission16_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_00_coefficients]

def admission16_01_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
    Record12518109.Bernstein.bsum 0 0 (2:ℝ) admission16_01_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_01_coefficients, Fin.sum_univ_succ, admission_power_capP_01] <;> ring
theorem admission16_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
  rw [admission16_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_01_coefficients]

def admission16_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(619999/5000000:ℝ), (0:ℝ)]]
theorem admission16_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (9380001/10000000:ℝ) admission16_02_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_02_coefficients, Fin.sum_univ_succ, admission_power_capP_02] <;> ring
theorem admission16_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
  rw [admission16_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_02_coefficients]

def admission16_03_coefficients : Fin 2 → Fin 2 → ℝ := ![![(950/9:ℝ), (48:ℝ)],
![(527/9:ℝ), (0:ℝ)]]
theorem admission16_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
    Record12518109.Bernstein.bsum 1 1 (979/768:ℝ) admission16_03_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_03_coefficients, Fin.sum_univ_succ, admission_power_capP_03] <;> ring
theorem admission16_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
  rw [admission16_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_03_coefficients]

def admission16_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1766819989/2500000:ℝ), (704:ℝ), (0:ℝ)],
![(6095540233/5000000:ℝ), (132540008/78125:ℝ), (37520004/78125:ℝ)]]
theorem admission16_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (309540033/1280000000:ℝ) admission16_04_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_04_coefficients, Fin.sum_univ_succ, admission_power_capP_04] <;> ring
theorem admission16_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
  rw [admission16_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_04_coefficients]

def admission16_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(888229651/1000000:ℝ), (15192412699/7500000:ℝ), (17020460699/15000000:ℝ)],
![(0:ℝ), (2050851931/7500000:ℝ), (4058923931/15000000:ℝ)]]
theorem admission16_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (7804506081/131072000000:ℝ) admission16_05_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_05_coefficients, Fin.sum_univ_succ, admission_power_capP_05] <;> ring
theorem admission16_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
  rw [admission16_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_05_coefficients]

def admission16_06_coefficients : Fin 2 → Fin 3 → ℝ := ![![(315962609341/166500000:ℝ), (48846324514/26015625:ℝ), (0:ℝ)],
![(26086743773/9000000:ℝ), (99541897501/26015625:ℝ), (548240148/578125:ℝ)]]
theorem admission16_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
    Record12518109.Bernstein.bsum 1 2 (14039337743/28416000000:ℝ) admission16_06_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_06_coefficients, Fin.sum_univ_succ, admission_power_capP_06] <;> ring
theorem admission16_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
  rw [admission16_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_06_coefficients]

def admission16_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4416473453/1500000:ℝ), (3757440238/703125:ℝ), (37520004/15625:ℝ)],
![(1508926177/3000000:ℝ), (352559887/703125:ℝ), (0:ℝ)]]
theorem admission16_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (353313371/512000000:ℝ) admission16_07_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_07_coefficients, Fin.sum_univ_succ, admission_power_capP_07] <;> ring
theorem admission16_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
  rw [admission16_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_07_coefficients]

def admission16_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(55271628671/7500000:ℝ), (2032307914/140625:ℝ), (4981742504/703125:ℝ), (0:ℝ)],
![(250156605403/15000000:ℝ), (5758063969/140625:ℝ), (22624640036/703125:ℝ), (123520128/15625:ℝ)]]
theorem admission16_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (29444953/256000000:ℝ) admission16_08_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_08_coefficients, Fin.sum_univ_succ, admission_power_capP_08] <;> ring
theorem admission16_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
  rw [admission16_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_08_coefficients]

def admission16_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2393033854591740327722471/156250000000000000000:ℝ), (12446944114386302265180979/281250000000000000000:ℝ), (1861442372503196762256163/43945312500000000000:ℝ), (3276488938074470141631/244140625000000000:ℝ)],
![(168764366829478045715203/312500000000000000000:ℝ), (147291856677354249386419/112500000000000000000:ℝ), (67356121200189181975739/87890625000000000000:ℝ), (0:ℝ)]]
theorem admission16_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (22898038930545140961861/1024000000000000000000000:ℝ) admission16_09_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_09_coefficients, Fin.sum_univ_succ, admission_power_capP_09] <;> ring
theorem admission16_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
  rw [admission16_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_09_coefficients]

def admission16_10_coefficients : Fin 3 → Fin 3 → ℝ := ![![(109398924769/11250000:ℝ), (2334210136/140625:ℝ), (106804452/15625:ℝ)],
![(15431116077/1250000:ℝ), (1529934528/78125:ℝ), (558942264/78125:ℝ)],
![(102100677401/45000000:ℝ), (520628/225:ℝ), (0:ℝ)]]
theorem admission16_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
    Record12518109.Bernstein.bsum 2 2 (735772599/327680000000:ℝ) admission16_10_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_10_coefficients, Fin.sum_univ_succ, admission_power_capP_10] <;> ring
theorem admission16_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
  rw [admission16_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_10_coefficients]

def admission16_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(55505844797/22500000:ℝ), (3147219569/703125:ℝ), (157520004/78125:ℝ)],
![(3950013629/9000000:ℝ), (606979021/1406250:ℝ), (0:ℝ)]]
theorem admission16_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (4846739473/7680000000:ℝ) admission16_11_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_11_coefficients, Fin.sum_univ_succ, admission_power_capP_11] <;> ring
theorem admission16_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
  rw [admission16_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_11_coefficients]

def admission16_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission16_12_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_12_coefficients, Fin.sum_univ_succ, admission_power_capP_12] <;> ring
theorem admission16_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
  rw [admission16_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_12_coefficients]

def admission16_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (263461388040213633877/5000000000000000000000:ℝ) admission16_13_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_13_coefficients, Fin.sum_univ_succ, admission_power_capP_13] <;> ring
theorem admission16_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
  rw [admission16_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_13_coefficients]

def admission16_14_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2469691231/7500000:ℝ), (105546007/234375:ℝ), (1919988/15625:ℝ)],
![(3112033883/15000000:ℝ), (96372731/468750:ℝ), (0:ℝ)]]
theorem admission16_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
    Record12518109.Bernstein.bsum 1 2 (52213007/512000000:ℝ) admission16_14_coefficients
      (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_14_coefficients, Fin.sum_univ_succ, admission_power_capP_14] <;> ring
theorem admission16_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
  rw [admission16_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_14_coefficients]

theorem admission16_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ)) (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .capP δ p j := by
  fin_cases j
  · exact admission16_00_pos hδ hp
  · exact admission16_01_pos hδ hp
  · exact admission16_02_pos hδ hp
  · exact admission16_03_pos hδ hp
  · exact admission16_04_pos hδ hp
  · exact admission16_05_pos hδ hp
  · exact admission16_06_pos hδ hp
  · exact admission16_07_pos hδ hp
  · exact admission16_08_pos hδ hp
  · exact admission16_09_pos hδ hp
  · exact admission16_10_pos hδ hp
  · exact admission16_11_pos hδ hp
  · exact admission16_12_pos hδ hp
  · exact admission16_13_pos hδ hp
  · exact admission16_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
