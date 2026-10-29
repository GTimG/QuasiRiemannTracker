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

def admission02_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1:ℝ), (0:ℝ)]]
theorem admission02_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (5/2:ℝ) admission02_00_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_00_coefficients, Fin.sum_univ_succ, admission_power_capP_00] <;> ring
theorem admission02_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
  rw [admission02_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_00_coefficients]

def admission02_01_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
    Record12518109.Bernstein.bsum 0 0 (2:ℝ) admission02_01_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_01_coefficients, Fin.sum_univ_succ, admission_power_capP_01] <;> ring
theorem admission02_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
  rw [admission02_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_01_coefficients]

def admission02_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(619999/5000000:ℝ), (0:ℝ)]]
theorem admission02_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (9380001/10000000:ℝ) admission02_02_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_02_coefficients, Fin.sum_univ_succ, admission_power_capP_02] <;> ring
theorem admission02_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
  rw [admission02_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_02_coefficients]

def admission02_03_coefficients : Fin 2 → Fin 2 → ℝ := ![![(430/9:ℝ), (24:ℝ)],
![(223/9:ℝ), (0:ℝ)]]
theorem admission02_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
    Record12518109.Bernstein.bsum 1 1 (611/384:ℝ) admission02_03_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_03_coefficients, Fin.sum_univ_succ, admission_power_capP_03] <;> ring
theorem admission02_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
  rw [admission02_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_03_coefficients]

def admission02_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(241859997/2500000:ℝ), (96:ℝ), (0:ℝ)],
![(1164660057/5000000:ℝ), (27510002/78125:ℝ), (9380001/78125:ℝ)]]
theorem admission02_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (84420009/640000000:ℝ) admission02_04_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_04_coefficients, Fin.sum_univ_succ, admission_power_capP_04] <;> ring
theorem admission02_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
  rw [admission02_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_04_coefficients]

def admission02_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1140756063/5000000:ℝ), (3440380171/7500000:ℝ), (3447332171/15000000:ℝ)],
![(0:ℝ), (109983979/7500000:ℝ), (206947979/15000000:ℝ)]]
theorem admission02_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (19759962677/81920000000:ℝ) admission02_05_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_05_coefficients, Fin.sum_univ_succ, admission_power_capP_05] <;> ring
theorem admission02_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
  rw [admission02_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_05_coefficients]

def admission02_06_coefficients : Fin 2 → Fin 3 → ℝ := ![![(288728004713/832500000:ℝ), (8826681961/26015625:ℝ), (0:ℝ)],
![(1016352084997/1665000000:ℝ), (43678130249/52031250:ℝ), (137060037/578125:ℝ)]]
theorem admission02_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
    Record12518109.Bernstein.bsum 1 2 (3935818039/14208000000:ℝ) admission02_06_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_06_coefficients, Fin.sum_univ_succ, admission_power_capP_06] <;> ring
theorem admission02_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
  rw [admission02_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_06_coefficients]

def admission02_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(18831579691/22500000:ℝ), (1009560037/703125:ℝ), (9380001/15625:ℝ)],
![(9744616799/45000000:ℝ), (302639903/1406250:ℝ), (0:ℝ)]]
theorem admission02_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (303286699/256000000:ℝ) admission02_07_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_07_coefficients, Fin.sum_univ_succ, admission_power_capP_07] <;> ring
theorem admission02_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
  rw [admission02_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_07_coefficients]

def admission02_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (6157848571/7500000:ℝ), (37125548561/22500000:ℝ), (149082103/180000:ℝ)],
![(1345293107/1000000:ℝ), (33649512907/7500000:ℝ), (111567859697/22500000:ℝ), (8173777183/4500000:ℝ)]]
theorem admission02_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (19266772193/393216000000:ℝ) admission02_08_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_08_coefficients, Fin.sum_univ_succ, admission_power_capP_08] <;> ring
theorem admission02_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
  rw [admission02_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_08_coefficients]

def admission02_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10161976217968486441541143/2812500000000000000000:ℝ), (2779365161246987457627343/312500000000000000000:ℝ), (1223022612966039855065849/175781250000000000000:ℝ), (3276488938074470141631/1953125000000000000:ℝ)],
![(8947467161249296852408187/5625000000000000000000:ℝ), (1989942190261302750846867/625000000000000000000:ℝ), (559820628686089244075851/351562500000000000000:ℝ), (0:ℝ)]]
theorem admission02_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (55681620129277917392949/512000000000000000000000:ℝ) admission02_09_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_09_coefficients, Fin.sum_univ_succ, admission_power_capP_09] <;> ring
theorem admission02_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
  rw [admission02_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_09_coefficients]

def admission02_10_coefficients : Fin 3 → Fin 3 → ℝ := ![![(979871017/1250000:ℝ), (206381638/234375:ℝ), (7567773/78125:ℝ)],
![(46998931/30000:ℝ), (1226184932/703125:ℝ), (13797774/78125:ℝ)],
![(10298493107/15000000:ℝ), (154714/225:ℝ), (0:ℝ)]]
theorem admission02_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
    Record12518109.Bernstein.bsum 2 2 (1878170679/81920000000:ℝ) admission02_10_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_10_coefficients, Fin.sum_univ_succ, admission_power_capP_10] <;> ring
theorem admission02_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
  rw [admission02_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_10_coefficients]

def admission02_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1619139453/2500000:ℝ), (1615459717/1406250:ℝ), (39380001/78125:ℝ)],
![(688818889/5000000:ℝ), (378819389/2812500:ℝ), (0:ℝ)]]
theorem admission02_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (4018259777/3840000000:ℝ) admission02_11_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_11_coefficients, Fin.sum_univ_succ, admission_power_capP_11] <;> ring
theorem admission02_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
  rw [admission02_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_11_coefficients]

def admission02_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission02_12_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_12_coefficients, Fin.sum_univ_succ, admission_power_capP_12] <;> ring
theorem admission02_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
  rw [admission02_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_12_coefficients]

def admission02_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (263461388040213633877/5000000000000000000000:ℝ) admission02_13_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_13_coefficients, Fin.sum_univ_succ, admission_power_capP_13] <;> ring
theorem admission02_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
  rw [admission02_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_13_coefficients]

def admission02_14_coefficients : Fin 2 → Fin 3 → ℝ := ![![(200158749/2500000:ℝ), (51573011/468750:ℝ), (479997/15625:ℝ)],
![(249438441/5000000:ℝ), (46026379/937500:ℝ), (0:ℝ)]]
theorem admission02_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
    Record12518109.Bernstein.bsum 1 2 (32586463/256000000:ℝ) admission02_14_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_capP_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission02_14_coefficients, Fin.sum_univ_succ, admission_power_capP_14] <;> ring
theorem admission02_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
  rw [admission02_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission02_14_coefficients]

theorem admission02_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .capP δ p j := by
  fin_cases j
  · exact admission02_00_pos hδ hp
  · exact admission02_01_pos hδ hp
  · exact admission02_02_pos hδ hp
  · exact admission02_03_pos hδ hp
  · exact admission02_04_pos hδ hp
  · exact admission02_05_pos hδ hp
  · exact admission02_06_pos hδ hp
  · exact admission02_07_pos hδ hp
  · exact admission02_08_pos hδ hp
  · exact admission02_09_pos hδ hp
  · exact admission02_10_pos hδ hp
  · exact admission02_11_pos hδ hp
  · exact admission02_12_pos hδ hp
  · exact admission02_13_pos hδ hp
  · exact admission02_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
