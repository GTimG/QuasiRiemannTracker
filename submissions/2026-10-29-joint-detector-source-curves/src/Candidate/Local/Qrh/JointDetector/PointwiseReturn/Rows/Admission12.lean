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

def admission12_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission12_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission12_00_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission12_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission12_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_00_coefficients]

def admission12_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission12_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission12_01_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission12_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission12_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_01_coefficients]

def admission12_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission12_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission12_02_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission12_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission12_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_02_coefficients]

def admission12_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(103424324518824448/424191237967:ℝ), (131896819975932416/424191237967:ℝ), (28592495457107968/424191237967:ℝ)],
![(74736422018636032/424191237967:ℝ), (74615622018636032/424191237967:ℝ), (0:ℝ)]]
theorem admission12_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (731940056262047/868743655356416:ℝ) admission12_03_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission12_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission12_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_03_coefficients]

def admission12_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(32694601987159228780913649/848382475934000000000:ℝ), (38400:ℝ), (0:ℝ)],
![(342599873292239352353749323/6059874828100000000000:ℝ), (1535593396257759001793872/20712462791357421875:ℝ), (367466217297523250896936/20712462791357421875:ℝ)]]
theorem admission12_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (413399494459713657259053/3474974621425664000000000:ℝ) admission12_04_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission12_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission12_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_04_coefficients]

def admission12_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(121601041670913509593660177/3029937414050000000000:ℝ), (1548998439187464019293872/20712462791357421875:ℝ), (716356091063699090896936/20712462791357421875:ℝ)],
![(222034886225366591040679667/42419123796700000000000:ℝ), (200795307821856464/37874217675625:ℝ), (0:ℝ)]]
theorem admission12_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (15774589457504854977960999/173748731071283200000000000:ℝ) admission12_05_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission12_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission12_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_05_coefficients]

def admission12_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5464672251374235141437169515218364815271/260066938891215344720480195312500:ℝ), (62238637712373215674021411606576707721/1486096793664087684117029687500:ℝ), (1356792421460267296472894378983139758976/65016734722803836180120048828125:ℝ), (0:ℝ)],
![(65221487074636454829504797203306951692911/2600669388912153447204801953125000:ℝ), (28081771316666899360395390802606470380771/520133877782430689440960390625000:ℝ), (10691469783642650720723106574060804170688/325083673614019180900600244140625:ℝ), (258589500727664546098442394569025828864/65016734722803836180120048828125:ℝ)]]
theorem admission12_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (9059204262247674109193652022582661899/54539990102959004261124448256000000000:ℝ) admission12_06_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission12_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission12_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_06_coefficients]

def admission12_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(57051728142499017592216250400312100001/359876412735952044586178000000000:ℝ), (750057866926688099576180734576628357/3514418093124531685411894531250:ℝ), (97081354858883296817427864967169112/1757209046562265842705947265625:ℝ)],
![(1844649977997812471207125430152813012477/17993820636797602229308900000000000:ℝ), (3590418755676669832066690900200415229/35144180931245316854118945312500:ℝ), (0:ℝ)]]
theorem admission12_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (4858112799396618311572119409398754313/14740537865664595746249850880000000000:ℝ) admission12_07_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission12_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission12_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_07_coefficients]

def admission12_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10694483625183203813198232745426456976955349765067/5623068948999250696659031250000000000000000:ℝ), (21272246831687334960478426767594626809948623916747/5623068948999250696659031250000000000000000:ℝ), (8264257806540327710230850923616254019916620431/4393022616405664606764868164062500000000:ℝ), (0:ℝ)],
![(287521601536382288566856994315262388219935227010931/56230689489992506966590312500000000000000000:ℝ), (750719842038118961473375188262939640626995008899699/56230689489992506966590312500000000000000000:ℝ), (2500269409056339473257039577410177287316185961523/219651130820283230338243408203125000000000:ℝ), (2159006688301027626233031818742485404460251761/686409783813385094807010650634765625000:ℝ)]]
theorem admission12_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (156909067719109525280367011087819796530915297/9433944234025341277599904563200000000000000000:ℝ) admission12_08_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission12_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission12_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_08_coefficients]

def admission12_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(16547544274848558932640619278787548702629/1799382063679760222930890000000000:ℝ), (322331485243556716805323953354417451151/14057672372498126741647578125000:ℝ), (6424865857265635242075585994486412656/351441809312453168541189453125:ℝ), (7992682035768045387281177388814193664/1757209046562265842705947265625:ℝ)],
![(82175220902361292269182266904011712968061/17993820636797602229308900000000000:ℝ), (1282388491589379127241381881750992876311/140576723724981267416475781250000:ℝ), (40024272574917525555718216847454409432/8786045232811329213529736328125:ℝ), (0:ℝ)]]
theorem admission12_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (1513229753679759142124434415167560407/29481075731329191492499701760000000000:ℝ) admission12_09_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission12_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission12_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_09_coefficients]

def admission12_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(280847112037665887481744394693/372824330244433593750:ℝ), (32215776969928233539171204849/17753539535449218750:ℝ), (28403751653302934070070908928/20712462791357421875:ℝ), (57792137323687898210212726784/186412165122216796875:ℝ)],
![(445116370077979570933419091001/372824330244433593750:ℝ), (1005350672574371067526536160313/372824330244433593750:ℝ), (338417226337075052204837801984/186412165122216796875:ℝ), (58301030635754303908279267328/186412165122216796875:ℝ)],
![(93274695596966678052260531419/213042474425390625000:ℝ), (1302898358150566163453823719933/1491297320977734375000:ℝ), (41598185043395162693632/95443028542575:ℝ), (0:ℝ)]]
theorem admission12_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (1367099991419539273176280067/177918700616993996800000000000:ℝ) admission12_10_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission12_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission12_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_10_coefficients]

def admission12_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1334713113999040775483767577510266989383/8996910318398801114654450000000000:ℝ), (7017984912565929784357810349301729771/35144180931245316854118945312500:ℝ), (454123974055873323250216024967169112/8786045232811329213529736328125:ℝ)],
![(1725937657060610142984590910081498976003/17993820636797602229308900000000000:ℝ), (6717665474834641089606968908491442167/70288361862490633708237890625000:ℝ), (0:ℝ)]]
theorem admission12_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (21932370543117379542020578923069343753/73702689328322978731249254400000000000:ℝ) admission12_11_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission12_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission12_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_11_coefficients]

def admission12_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission12_12_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission12_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission12_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_12_coefficients]

def admission12_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission12_13_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission12_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission12_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_13_coefficients]

def admission12_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission12_14_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission12_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission12_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_14_coefficients]

theorem admission12_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ)) (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission12_00_pos hδ hp
  · exact admission12_01_pos hδ hp
  · exact admission12_02_pos hδ hp
  · exact admission12_03_pos hδ hp
  · exact admission12_04_pos hδ hp
  · exact admission12_05_pos hδ hp
  · exact admission12_06_pos hδ hp
  · exact admission12_07_pos hδ hp
  · exact admission12_08_pos hδ hp
  · exact admission12_09_pos hδ hp
  · exact admission12_10_pos hδ hp
  · exact admission12_11_pos hδ hp
  · exact admission12_12_pos hδ hp
  · exact admission12_13_pos hδ hp
  · exact admission12_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
