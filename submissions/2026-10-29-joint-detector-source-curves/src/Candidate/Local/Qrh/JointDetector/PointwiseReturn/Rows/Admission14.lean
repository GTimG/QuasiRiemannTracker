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

def admission14_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission14_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission14_00_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission14_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission14_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_00_coefficients]

def admission14_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission14_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission14_01_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission14_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission14_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_01_coefficients]

def admission14_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission14_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission14_02_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission14_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission14_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_02_coefficients]

def admission14_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1626323600510368/424191237967:ℝ), (2057881342027680/424191237967:ℝ), (446757741517312/424191237967:ℝ)],
![(1168339978608000/424191237967:ℝ), (164619996944000/60598748281:ℝ), (0:ℝ)]]
theorem admission14_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (22136892687085/27148239229888:ℝ) admission14_03_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission14_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission14_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_03_coefficients]

def admission14_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(26530021706586582279119777/42419123796700000000000:ℝ), (608:ℝ), (0:ℝ)],
![(9921314398008233975364903/10604780949175000000000:ℝ), (98957181908065406362117/82849851165429687500:ℝ), (45933277162190406362117/165699702330859375000:ℝ)]]
theorem admission14_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (2618196798244853162640669/21718591383910400000000000:ℝ) admission14_04_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission14_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission14_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_04_coefficients]

def admission14_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1034828960947530322783287/1696764951868000000000:ℝ), (96002862062342990737117/82849851165429687500:ℝ), (89544511382962386362117/165699702330859375000:ℝ)],
![(63523871345086406362117/2120956189835000000000:ℝ), (11776691682328/302993741405:ℝ), (0:ℝ)]]
theorem admission14_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (83480547813530440913649/1085929569195520000000000:ℝ) admission14_05_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission14_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission14_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_05_coefficients]

def admission14_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(180643578011298272721580544399056153999/4161071022259445515527683125000000:ℝ), (251080765378928125803423057001738943581/2972193587328175368234059375000000:ℝ), (13361899293269587062750916828388934923/325083673614019180900600244140625:ℝ), (0:ℝ)],
![(54770109633552184365792208134758334937/1040267755564861378881920781250000:ℝ), (115080442745482354441847729676652938137/1040267755564861378881920781250000:ℝ), (4277131356437408258851990398261041272/65016734722803836180120048828125:ℝ), (505057618608719816598520301892628572/65016734722803836180120048828125:ℝ)]]
theorem admission14_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (308613611656722367624440204995491763/1842567233208074468281231360000000000:ℝ) admission14_06_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission14_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission14_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_06_coefficients]

def admission14_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8965922912977186993535866220596542557/3598764127359520445861780000000000:ℝ), (930845903849640301720725456501009481/281153447449962534832951562500000:ℝ), (12135169357360412102178483120896139/14057672372498126741647578125000:ℝ)],
![(39324292332167258358242782158705577/25705458052568003184727000000000:ℝ), (2989524359431032333111316319900429/2008238910356875248806796875000:ℝ), (0:ℝ)]]
theorem admission14_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (4045056452453470700726161040298713/13161194522914817630580224000000000:ℝ) admission14_07_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission14_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission14_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_07_coefficients]

def admission14_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1923228629301278188276348618746234069903652910591/449845515919940055732722500000000000000000000:ℝ), (737285642166964253684363946016201831639016598419/89969103183988011146544500000000000000000000:ℝ), (55254135780961189829389439581746237134107190047/14057672372498126741647578125000000000000000:ℝ), (0:ℝ)],
![(51700597928794311507262946647180533564837123953/4498455159199400557327225000000000000000000:ℝ), (92294142943321771278838123863607862267327221187/3213182256571000398090875000000000000000000:ℝ), (16437251816871053576956987153371154185392532539/702883618624906337082378906250000000000000:ℝ), (2159006688301027626233031818742485404460251761/351441809312453168541189453125000000000000:ℝ)]]
theorem admission14_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (3733756692476662006390302763789815323042957711/210579112366637082089283584000000000000000000000:ℝ) admission14_08_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission14_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission14_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_08_coefficients]

def admission14_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(12805495674675458558402365659373275817/719752825471904089172356000000000:ℝ), (9965166531713687916750941857968103063/224922757959970027866361250000000:ℝ), (2487614996738055182468470398393348631/70288361862490633708237890625000:ℝ), (15610707101109463647033549587527722/1757209046562265842705947265625:ℝ)],
![(1367845185422199164162601786634073887/179938206367976022293089000000000:ℝ), (848530786412800637589041835690809473/56230689489992506966590312500000:ℝ), (26296861478979260447761146253919837/3514418093124531685411894531250:ℝ), (0:ℝ)]]
theorem admission14_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (8140532548842383643059259348349601/184256723320807446828123136000000000:ℝ) admission14_09_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission14_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission14_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_09_coefficients]

def admission14_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21798615338829766156939117/113622653026875000000:ℝ), (5523636213911498280258128309/11930378567821875000000:ℝ), (66011913078568901916707524/186412165122216796875:ℝ), (15476065370219326388902508/186412165122216796875:ℝ)],
![(17576294009742685346328691/59651892839109375000:ℝ), (66674380555604368929682453/99419821398515625000:ℝ), (274738130576702619218464/591784651181640625:ℝ), (3293999524069805003587744/37282433024443359375:ℝ)],
![(2880148420085321155465181/29825946419554687500:ℝ), (5663490732847225155465181/29825946419554687500:ℝ), (356095016033523712/3817721141703:ℝ), (0:ℝ)]]
theorem admission14_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (6086870325437406362117/992849891835904000000000:ℝ) admission14_10_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission14_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission14_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_10_coefficients]

def admission14_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(41964188429404777061218389833437044559/17993820636797602229308900000000000:ℝ), (1741416036790671119313153739666104547/562306894899925069665903125000000:ℝ), (56765496756984165406277003120896139/70288361862490633708237890625000:ℝ)],
![(183638575992149553873381562364091187/128527290262840015923635000000000:ℝ), (5577480880540565469339473564960391/4016477820713750497613593750000:ℝ), (0:ℝ)]]
theorem admission14_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (728560790381385967001824994243041/2632238904582963526116044800000000:ℝ) admission14_11_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission14_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission14_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_11_coefficients]

def admission14_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission14_12_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission14_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission14_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_12_coefficients]

def admission14_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission14_13_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission14_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission14_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_13_coefficients]

def admission14_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission14_14_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission14_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission14_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_14_coefficients]

theorem admission14_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission14_00_pos hδ hp
  · exact admission14_01_pos hδ hp
  · exact admission14_02_pos hδ hp
  · exact admission14_03_pos hδ hp
  · exact admission14_04_pos hδ hp
  · exact admission14_05_pos hδ hp
  · exact admission14_06_pos hδ hp
  · exact admission14_07_pos hδ hp
  · exact admission14_08_pos hδ hp
  · exact admission14_09_pos hδ hp
  · exact admission14_10_pos hδ hp
  · exact admission14_11_pos hδ hp
  · exact admission14_12_pos hδ hp
  · exact admission14_13_pos hδ hp
  · exact admission14_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
