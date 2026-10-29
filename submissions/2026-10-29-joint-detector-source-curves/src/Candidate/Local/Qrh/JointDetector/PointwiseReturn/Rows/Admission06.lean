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

def admission06_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission06_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission06_00_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission06_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission06_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_00_coefficients]

def admission06_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission06_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission06_01_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission06_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission06_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_01_coefficients]

def admission06_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission06_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission06_02_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission06_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission06_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_02_coefficients]

def admission06_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(412987370223856/424191237967:ℝ), (73925257943312/60598748281:ℝ), (111689435379328/424191237967:ℝ)],
![(296084994652000/424191237967:ℝ), (41154999236000/60598748281:ℝ), (0:ℝ)]]
theorem admission06_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (22136892687085/27148239229888:ℝ) admission06_03_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission06_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission06_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_03_coefficients]

def admission06_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6458498560605686342740947/42419123796700000000000:ℝ), (144:ℝ), (0:ℝ)],
![(5057919625082140971777159/21209561898350000000000:ℝ), (98957181908065406362117/331399404661718750000:ℝ), (45933277162190406362117/662798809323437500000:ℝ)]]
theorem admission06_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (1240198483379140971777159/10859295691955200000000000:ℝ) admission06_04_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission06_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission06_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_04_coefficients]

def admission06_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6801785559668661104434541/42419123796700000000000:ℝ), (99241023609837032612117/331399404661718750000:ℝ), (89544511382962386362117/662798809323437500000:ℝ)],
![(22305450456938406362117/4241912379670000000000:ℝ), (2944172920582/302993741405:ℝ), (0:ℝ)]]
theorem admission06_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (83480547813530440913649/1085929569195520000000000:ℝ) admission06_05_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission06_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission06_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_05_coefficients]

def admission06_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(230087535602597414322228909848724519089/41610710222594455155276831250000000:ℝ), (87188078491681017121148777790103598429/8322142044518891031055366250000000:ℝ), (174513595722742298381347110727866109/35144180931245316854118945312500:ℝ), (0:ℝ)],
![(28676827373121280360552609778952061913/4161071022259445515527683125000000:ℝ), (58767723889093097898580370549899363513/4161071022259445515527683125000000:ℝ), (534641419554676032356498799782630159/65016734722803836180120048828125:ℝ), (126264404652179954149630075473157143/130033469445607672360240097656250:ℝ)]]
theorem admission06_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (5519955208671093869827698679206861901/34087493814349377663202780160000000000:ℝ) admission06_06_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission06_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission06_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_06_coefficients]

def admission06_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1694118869274249883728229413523883269/2570545805256800318472700000000000:ℝ), (9772975745760404007333952075307279/11475650916325001421753125000000:ℝ), (12135169357360412102178483120896139/56230689489992506966590312500000:ℝ)],
![(100956682159043257131651788556714157/257054580525680031847270000000000:ℝ), (2989524359431032333111316319900429/8032955641427500995227187500000:ℝ), (0:ℝ)]]
theorem admission06_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (4045056452453470700726161040298713/13161194522914817630580224000000000:ℝ) admission06_07_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission06_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission06_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_07_coefficients]

def admission06_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(395547282973167252274934783912106437751606314909/899691031839880111465445000000000000000000000:ℝ), (717626441210276348988924882091348550516357839981/899691031839880111465445000000000000000000000:ℝ), (20422018910312311633801477172583819547796970317/56230689489992506966590312500000000000000000:ℝ), (0:ℝ)],
![(26788601550925514670414878776097753348672242369/17993820636797602229308900000000000000000000:ℝ), (327331584540277336607614332736656700766913676117/89969103183988011146544500000000000000000000:ℝ), (16437251816871053576956987153371154185392532539/5623068948999250696659031250000000000000000:ℝ), (2159006688301027626233031818742485404460251761/2811534474499625348329515625000000000000000:ℝ)]]
theorem admission06_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (9829638391216775583016511945150625523959974347/737026893283229787312492544000000000000000000000:ℝ) admission06_08_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission06_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission06_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_08_coefficients]

def admission06_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(43416597595521731612226753111798968939/17993820636797602229308900000000000:ℝ), (13239322091800774510586651761279322969/2249227579599700278663612500000000:ℝ), (1288003955881694759168845960602486941/281153447449962534832951562500000:ℝ), (7805353550554731823516774793763861/7028836186249063370823789062500:ℝ)],
![(1733978770463263388757387607894763219/1799382063679760222930890000000000:ℝ), (427781002749132470424863495628092081/224922757959970027866361250000000:ℝ), (26296861478979260447761146253919837/28115344744996253483295156250000:ℝ), (0:ℝ)]]
theorem admission06_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (8140532548842383643059259348349601/184256723320807446828123136000000000:ℝ) admission06_09_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission06_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission06_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_09_coefficients]

def admission06_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(42843034349688747593637883/3408679590806250000000:ℝ), (234497445550224001771108639/7953585711881250000000:ℝ), (2704320110226915594983287/124274776748144531250:ℝ), (1810266640011203469983287/372824330244433593750:ℝ)],
![(3358255092965643593637883/170433979540312500000:ℝ), (52504136799720605169816157/1193037856782187500000:ℝ), (158750224094199598310386/5326061860634765625:ℝ), (205874970254362812724234/37282433024443359375:ℝ)],
![(212543180529195593637883/34086795908062500000:ℝ), (2881498420085321155465181/238607571356437500000:ℝ), (22255938502095232/3817721141703:ℝ), (0:ℝ)]]
theorem admission06_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (6086870325437406362117/992849891835904000000000:ℝ) admission06_10_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission06_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission06_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_10_coefficients]

def admission06_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1589514557136570041819022746540854219/2570545805256800318472700000000000:ℝ), (25624811459913091805976416147191659/32131822565710003980908750000000:ℝ), (56765496756984165406277003120896139/281153447449962534832951562500000:ℝ)],
![(94398881903500506363949985324724931/257054580525680031847270000000000:ℝ), (5577480880540565469339473564960391/16065911282855001990454375000000:ℝ), (0:ℝ)]]
theorem admission06_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (728560790381385967001824994243041/2632238904582963526116044800000000:ℝ) admission06_11_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission06_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission06_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_11_coefficients]

def admission06_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission06_12_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission06_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission06_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_12_coefficients]

def admission06_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission06_13_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission06_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission06_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_13_coefficients]

def admission06_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission06_14_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission06_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission06_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_14_coefficients]

theorem admission06_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission06_00_pos hδ hp
  · exact admission06_01_pos hδ hp
  · exact admission06_02_pos hδ hp
  · exact admission06_03_pos hδ hp
  · exact admission06_04_pos hδ hp
  · exact admission06_05_pos hδ hp
  · exact admission06_06_pos hδ hp
  · exact admission06_07_pos hδ hp
  · exact admission06_08_pos hδ hp
  · exact admission06_09_pos hδ hp
  · exact admission06_10_pos hδ hp
  · exact admission06_11_pos hδ hp
  · exact admission06_12_pos hδ hp
  · exact admission06_13_pos hδ hp
  · exact admission06_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
