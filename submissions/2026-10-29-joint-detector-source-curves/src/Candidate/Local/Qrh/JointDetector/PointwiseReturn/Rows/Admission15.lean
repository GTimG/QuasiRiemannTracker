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

def admission15_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission15_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission15_00_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission15_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission15_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_00_coefficients]

def admission15_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission15_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission15_01_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission15_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission15_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_01_coefficients]

def admission15_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission15_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission15_02_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission15_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission15_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_02_coefficients]

def admission15_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(407774430031328/424191237967:ℝ), (511463865410656/424191237967:ℝ), (111689435379328/424191237967:ℝ)],
![(290872054459472/424191237967:ℝ), (282072054459472/424191237967:ℝ), (0:ℝ)]]
theorem admission15_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (41656064232467/54296478459776:ℝ) admission15_03_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission15_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission15_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_03_coefficients]

def admission15_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(717610951178409593637883/4241912379670000000000:ℝ), (160:ℝ), (0:ℝ)],
![(10833450201342691537192201/42419123796700000000000:ℝ), (104259572382652906362117/331399404661718750000:ℝ), (45933277162190406362117/662798809323437500000:ℝ)]]
theorem admission15_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (137799831486571219086351/1085929569195520000000000:ℝ) admission15_04_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission15_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission15_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_04_coefficients]

def admission15_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(939818722157039577259053/6059874828100000000000:ℝ), (6561768654970632977192201/21209561898350000000000:ℝ), (6355676550529892977192201/42419123796700000000000:ℝ)],
![(0:ℝ), (416435248381802890016713/21209561898350000000000:ℝ), (624827822020300250016713/42419123796700000000000:ℝ)]]
theorem admission15_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (4908645849867114750451251/99284989183590400000000000:ℝ) admission15_05_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission15_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission15_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_05_coefficients]

def admission15_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3519480917750217403966349623401576191/594438717465635073646811875000000:ℝ), (1332752601213823494291882380127893651/118887743493127014729362375000000:ℝ), (98641375021830314609158196163684127/18576209920801096051462871093750:ℝ), (0:ℝ)],
![(43292057481590086794420237368415204773/5944387174656350736468118750000000:ℝ), (17662864481638974753777675702663954881/1188877434931270147293623750000000:ℝ), (11140721600880177629661206630179446037/1300334694456076723602400976562500:ℝ), (126264404652179954149630075473157143/130033469445607672360240097656250:ℝ)]]
theorem admission15_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (84267834608966196175379841508947619/486964197347848252331468288000000000:ℝ) admission15_06_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission15_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission15_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_06_coefficients]

def admission15_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1095022194548835987191273979765675547/1799382063679760222930890000000000:ℝ), (45197009230738050536136180481095281/56230689489992506966590312500000:ℝ), (12135169357360412102178483120896139/56230689489992506966590312500000:ℝ)],
![(6158357611701638685030759101959563577/17993820636797602229308900000000000:ℝ), (182360985925292972319790295513926169/562306894899925069665903125000000:ℝ), (0:ℝ)]]
theorem admission15_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (246748443599661712744295823458221493/921283616604037234140615680000000000:ℝ) admission15_07_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission15_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission15_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_07_coefficients]

def admission15_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(64854793728994689312617375680729233800633155493/89969103183988011146544500000000000000000000:ℝ), (120066942463378684489243278137378101938729507061/89969103183988011146544500000000000000000000:ℝ), (3483211687064887819558796240916241758631021973/5623068948999250696659031250000000000000000:ℝ), (0:ℝ)],
![(1592430731863055374371982911700073567688337358471/899691031839880111465445000000000000000000000:ℝ), (3756358828826283861979651226648999476540073991799/899691031839880111465445000000000000000000000:ℝ), (178782616129047102331356356770290139892438574803/56230689489992506966590312500000000000000000:ℝ), (2159006688301027626233031818742485404460251761/2811534474499625348329515625000000000000000:ℝ)]]
theorem admission15_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (1630665845611985846171560740137808173734072963/73702689328322978731249254400000000000000000000:ℝ) admission15_08_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission15_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission15_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_08_coefficients]

def admission15_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(746429855881054947115536391019662327/359876412735952044586178000000000:ℝ), (1177094943602386725482473875829422737/224922757959970027866361250000000:ℝ), (17137300583662291761423206254155167/4016477820713750497613593750000:ℝ), (7805353550554731823516774793763861/7028836186249063370823789062500:ℝ)],
![(11244682903163649631123942518131779601/17993820636797602229308900000000000:ℝ), (2809437371714417448486721953295825211/2249227579599700278663612500000000:ℝ), (24939385680636895515484277103939017/40164778207137504976135937500000:ℝ), (0:ℝ)]]
theorem admission15_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (57989264836759640960042269102204427/1842567233208074468281231360000000000:ℝ) admission15_09_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission15_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission15_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_09_coefficients]

def admission15_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74110780833826073438651813/5965189283910937500000:ℝ), (182784633225783562542696389/5965189283910937500000:ℝ), (9095129789573395853504179/372824330244433593750:ℝ), (2307232765076052784501393/372824330244433593750:ℝ)],
![(105072746599073078873236771/5965189283910937500000:ℝ), (27458167050803350778841227/662798809323437500000:ℝ), (1904101146873882470880223/62137388374072265625:ℝ), (1277857913804238720880223/186412165122216796875:ℝ)],
![(102373616864056067331019493/23860757135643750000000:ℝ), (198914923590578395331019493/23860757135643750000000:ℝ), (384858426906089312/95443028542575:ℝ), (0:ℝ)]]
theorem admission15_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (1953576462730131668980507/694994924285132800000000000:ℝ) admission15_10_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission15_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission15_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_10_coefficients]

def admission15_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5120456762846011015739113586234049033/8996910318398801114654450000000000:ℝ), (422273817846856453051989587257198241/562306894899925069665903125000000:ℝ), (56765496756984165406277003120896139/281153447449962534832951562500000:ℝ)],
![(5722233358981067184221566919412863703/17993820636797602229308900000000000:ℝ), (338102896234594275748567758909915787/1124613789799850139331806250000000:ℝ), (0:ℝ)]]
theorem admission15_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (1104684892896472946034362730562633333/4606418083020186170703078400000000000:ℝ) admission15_11_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission15_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission15_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_11_coefficients]

def admission15_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission15_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission15_12_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission15_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission15_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_12_coefficients]

def admission15_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission15_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission15_13_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission15_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission15_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_13_coefficients]

def admission15_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission15_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission15_14_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission15_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission15_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission15_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission15_14_coefficients]

theorem admission15_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission15_00_pos hδ hp
  · exact admission15_01_pos hδ hp
  · exact admission15_02_pos hδ hp
  · exact admission15_03_pos hδ hp
  · exact admission15_04_pos hδ hp
  · exact admission15_05_pos hδ hp
  · exact admission15_06_pos hδ hp
  · exact admission15_07_pos hδ hp
  · exact admission15_08_pos hδ hp
  · exact admission15_09_pos hδ hp
  · exact admission15_10_pos hδ hp
  · exact admission15_11_pos hδ hp
  · exact admission15_12_pos hδ hp
  · exact admission15_13_pos hδ hp
  · exact admission15_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
