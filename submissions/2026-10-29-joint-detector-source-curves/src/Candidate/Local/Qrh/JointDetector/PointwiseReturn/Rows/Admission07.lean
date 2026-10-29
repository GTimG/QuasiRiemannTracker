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

def admission07_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission07_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission07_00_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission07_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission07_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_00_coefficients]

def admission07_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission07_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission07_01_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission07_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission07_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_01_coefficients]

def admission07_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission07_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission07_02_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission07_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission07_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_02_coefficients]

def admission07_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1637549480895424/424191237967:ℝ), (295701031773248/60598748281:ℝ), (446757741517312/424191237967:ℝ)],
![(1179565858993056/424191237967:ℝ), (1164365858993056/424191237967:ℝ), (0:ℝ)]]
theorem admission07_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (13023613127149/15513279559936:ℝ) admission07_03_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission07_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission07_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_03_coefficients]

def admission07_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(12566852387330486342740947/21209561898350000000000:ℝ), (576:ℝ), (0:ℝ)],
![(38288940660107326307821729/42419123796700000000000:ℝ), (96305986670771656362117/82849851165429687500:ℝ), (45933277162190406362117/165699702330859375000:ℝ)]]
theorem admission07_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (1240198483379140971777159/10859295691955200000000000:ℝ) admission07_04_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission07_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission07_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_04_coefficients]

def admission07_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13773787853218208551610029/21209561898350000000000:ℝ), (99241023609837032612117/82849851165429687500:ℝ), (89544511382962386362117/165699702330859375000:ℝ)],
![(2947329109649887160880223/42419123796700000000000:ℝ), (2952388882002562/37874217675625:ℝ), (0:ℝ)]]
theorem admission07_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (1938244490419495977359331/21718591383910400000000000:ℝ) admission07_05_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission07_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission07_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_05_coefficients]

def admission07_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(87265202539672938121148777790103598429/2080535511129722757763841562500000:ℝ), (121312655304265549738967692450586419751/1486096793664087684117029687500000:ℝ), (349027191445484596762694221455732218/8786045232811329213529736328125:ℝ), (0:ℝ)],
![(30423895086036620140555120531454911801/594438717465635073646811875000000:ℝ), (2242420671516867904558540888829096034187/20805355111297227577638415625000000:ℝ), (20937763572400384311728721356778363503/325083673614019180900600244140625:ℝ), (505057618608719816598520301892628572/65016734722803836180120048828125:ℝ)]]
theorem admission07_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (5519955208671093869827698679206861901/34087493814349377663202780160000000000:ℝ) admission07_06_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission07_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission07_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_06_coefficients]

def admission07_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(37279366175866769275040205040099571/14395056509438081783447120000000:ℝ), (9772975745760404007333952075307279/2868912729081250355438281250000:ℝ), (12135169357360412102178483120896139/14057672372498126741647578125000:ℝ)],
![(5859319557492921495378174541647130973/3598764127359520445861780000000000:ℝ), (445439129555223817633586131665163921/281153447449962534832951562500000:ℝ), (0:ℝ)]]
theorem admission07_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (602713411415567134408197995004508237/1842567233208074468281231360000000000:ℝ) admission07_07_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission07_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission07_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_07_coefficients]

def admission07_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(719963013374220293702341650382398050516357839981/224922757959970027866361250000000000000000000:ℝ), (10969048370722162570164577212912246208366887121/1799382063679760222930890000000000000000000:ℝ), (20422018910312311633801477172583819547796970317/7028836186249063370823789062500000000000000:ℝ), (0:ℝ)],
![(4686757190326593549854629346736615387612775164671/449845515919940055732722500000000000000000000:ℝ), (2395402778782153470631332382810430622264489950867/89969103183988011146544500000000000000000000:ℝ), (314334938377084504977353257830844485669337401367/14057672372498126741647578125000000000000000:ℝ), (2159006688301027626233031818742485404460251761/351441809312453168541189453125000000000000:ℝ)]]
theorem admission07_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (9829638391216775583016511945150625523959974347/737026893283229787312492544000000000000000000000:ℝ) admission07_08_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission07_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission07_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_08_coefficients]

def admission07_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(34363662447619210375823455652897252887/1799382063679760222930890000000000:ℝ), (5270849195475069621342416665781161493/112461378979985013933180625000000:ℝ), (1288003955881694759168845960602486941/35144180931245316854118945312500:ℝ), (15610707101109463647033549587527722/1757209046562265842705947265625:ℝ)],
![(32056750230305111242887118741609604429/3598764127359520445861780000000000:ℝ), (794131000977530775258011763271491563/44984551591994005573272250000000:ℝ), (614330144604919544824444447890021991/70288361862490633708237890625000:ℝ), (0:ℝ)]]
theorem admission07_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (26603815946930266904533644478326229/526447780916592705223208960000000000:ℝ) admission07_09_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission07_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission07_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_09_coefficients]

def admission07_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(571623005687879805169816157/2982594641955468750000:ℝ), (12825441105613628508155989/28405663256718750000:ℝ), (20640628631685626130830084/62137388374072265625:ℝ), (13488200869959929130830084/186412165122216796875:ℝ)],
![(43562181821093939748442499/142028316283593750000:ℝ), (2037702521702311879033013951/2982594641955468750000:ℝ), (84648748961298324279598888/186412165122216796875:ℝ), (14482133120089627759866296/186412165122216796875:ℝ)],
![(1298386426883088557588846773/11930378567821875000000:ℝ), (364604523261341087655549539/1704339795403125000000:ℝ), (1432409012510056064/13634718363225:ℝ), (0:ℝ)]]
theorem admission07_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (20912253253779569411153227/2779979697140531200000000000:ℝ) admission07_10_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission07_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission07_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_10_coefficients]

def admission07_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21843504525060335118078224068475955677/8996910318398801114654450000000000:ℝ), (25624811459913091805976416147191659/8032955641427500995227187500000:ℝ), (56765496756984165406277003120896139/70288361862490633708237890625000:ℝ)],
![(1097288850384673228688459081379505319/719752825471904089172356000000000:ℝ), (833168088678924472812721689731766323/562306894899925069665903125000000:ℝ), (0:ℝ)]]
theorem admission07_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (2720259256605803380725218489213331917/9212836166040372341406156800000000000:ℝ) admission07_11_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission07_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission07_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_11_coefficients]

def admission07_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission07_12_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission07_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission07_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_12_coefficients]

def admission07_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission07_13_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission07_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission07_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_13_coefficients]

def admission07_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission07_14_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission07_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission07_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_14_coefficients]

theorem admission07_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission07_00_pos hδ hp
  · exact admission07_01_pos hδ hp
  · exact admission07_02_pos hδ hp
  · exact admission07_03_pos hδ hp
  · exact admission07_04_pos hδ hp
  · exact admission07_05_pos hδ hp
  · exact admission07_06_pos hδ hp
  · exact admission07_07_pos hδ hp
  · exact admission07_08_pos hδ hp
  · exact admission07_09_pos hδ hp
  · exact admission07_10_pos hδ hp
  · exact admission07_11_pos hδ hp
  · exact admission07_12_pos hδ hp
  · exact admission07_13_pos hδ hp
  · exact admission07_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
