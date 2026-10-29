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

def admission11_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission11_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission11_00_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission11_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission11_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_00_coefficients]

def admission11_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission11_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission11_01_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission11_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission11_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_01_coefficients]

def admission11_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission11_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission11_02_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission11_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission11_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_02_coefficients]

def admission11_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3698011589958016/60598748281:ℝ), (32974204993983104/424191237967:ℝ), (7148123864276992/424191237967:ℝ)],
![(2670093391984128/60598748281:ℝ), (18629853743888896/424191237967:ℝ), (0:ℝ)]]
theorem admission11_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (13023613127149/15513279559936:ℝ) admission11_03_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission11_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission11_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_03_coefficients]

def admission11_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16405658449226428780913649/1696764951868000000000:ℝ), (9600:ℝ), (0:ℝ)],
![(30187635865170071678785517/2120956189835000000000:ℝ), (385223946683086625448468/20712462791357421875:ℝ), (91866554324380812724234/20712462791357421875:ℝ)]]
theorem admission11_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (413399494459713657259053/3474974621425664000000000:ℝ) admission11_04_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission11_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission11_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_04_coefficients]

def admission11_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(424894409457026923816390007/42419123796700000000000:ℝ), (387249609796866004823468/20712462791357421875:ℝ), (179089022765924772724234/20712462791357421875:ℝ)],
![(12867355753178495480880223/10604780949175000000000:ℝ), (47238222112040992/37874217675625:ℝ), (0:ℝ)]]
theorem admission11_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (1938244490419495977359331/21718591383910400000000000:ℝ) admission11_05_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission11_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission11_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_05_coefficients]

def admission11_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2751167746003692132866380757252085297319/1040267755564861378881920781250000:ℝ), (5464591913824243557062169515218364815271/1040267755564861378881920781250000:ℝ), (169599052682533412059111797372892469872/65016734722803836180120048828125:ℝ), (0:ℝ)],
![(4114565740803477403652184739468520847371/1300334694456076723602400976562500:ℝ), (8827955941725502408458631420381217331979/1300334694456076723602400976562500:ℝ), (1340016868633624595950638166833815264192/325083673614019180900600244140625:ℝ), (32323687590958068262305299321128228608/65016734722803836180120048828125:ℝ)]]
theorem admission11_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (9059204262247674109193652022582661899/54539990102959004261124448256000000000:ℝ) admission11_06_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission11_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission11_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_06_coefficients]

def admission11_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(142949480467011182440102050813134225957/3598764127359520445861780000000000:ℝ), (750057866926688099576180734576628357/14057672372498126741647578125000:ℝ), (24270338714720824204356966241792278/1757209046562265842705947265625:ℝ)],
![(114820910662067580462539409987947127697/4498455159199400557327225000000000:ℝ), (445439129555223817633586131665163921/17572090465622658427059472656250:ℝ), (0:ℝ)]]
theorem admission11_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (602713411415567134408197995004508237/1842567233208074468281231360000000000:ℝ) admission11_07_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission11_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission11_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_07_coefficients]

def admission11_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5405845414864882400465783314372689716708712689227/22492275795997002786636125000000000000000000:ℝ), (10693996839315715491382937585365821664455349765067/22492275795997002786636125000000000000000000:ℝ), (8264257806540327710230850923616254019916620431/35144180931245316854118945312500000000000:ℝ), (0:ℝ)],
![(18278040335781902612414614514094569730614432171423/28115344744996253483295156250000000000000000:ℝ), (47457565013083154054603960865660862500453130530079/28115344744996253483295156250000000000000000:ℝ), (314334938377084504977353257830844485669337401367/219651130820283230338243408203125000000000:ℝ), (2159006688301027626233031818742485404460251761/5491278270507080758456085205078125000000:ℝ)]]
theorem admission11_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (156909067719109525280367011087819796530915297/9433944234025341277599904563200000000000000000:ℝ) admission11_08_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission11_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission11_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_08_coefficients]

def admission11_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(118347357616026919055903895344212572247/102821832210272012738908000000000:ℝ), (23035576483163978824239234605818752697/8032955641427500995227187500000:ℝ), (803108232158204405259448249310801582/351441809312453168541189453125:ℝ), (999085254471005673410147173601774208/1757209046562265842705947265625:ℝ)],
![(361236800784899588257081388224635509287/642636451314200079618175000000000:ℝ), (11261281272358649383513851582747057173/10041194551784376244033984375000:ℝ), (4914641156839356358595555583120175928/8786045232811329213529736328125:ℝ), (0:ℝ)]]
theorem admission11_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (26603815946930266904533644478326229/526447780916592705223208960000000000:ℝ) admission11_09_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission11_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission11_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_09_coefficients]

def admission11_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(141305565898631682969598208453/2982594641955468750000:ℝ), (113388959505434334262052247703/994198213985156250000:ℝ), (1785836422332816831422484736/20712462791357421875:ℝ), (3643814414734643994267454208/186412165122216796875:ℝ)],
![(3101476018054861145215216373/41424925582714843750:ℝ), (9008237827893269464720004923/53260618606347656250:ℝ), (21279375926372512679577315328/186412165122216796875:ℝ), (3707426078742944706525771776/186412165122216796875:ℝ)],
![(5058825597221985725588846773/186412165122216796875:ℝ), (1438911282643883135655549539/26630309303173828125:ℝ), (366696707202574352384/13634718363225:ℝ), (0:ℝ)]]
theorem admission11_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (20912253253779569411153227/2779979697140531200000000000:ℝ) admission11_10_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission11_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission11_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_10_coefficients]

def admission11_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(668922519907208904590078457582836164039/17993820636797602229308900000000000:ℝ), (7017984912565929784357810349301729771/140576723724981267416475781250000:ℝ), (113530993513968330812554006241792278/8786045232811329213529736328125:ℝ)],
![(107416357772793580107232759248737199983/4498455159199400557327225000000000:ℝ), (833168088678924472812721689731766323/35144180931245316854118945312500:ℝ), (0:ℝ)]]
theorem admission11_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (2720259256605803380725218489213331917/9212836166040372341406156800000000000:ℝ) admission11_11_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission11_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission11_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_11_coefficients]

def admission11_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission11_12_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission11_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission11_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_12_coefficients]

def admission11_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission11_13_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission11_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission11_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_13_coefficients]

def admission11_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission11_14_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission11_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission11_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_14_coefficients]

theorem admission11_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission11_00_pos hδ hp
  · exact admission11_01_pos hδ hp
  · exact admission11_02_pos hδ hp
  · exact admission11_03_pos hδ hp
  · exact admission11_04_pos hδ hp
  · exact admission11_05_pos hδ hp
  · exact admission11_06_pos hδ hp
  · exact admission11_07_pos hδ hp
  · exact admission11_08_pos hδ hp
  · exact admission11_09_pos hδ hp
  · exact admission11_10_pos hδ hp
  · exact admission11_11_pos hδ hp
  · exact admission11_12_pos hδ hp
  · exact admission11_13_pos hδ hp
  · exact admission11_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
