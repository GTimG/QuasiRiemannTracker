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

def admission17_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(157755268577/57755268577:ℝ), (0:ℝ)]]
theorem admission17_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (188776342885/115510537154:ℝ) admission17_00_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission17_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission17_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_00_coefficients]

def admission17_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(100000000000/57755268577:ℝ), (0:ℝ)]]
theorem admission17_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (65510537154/57755268577:ℝ) admission17_01_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission17_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission17_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_01_coefficients]

def admission17_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4934995154607585173877/5775526857700000000000:ℝ), (0:ℝ)]]
theorem admission17_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (6616058560792414826123/11551053715400000000000:ℝ) admission17_02_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission17_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission17_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_02_coefficients]

def admission17_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(509573006484848/519797417193:ℝ), (645275214686960/519797417193:ℝ), (15778023133568/57755268577:ℝ)],
![(362387556957824/519797417193:ℝ), (355187556957824/519797417193:ℝ), (0:ℝ)]]
theorem admission17_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (2666134606121/2772252891696:ℝ) admission17_03_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission17_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission17_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_03_coefficients]

def admission17_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(681403974144653096217139/5775526857700000000000:ℝ), (112:ℝ), (0:ℝ)],
![(150271893364146903782861/721940857212500000000:ℝ), (12391585418492414826123/45121303575781250000:ℝ), (6616058560792414826123/90242607151562500000:ℝ)]]
theorem admission17_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (138937229776640711348583/1478534875571200000000000:ℝ) admission17_04_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission17_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission17_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_04_coefficients]

def admission17_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3470814465256968197964199/17326580573100000000000:ℝ), (46680718761714563228369/135363910727343750000:ℝ), (12776883531227794826123/90242607151562500000:ℝ)],
![(85305769048911484478369/2165822571637500000000:ℝ), (4630687725636712/108291128581875:ℝ), (0:ℝ)]]
theorem admission17_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (24569626855598615521631/184816859446400000000000:ℝ) admission17_05_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission17_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission17_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_05_coefficients]

def admission17_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(33781732547773408083190333216380934327/6942365369485421252758481250000000:ℝ), (4290954487977305244841943489019718649/462824357965694750183898750000000:ℝ), (958423355115288807482463097466088919/216948917796419414148702539062500:ℝ), (0:ℝ)],
![(5554964088618667807460783732659611221/867795671185677656594810156250000:ℝ), (776785840772042291945372471306961931/57853044745711843772987343750000:ℝ), (886360154912701760551671000478658933/108474458898209707074351269531250:ℝ), (73696282953394051253270620636971/65149825164089914158769531250:ℝ)]]
theorem admission17_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (96512818550592521686734580844637027/631909523409161898917749760000000000:ℝ) admission17_06_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission17_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission17_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_06_coefficients]

def admission17_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2327769723365457644503829370775532309/3002103943561263244436100000000000:ℝ), (92864106710156813971033841512868593/93815748236289476388628125000000:ℝ), (249791067883877703704670620636971/1042397202625438626540312500000:ℝ)],
![(182392638417100911713176884708779527/375262992945157905554512500000000:ℝ), (5432153189707702065423963172993319/11726968529536184548578515625000:ℝ), (0:ℝ)]]
theorem admission17_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (2747701746722654740751376827006681/6404488412930694921463680000000000:ℝ) admission17_07_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission17_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission17_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_07_coefficients]

def admission17_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (79841133734988004342497807501834811467397091/9381574823628947638862812500000000000000000:ℝ), (209728319977529959370859817946066276594789581/3752629929451579055545125000000000000000000:ℝ), (817215957842296802378129870130036760039153723/18763149647257895277725625000000000000000000:ℝ)],
![(2221896071792421310347343412796536358343448219/2084794405250877253080625000000000000000000:ℝ), (54383907425213869046038944696442626519683652841/18763149647257895277725625000000000000000000:ℝ), (49980819989161991089091561326994530000005465713/18763149647257895277725625000000000000000000:ℝ), (15511984781993768709560223226181730705412846843/18763149647257895277725625000000000000000000:ℝ)]]
theorem admission17_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (1584286956065309877850982687485333587245050117/1639549033710257899894702080000000000000000000000:ℝ) admission17_08_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission17_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission17_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_08_coefficients]

def admission17_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(9461305863246252568844126450506883917/3002103943561263244436100000000000:ℝ), (2771805437456111659803368997765133967/375262992945157905554512500000000:ℝ), (84515574489500213245763277225983881/15635958039381579398104687500000:ℝ), (152774095587459497090188583623029/130299650328179828317539062500:ℝ)],
![(615477434764847423424946623928954571/375262992945157905554512500000000:ℝ), (150784035948026021450908829861948401/46907874118144738194314062500000:ℝ), (3072545738825787691906284846626903/1954494754922697424763085937500:ℝ), (0:ℝ)]]
theorem admission17_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (963619214467286917830118063913899/12808976825861389842927360000000000:ℝ) admission17_09_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission17_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission17_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_09_coefficients]

def admission17_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(38218956139864176611265683/3248733857456250000000:ℝ), (82174934700131881167672083/3248733857456250000000:ℝ), (32239290215723500521631/2030458660910156250:ℝ), (4777139553056185173877/2030458660910156250:ℝ)],
![(4382308942488539361255427/203045866091015625000:ℝ), (3051620884709711421170561/67681955363671875000:ℝ), (74901310083362560463672/2820081473486328125:ℝ), (77837889295188681391016/25380733261376953125:ℝ)],
![(450182627322533436912647/50761466522753906250:ℝ), (872854724676781436912647/50761466522753906250:ℝ), (108117656922687488/12994935429825:ℝ), (0:ℝ)]]
theorem admission17_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (16787817440175563087353/1478534875571200000000000:ℝ) admission17_10_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission17_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission17_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_10_coefficients]

def admission17_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(241387022924855242008492940193091363/333567104840140360492900000000000:ℝ), (19142978590498986577571188386296959/20847944052508772530806250000000:ℝ), (1144356326291326680572230620636971/5211986013127193132701562500000:ℝ)],
![(19042035312343205042128527455282857/41695888105017545061612500000000:ℝ), (1131126112264683436013129410389013/2605993006563596566350781250000:ℝ), (0:ℝ)]]
theorem admission17_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (12437744697026782316641312001527841/32022442064653474607318400000000000:ℝ) admission17_11_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission17_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission17_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_11_coefficients]

def admission17_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission17_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission17_12_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission17_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission17_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_12_coefficients]

def admission17_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission17_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (263461388040213633877/5000000000000000000000:ℝ) admission17_13_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission17_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission17_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_13_coefficients]

def admission17_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission17_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission17_14_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission17_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission17_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_14_coefficients]

theorem admission17_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission17_00_pos hδ hp
  · exact admission17_01_pos hδ hp
  · exact admission17_02_pos hδ hp
  · exact admission17_03_pos hδ hp
  · exact admission17_04_pos hδ hp
  · exact admission17_05_pos hδ hp
  · exact admission17_06_pos hδ hp
  · exact admission17_07_pos hδ hp
  · exact admission17_08_pos hδ hp
  · exact admission17_09_pos hδ hp
  · exact admission17_10_pos hδ hp
  · exact admission17_11_pos hδ hp
  · exact admission17_12_pos hδ hp
  · exact admission17_13_pos hδ hp
  · exact admission17_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
