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

def admission03_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission03_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission03_00_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission03_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission03_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_00_coefficients]

def admission03_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission03_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission03_01_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission03_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission03_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_01_coefficients]

def admission03_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission03_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission03_02_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission03_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission03_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_02_coefficients]

def admission03_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(729924125645968/424191237967:ℝ), (829613561025296/424191237967:ℝ), (111689435379328/424191237967:ℝ)],
![(613021750074112/424191237967:ℝ), (600221750074112/424191237967:ℝ), (0:ℝ)]]
theorem admission03_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (6188653457197/6787059807472:ℝ) admission03_03_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission03_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission03_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_03_coefficients]

def admission03_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2152832853535228780913649/8483824759340000000000:ℝ), (240:ℝ), (0:ℝ)],
![(901344059827171219086351/2651195237293750000000:ℝ), (130771524755590406362117/331399404661718750000:ℝ), (45933277162190406362117/662798809323437500000:ℝ)]]
theorem admission03_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (413399494459713657259053/4343718276782080000000000:ℝ) admission03_04_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission03_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission03_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_04_coefficients]

def admission03_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10416369370596782422607243/42419123796700000000000:ℝ), (128366505121675930112117/331399404661718750000:ℝ), (89544511382962386362117/662798809323437500000:ℝ)],
![(239852394718594086362117/2651195237293750000000:ℝ), (3696648073568624/37874217675625:ℝ), (0:ℝ)]]
theorem admission03_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (171509068304134840913649/1357411961494400000000000:ℝ) admission03_05_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission03_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission03_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_05_coefficients]

def admission03_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(82269337057088283355642225665858319067/8322142044518891031055366250000000:ℝ), (31212469240700430360889717824732065087/1664428408903778206211073250000000:ℝ), (2314065290824591826525198858056312699/260066938891215344720480195312500:ℝ), (0:ℝ)],
![(29251713963378550378844269766880480961/2600669388912153447204801953125000:ℝ), (11650607218125458155028784527084715877/520133877782430689440960390625000:ℝ), (7903075901737507369823063594501560321/650167347228038361801200488281250:ℝ), (126264404652179954149630075473157143/130033469445607672360240097656250:ℝ)]]
theorem admission03_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (1980706155094513630461745335831061903/13634997525739751065281112064000000000:ℝ) admission03_06_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission03_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission03_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_06_coefficients]

def admission03_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(902409615751133377682107819267155341/719752825471904089172356000000000:ℝ), (159153078728389844733832636319900429/112461378979985013933180625000000:ℝ), (12135169357360412102178483120896139/56230689489992506966590312500000:ℝ)],
![(1110523503749475828448169674123855727/1124613789799850139331806250000000:ℝ), (32884767953741355664224479518904719/35144180931245316854118945312500:ℝ), (0:ℝ)]]
theorem admission03_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (44495620976988177707987771443285843/115160452075504654267576960000000000:ℝ) admission03_07_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission03_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission03_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_07_coefficients]

def admission03_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(26891581190829593734512393849811200907248730189/539814619103928066879267000000000000000000000:ℝ), (4860805823236486590286017633698034947807381951/179938206367976022293089000000000000000000000:ℝ), (0:ℝ), (9739820654632964970434699447216959265084929/688539054979500085305187500000000000000000:ℝ)],
![(46345410776148022068906084905115620212222829087/42173017117494380224942734375000000000000000:ℝ), (80624794790896232813707766670115894746619244717/28115344744996253483295156250000000000000000:ℝ), (20564357036914032019395484908732531758018336439/8032955641427500995227187500000000000000000:ℝ), (26385331471689346798347682097823455857512182653/33738413693995504179954187500000000000000000:ℝ)]]
theorem admission03_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (435615138820194836191649813561898627121569859/5896215146265838298499940352000000000000000000000:ℝ) admission03_08_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission03_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission03_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_08_coefficients]

def admission03_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(17027360901206060505120072686802002297/3598764127359520445861780000000000:ℝ), (935624909695989129515317549180025047/89969103183988011146544500000000:ℝ), (380908846154564941424668702877637263/56230689489992506966590312500000:ℝ), (7805353550554731823516774793763861/7028836186249063370823789062500:ℝ)],
![(3691249663446325300059217900072417171/1124613789799850139331806250000000:ℝ), (901819417380642401971557620281389001/140576723724981267416475781250000:ℝ), (54969305605057659527006813520306109/17572090465622658427059472656250:ℝ), (0:ℝ)]]
theorem admission03_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (16029680848969028421461655280759897/230320904151009308535153920000000000:ℝ) admission03_09_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission03_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission03_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_09_coefficients]

def admission03_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(984584161632476770050930317/23860757135643750000000:ℝ), (676838793140001121820846767/7953585711881250000000:ℝ), (2023816728636170821384401/41424925582714843750:ℝ), (1881151842295434339153203/372824330244433593750:ℝ)],
![(57460008271426266879454037/745648660488867187500:ℝ), (115558507132418462865103061/745648660488867187500:ℝ), (15579317167661978494618384/186412165122216796875:ℝ), (1064817452413929498206128/186412165122216796875:ℝ)],
![(6505170756689311060033426/186412165122216796875:ℝ), (12569650714704527060033426/186412165122216796875:ℝ), (3102248938503790592/95443028542575:ℝ), (0:ℝ)]]
theorem admission03_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (115380880980683469983287/10859295691955200000000000:ℝ) admission03_10_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission03_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission03_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_10_coefficients]

def admission03_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21277277130256898783229386411788250571/17993820636797602229308900000000000:ℝ), (1496575124347779024483719277248181767/1124613789799850139331806250000000:ℝ), (56765496756984165406277003120896139/281153447449962534832951562500000:ℝ)],
![(1047412310221621495998295384920813513/1124613789799850139331806250000000:ℝ), (61883149055541274633019241352731317/70288361862490633708237890625000:ℝ), (0:ℝ)]]
theorem admission03_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (201946795463666304336356969831337323/575802260377523271337884800000000000:ℝ) admission03_11_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission03_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission03_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_11_coefficients]

def admission03_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission03_12_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission03_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission03_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_12_coefficients]

def admission03_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission03_13_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission03_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission03_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_13_coefficients]

def admission03_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission03_14_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission03_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission03_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_14_coefficients]

theorem admission03_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission03_00_pos hδ hp
  · exact admission03_01_pos hδ hp
  · exact admission03_02_pos hδ hp
  · exact admission03_03_pos hδ hp
  · exact admission03_04_pos hδ hp
  · exact admission03_05_pos hδ hp
  · exact admission03_06_pos hδ hp
  · exact admission03_07_pos hδ hp
  · exact admission03_08_pos hδ hp
  · exact admission03_09_pos hδ hp
  · exact admission03_10_pos hδ hp
  · exact admission03_11_pos hδ hp
  · exact admission03_12_pos hδ hp
  · exact admission03_13_pos hδ hp
  · exact admission03_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
