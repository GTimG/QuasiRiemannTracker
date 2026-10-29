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

def admission09_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission09_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission09_00_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission09_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission09_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_00_coefficients]

def admission09_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission09_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission09_01_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission09_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission09_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_01_coefficients]

def admission09_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission09_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission09_02_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission09_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission09_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_02_coefficients]

def admission09_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6498146162811584/424191237967:ℝ), (8255577128880832/424191237967:ℝ), (1787030966069248/424191237967:ℝ)],
![(4687863435972224/424191237967:ℝ), (4657463435972224/424191237967:ℝ), (0:ℝ)]]
theorem admission09_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (13023613127149/15513279559936:ℝ) admission09_03_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission09_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission09_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_03_coefficients]

def admission09_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(101887969056540354964601671/42419123796700000000000:ℝ), (2368:ℝ), (0:ℝ)],
![(75838686882021670336523681/21209561898350000000000:ℝ), (96305986670771656362117/20712462791357421875:ℝ), (45933277162190406362117/41424925582714843750:ℝ)]]
theorem admission09_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (5098593765003135106194987/43437182767820800000000000:ℝ) admission09_04_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission09_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission09_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_04_coefficients]

def admission09_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(107536379366204105310206137/42419123796700000000000:ℝ), (97621942836090011674617/20712462791357421875:ℝ), (89544511382962386362117/41424925582714843750:ℝ)],
![(6254004657492756600880223/21209561898350000000000:ℝ), (11809555528010248/37874217675625:ℝ), (0:ℝ)]]
theorem admission09_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (1938244490419495977359331/21718591383910400000000000:ℝ) admission09_05_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission09_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission09_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_05_coefficients]

def admission09_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(493819313676971172781358441902911783083/1486096793664087684117029687500000:ℝ), (184304281625311804628912061626176052329/281153447449962534832951562500000:ℝ), (105103621507010068571882412089004107956/325083673614019180900600244140625:ℝ), (0:ℝ)],
![(2081209277148701590747014392223454891147/5201338777824306894409603906250000:ℝ), (4437599094919746072525237732679803133451/5201338777824306894409603906250000:ℝ), (167502108579203074493829770854226908024/325083673614019180900600244140625:ℝ), (4040460948869758532788162415141028576/65016734722803836180120048828125:ℝ)]]
theorem admission09_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (22458614048640915341759684943246919033/136349975257397510652811120640000000000:ℝ) admission09_06_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission09_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission09_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_06_coefficients]

def admission09_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(181233030453662974824027647246004921367/17993820636797602229308900000000000:ℝ), (1888597526934159894439452759881122823/140576723724981267416475781250000:ℝ), (12135169357360412102178483120896139/3514418093124531685411894531250:ℝ)],
![(8257814582714133115062912162115163687/1285272902628400159236350000000000:ℝ), (445439129555223817633586131665163921/70288361862490633708237890625000:ℝ), (0:ℝ)]]
theorem admission09_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (602713411415567134408197995004508237/1842567233208074468281231360000000000:ℝ) admission09_07_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission09_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission09_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_07_coefficients]

def admission09_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1286698651481582670574775255848134492057360954469/44984551591994005573272250000000000000000000:ℝ), (12578973414016853949170477244631558788987677135929/224922757959970027866361250000000000000000000:ℝ), (13728310514512259013856056275273410889957304383/502059727589218812201699218750000000000000:ℝ), (0:ℝ)],
![(1843190342922811897755175332740464808722665500051/22492275795997002786636125000000000000000000:ℝ), (23803864266968229586972428231255056241032676679583/112461378979985013933180625000000000000000000:ℝ), (314334938377084504977353257830844485669337401367/1757209046562265842705947265625000000000000:ℝ), (2159006688301027626233031818742485404460251761/43930226164056646067648681640625000000000:ℝ)]]
theorem admission09_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (45795573629770185210765143236829958309220652671/2948107573132919149249970176000000000000000000000:ℝ) admission09_08_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission09_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission09_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_08_coefficients]

def admission09_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2641488830440389137405791980335205831863/17993820636797602229308900000000000:ℝ), (204625142417105025818367239758691998181/562306894899925069665903125000000:ℝ), (5063622908501444700806162319598322513/17572090465622658427059472656250:ℝ), (124885656808875709176268396700221776/1757209046562265842705947265625:ℝ)],
![(635204668561397269792698077676490277041/8996910318398801114654450000000000:ℝ), (39511839651795694815832516414267992787/281153447449962534832951562500000:ℝ), (614330144604919544824444447890021991/8786045232811329213529736328125:ℝ), (0:ℝ)]]
theorem admission09_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (26603815946930266904533644478326229/526447780916592705223208960000000000:ℝ) admission09_09_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission09_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission09_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_09_coefficients]

def admission09_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2554129187765647249164426611/852169897701562500000:ℝ), (42727788173591938080187532837/5965189283910937500000:ℝ), (200052283035531836875342624/37282433024443359375:ℝ), (6393219197725613003587744/5326061860634765625:ℝ)],
![(7090590441076879459970596147/1491297320977734375000:ℝ), (1771350799019811833610707547/165699702330859375000:ℝ), (63719078955195829736837248/8876769767724609375:ℝ), (231714129921434044157860736/186412165122216796875:ℝ)],
![(2551987987829387613588846773/1491297320977734375000:ℝ), (722706776388855103655549539/213042474425390625000:ℝ), (22918544200160897024/13634718363225:ℝ), (0:ℝ)]]
theorem admission09_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (20912253253779569411153227/2779979697140531200000000000:ℝ) admission09_10_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission09_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission09_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_10_coefficients]

def admission09_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(169712153987456356072769104211514794409/17993820636797602229308900000000000:ℝ), (3535152838984587545731502869969520677/281153447449962534832951562500000:ℝ), (56765496756984165406277003120896139/17572090465622658427059472656250:ℝ)],
![(7727657156763201978174081586557736473/1285272902628400159236350000000000:ℝ), (833168088678924472812721689731766323/140576723724981267416475781250000:ℝ), (0:ℝ)]]
theorem admission09_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (2720259256605803380725218489213331917/9212836166040372341406156800000000000:ℝ) admission09_11_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission09_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission09_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_11_coefficients]

def admission09_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission09_12_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission09_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission09_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_12_coefficients]

def admission09_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission09_13_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission09_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission09_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_13_coefficients]

def admission09_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission09_14_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission09_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission09_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_14_coefficients]

theorem admission09_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission09_00_pos hδ hp
  · exact admission09_01_pos hδ hp
  · exact admission09_02_pos hδ hp
  · exact admission09_03_pos hδ hp
  · exact admission09_04_pos hδ hp
  · exact admission09_05_pos hδ hp
  · exact admission09_06_pos hδ hp
  · exact admission09_07_pos hδ hp
  · exact admission09_08_pos hδ hp
  · exact admission09_09_pos hδ hp
  · exact admission09_10_pos hδ hp
  · exact admission09_11_pos hδ hp
  · exact admission09_12_pos hδ hp
  · exact admission09_13_pos hδ hp
  · exact admission09_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
