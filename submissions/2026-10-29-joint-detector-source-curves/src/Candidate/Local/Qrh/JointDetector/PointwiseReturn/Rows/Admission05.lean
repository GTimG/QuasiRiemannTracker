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

def admission05_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission05_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission05_00_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission05_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission05_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_00_coefficients]

def admission05_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission05_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission05_01_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission05_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission05_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_01_coefficients]

def admission05_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission05_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission05_02_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission05_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission05_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_02_coefficients]

def admission05_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(418200310416384/424191237967:ℝ), (523489745795712/424191237967:ℝ), (111689435379328/424191237967:ℝ)],
![(301297934844528/424191237967:ℝ), (294097934844528/424191237967:ℝ), (0:ℝ)]]
theorem admission05_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (46891506515873/54296478459776:ℝ) admission05_03_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission05_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission05_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_03_coefficients]

def admission05_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(717610951178409593637883/5302390474587500000000:ℝ), (128:ℝ), (0:ℝ)],
![(1879645659797174469983287/8483824759340000000000:ℝ), (93654791433477906362117/331399404661718750000:ℝ), (45933277162190406362117/662798809323437500000:ℝ)]]
theorem admission05_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (137799831486571219086351/1357411961494400000000000:ℝ) admission05_04_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission05_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission05_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_04_coefficients]

def admission05_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(956208485782293177259053/5302390474587500000000:ℝ), (105717346704825116362117/331399404661718750000:ℝ), (89544511382962386362117/662798809323437500000:ℝ)],
![(1070936831159068377259053/42419123796700000000000:ℝ), (1108172825928531/37874217675625:ℝ), (0:ℝ)]]
theorem admission05_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (1103439012284191568222841/10859295691955200000000000:ℝ) admission05_05_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission05_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission05_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_05_coefficients]

def admission05_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(26726425870334951295851668257417338101/5201338777824306894409603906250000:ℝ), (10135434362299298705233223621406830161/1040267755564861378881920781250000:ℝ), (1502277457988702014394653115601050794/325083673614019180900600244140625:ℝ), (0:ℝ)],
![(270492145091294999650110534000134804849/41610710222594455155276831250000000:ℝ), (22286168836979913663575550456189953977/1664428408903778206211073250000000:ℝ), (10244935181306863664598745361125760323/1300334694456076723602400976562500:ℝ), (126264404652179954149630075473157143/130033469445607672360240097656250:ℝ)]]
theorem admission05_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (642645249339319250922351056598423809/4260936726793672207900347520000000000:ℝ) admission05_06_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission05_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission05_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_06_coefficients]

def admission05_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1595930278043892312535308998959701287/2249227579599700278663612500000000:ℝ), (126445382694284771839341374642290133/140576723724981267416475781250000:ℝ), (12135169357360412102178483120896139/56230689489992506966590312500000:ℝ)],
![(7975577890564417313400491295980418403/17993820636797602229308900000000000:ℝ), (236172424395051554315793989272133891/562306894899925069665903125000000:ℝ), (0:ℝ)]]
theorem admission05_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (319559459743824185357366722183598327/921283616604037234140615680000000000:ℝ) admission05_07_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission05_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission05_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_07_coefficients]

def admission05_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(17818328582048451427961976377115067187110134361/112461378979985013933180625000000000000000000:ℝ), (29322932223345731635677122851114510205677576169/112461378979985013933180625000000000000000000:ℝ), (751490118746968134001873992000652688660465113/7028836186249063370823789062500000000000000:ℝ), (0:ℝ)],
![(1086429423229496092669504965909701767178886878429/899691031839880111465445000000000000000000000:ℝ), (2790272861979262870172635428084134538798199530541/899691031839880111465445000000000000000000000:ℝ), (149962420208373969207783386297132943815412075977/56230689489992506966590312500000000000000000:ℝ), (2159006688301027626233031818742485404460251761/2811534474499625348329515625000000000000000:ℝ)]]
theorem admission05_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (419077290789211588039677061115396163822402383/92128361660403723414061568000000000000000000000:ℝ) admission05_08_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission05_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission05_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_08_coefficients]

def admission05_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6188962799623839483584585834076852691/2249227579599700278663612500000000:ℝ), (1838461843447210220793570595533052321/281153447449962534832951562500000:ℝ), (43012402215844659219939608856691006/8786045232811329213529736328125:ℝ), (7805353550554731823516774793763861/7028836186249063370823789062500:ℝ)],
![(23434892506101618144023809639763484779/17993820636797602229308900000000000:ℝ), (5746182683268231960010547959266016409/2249227579599700278663612500000000:ℝ), (351361529815126940346832985350823621/281153447449962534832951562500000:ℝ), (0:ℝ)]]
theorem admission05_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (104821386140088031901142917864787593/1842567233208074468281231360000000000:ℝ) admission05_09_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission05_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission05_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_09_coefficients]

def admission05_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(253660327405056093637883/20712462791357421875:ℝ), (5112363451095662998206128/186412165122216796875:ℝ), (6969441523846670466395543/372824330244433593750:ℝ), (187614359278050593637883/53260618606347656250:ℝ)],
![(3456493880935144342740947/165699702330859375000:ℝ), (13359302760549672317292479/298259464195546875000:ℝ), (5238862898030897219086351/186412165122216796875:ℝ), (780891788739389406362117/186412165122216796875:ℝ)],
![(20449352831900467897392757/2651195237293750000000:ℝ), (39546793529835659897392757/2651195237293750000000:ℝ), (76292562791740768/10604780949175:ℝ), (0:ℝ)]]
theorem admission05_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (6071075867817387923465187/694994924285132800000000000:ℝ) admission05_10_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission05_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission05_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_10_coefficients]

def admission05_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(12012290274219958553988091279103861/17993820636797602229308900000000:ℝ), (7415540363282840002456015279601716/8786045232811329213529736328125:ℝ), (56765496756984165406277003120896139/281153447449962534832951562500000:ℝ)],
![(7493610107509003706731431026048626637/17993820636797602229308900000000000:ℝ), (442744427041084889958958540184538953/1124613789799850139331806250000000:ℝ), (0:ℝ)]]
theorem admission05_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (1445277873438377938472024749288010167/4606418083020186170703078400000000000:ℝ) admission05_11_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission05_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission05_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_11_coefficients]

def admission05_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission05_12_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission05_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission05_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_12_coefficients]

def admission05_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission05_13_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission05_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission05_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_13_coefficients]

def admission05_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission05_14_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission05_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission05_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_14_coefficients]

theorem admission05_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission05_00_pos hδ hp
  · exact admission05_01_pos hδ hp
  · exact admission05_02_pos hδ hp
  · exact admission05_03_pos hδ hp
  · exact admission05_04_pos hδ hp
  · exact admission05_05_pos hδ hp
  · exact admission05_06_pos hδ hp
  · exact admission05_07_pos hδ hp
  · exact admission05_08_pos hδ hp
  · exact admission05_09_pos hδ hp
  · exact admission05_10_pos hδ hp
  · exact admission05_11_pos hδ hp
  · exact admission05_12_pos hδ hp
  · exact admission05_13_pos hδ hp
  · exact admission05_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
