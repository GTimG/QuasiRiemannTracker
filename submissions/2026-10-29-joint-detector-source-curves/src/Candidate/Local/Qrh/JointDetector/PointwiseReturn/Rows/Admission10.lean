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

def admission10_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission10_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission10_00_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission10_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission10_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_00_coefficients]

def admission10_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission10_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission10_01_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission10_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission10_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_01_coefficients]

def admission10_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission10_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission10_02_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission10_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission10_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_02_coefficients]

def admission10_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(25933384651246336/424191237967:ℝ), (33022308515523328/424191237967:ℝ), (7148123864276992/424191237967:ℝ)],
![(18737957265429120/424191237967:ℝ), (18677957265429120/424191237967:ℝ), (0:ℝ)]]
theorem admission10_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (367278888701875/434371827678208:ℝ) admission10_03_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission10_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission10_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_03_coefficients]

def admission10_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(202336454207125954964601671/21209561898350000000000:ℝ), (9472:ℝ), (0:ℝ)],
![(598284164486992623982072457/42419123796700000000000:ℝ), (382572751445792875448468/20712462791357421875:ℝ), (91866554324380812724234/20712462791357421875:ℝ)]]
theorem admission10_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (5098593765003135106194987/43437182767820800000000000:ℝ) admission10_04_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission10_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission10_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_04_coefficients]

def admission10_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(43154507727672593117002789/4241912379670000000000:ℝ), (390487771344360046698468/20712462791357421875:ℝ), (179089022765924772724234/20712462791357421875:ℝ)],
![(2324803633296519571086351/1696764951868000000000:ℝ), (10631886359777448/7574843535125:ℝ), (0:ℝ)]]
theorem admission10_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (320864459833074842740947/3474974621425664000000000:ℝ) admission10_05_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission10_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission10_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_05_coefficients]

def admission10_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(184314993298644015878912061626176052329/70288361862490633708237890625000:ℝ), (13545890196585181159870220653864776845357/2600669388912153447204801953125000:ℝ), (840828972056080548575059296712032863648/325083673614019180900600244140625:ℝ), (0:ℝ)],
![(3268346747459021225063265546390136955047/1040267755564861378881920781250000:ℝ), (1403225783638046166730564776526503957691/208053551112972275776384156250000:ℝ), (266570115455407616846027695336277155696/65016734722803836180120048828125:ℝ), (32323687590958068262305299321128228608/65016734722803836180120048828125:ℝ)]]
theorem admission10_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (22458614048640915341759684943246919033/136349975257397510652811120640000000000:ℝ) admission10_06_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission10_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission10_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_06_coefficients]

def admission10_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(360841446791550131349123766931800411031/8996910318398801114654450000000000:ℝ), (1888597526934159894439452759881122823/35144180931245316854118945312500:ℝ), (24270338714720824204356966241792278/1757209046562265842705947265625:ℝ)],
![(93243826779262934469578983949943640613/3598764127359520445861780000000000:ℝ), (361732447491154912306469274707951909/14057672372498126741647578125000:ℝ), (0:ℝ)]]
theorem admission10_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (489451830746869954787865485876144273/1474053786566459574624985088000000000:ℝ) admission10_07_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission10_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission10_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_07_coefficients]

def admission10_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(12581374890963129670125933367597359663987677135929/56230689489992506966590312500000000000000000:ℝ), (24879539635019838025585503667276534946389421863097/56230689489992506966590312500000000000000000:ℝ), (13728310514512259013856056275273410889957304383/62757465948652351525212402343750000000000:ℝ), (0:ℝ)],
![(14249136810145891557516281643941909933377903902283/22492275795997002786636125000000000000000000:ℝ), (7444774205031748592506886514814696462892584680847/4498455159199400557327225000000000000000000:ℝ), (35512275872800041524217901316765695561109610173/25102986379460940610084960937500000000000:ℝ), (2159006688301027626233031818742485404460251761/5491278270507080758456085205078125000000:ℝ)]]
theorem admission10_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (45795573629770185210765143236829958309220652671/2948107573132919149249970176000000000000000000000:ℝ) admission10_08_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission10_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission10_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_08_coefficients]

def admission10_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10538155868924567551324088721251219068247/8996910318398801114654450000000000:ℝ), (408806778024676805860743967380771734053/140576723724981267416475781250000:ℝ), (20254491634005778803224649278393290052/8786045232811329213529736328125:ℝ), (999085254471005673410147173601774208/1757209046562265842705947265625:ℝ)],
![(2096030915404322547812654925511006450661/3598764127359520445861780000000000:ℝ), (65336850952931307122300513574960944911/56230689489992506966590312500000:ℝ), (1018285397378005006066799725748685286/1757209046562265842705947265625:ℝ), (0:ℝ)]]
theorem admission10_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (153664581433142333759498473954885199/2948107573132919149249970176000000000:ℝ) admission10_09_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission10_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission10_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_09_coefficients]

def admission10_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7062494795721209733427197857/149129732097773437500:ℝ), (84499962272504457641142541861/745648660488867187500:ℝ), (2259049664402520687607493888/26630309303173828125:ℝ), (3516591086718042569750819072/186412165122216796875:ℝ)],
![(2253139290230681216063387203/29825946419554687500:ℝ), (3617142942061879269075936377/21304247442539062500:ℝ), (604224251120029408172211712/5326061860634765625:ℝ), (102291507163609808057403904/5326061860634765625:ℝ)],
![(221345427367673010830183843/7953585711881250000:ℝ), (440703430957440242830183843/7953585711881250000:ℝ), (35096470574362757120/1272573713901:ℝ), (0:ℝ)]]
theorem admission10_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (2790637616944242509448471/355837401233987993600000000:ℝ) admission10_10_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission10_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission10_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_10_coefficients]

def admission10_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(337834067003318173623557636693766471401/8996910318398801114654450000000000:ℝ), (3535152838984587545731502869969520677/70288361862490633708237890625000:ℝ), (113530993513968330812554006241792278/8786045232811329213529736328125:ℝ)],
![(87282209038120352617193570559929115739/3598764127359520445861780000000000:ℝ), (5415988992190309117369731439303003/224922757959970027866361250000:ℝ), (0:ℝ)]]
theorem admission10_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (2210266703338833203823940993243203217/7370268932832297873124925440000000000:ℝ) admission10_11_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission10_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission10_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_11_coefficients]

def admission10_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission10_12_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission10_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission10_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_12_coefficients]

def admission10_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission10_13_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission10_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission10_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_13_coefficients]

def admission10_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission10_14_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission10_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission10_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_14_coefficients]

theorem admission10_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ)) (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission10_00_pos hδ hp
  · exact admission10_01_pos hδ hp
  · exact admission10_02_pos hδ hp
  · exact admission10_03_pos hδ hp
  · exact admission10_04_pos hδ hp
  · exact admission10_05_pos hδ hp
  · exact admission10_06_pos hδ hp
  · exact admission10_07_pos hδ hp
  · exact admission10_08_pos hδ hp
  · exact admission10_09_pos hδ hp
  · exact admission10_10_pos hδ hp
  · exact admission10_11_pos hδ hp
  · exact admission10_12_pos hδ hp
  · exact admission10_13_pos hδ hp
  · exact admission10_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
