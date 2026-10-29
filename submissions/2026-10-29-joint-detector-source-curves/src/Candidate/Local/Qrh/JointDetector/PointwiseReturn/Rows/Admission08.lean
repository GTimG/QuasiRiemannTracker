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

def admission08_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission08_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission08_00_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission08_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission08_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_00_coefficients]

def admission08_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission08_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission08_01_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission08_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission08_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_01_coefficients]

def admission08_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission08_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission08_02_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission08_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission08_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_02_coefficients]

def admission08_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6521397923581696/424191237967:ℝ), (1182804127092992/60598748281:ℝ), (1787030966069248/424191237967:ℝ)],
![(4711115196742336/424191237967:ℝ), (4681515196742336/424191237967:ℝ), (0:ℝ)]]
theorem admission08_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (184948304921789/217185913839104:ℝ) admission08_03_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission08_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission08_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_03_coefficients]

def admission08_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(24783560040780086342740947/10604780949175000000000:ℝ), (2304:ℝ), (0:ℝ)],
![(21274806410089047297058497/6059874828100000000000:ℝ), (94980389052124781362117/20712462791357421875:ℝ), (45933277162190406362117/41424925582714843750:ℝ)]]
theorem admission08_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (1240198483379140971777159/10859295691955200000000000:ℝ) admission08_04_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission08_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission08_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_04_coefficients]

def admission08_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5543558488063460689192201/2120956189835000000000:ℝ), (99241023609837032612117/20712462791357421875:ℝ), (89544511382962386362117/41424925582714843750:ℝ)],
![(15842799710050621675398329/42419123796700000000000:ℝ), (14770160371433372/37874217675625:ℝ), (0:ℝ)]]
theorem admission08_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (4145122514987879113805013/43437182767820800000000000:ℝ) admission08_05_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission08_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission08_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_05_coefficients]

def admission08_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(121340199607119807238967692450586419751/371524198416021921029257421875000:ℝ), (1675684976472766373306833763561278830481/2600669388912153447204801953125000:ℝ), (2792217531563876774101553771645857744/8786045232811329213529736328125:ℝ), (0:ℝ)],
![(4103208947557959574715615079742947053741/10402677555648613788819207812500000:ℝ), (8758679675594020867008064239436207652653/10402677555648613788819207812500000:ℝ), (165710535740056446563704848316119536596/325083673614019180900600244140625:ℝ), (4040460948869758532788162415141028576/65016734722803836180120048828125:ℝ)]]
theorem admission08_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (5519955208671093869827698679206861901/34087493814349377663202780160000000000:ℝ) admission08_06_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission08_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission08_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_06_coefficients]

def admission08_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(46181147409910694018505172660852329859/4498455159199400557327225000000000:ℝ), (9772975745760404007333952075307279/717228182270312588859570312500:ℝ), (12135169357360412102178483120896139/3514418093124531685411894531250:ℝ)],
![(17014423334853952122981973381002384241/2570545805256800318472700000000000:ℝ), (917783978345326926265174110209431703/140576723724981267416475781250000:ℝ), (0:ℝ)]]
theorem admission08_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (1241832330903215505122931439371704891/3685134466416148936562462720000000000:ℝ) admission08_07_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission08_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission08_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_07_coefficients]

def admission08_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10978394659377938349018244286076444208366887121/449845515919940055732722500000000000000000:ℝ), (2678140256600258265833866690659395227104866990413/56230689489992506966590312500000000000000000:ℝ), (20422018910312311633801477172583819547796970317/878604523281132921352973632812500000000000:ℝ), (0:ℝ)],
![(3497521500301834959837399838240439546224658757733/44984551591994005573272250000000000000000000:ℝ), (45741316146320638288109845980516134601497144184889/224922757959970027866361250000000000000000000:ℝ), (614259778793832443392920030425110373300161553321/3514418093124531685411894531250000000000000:ℝ), (2159006688301027626233031818742485404460251761/43930226164056646067648681640625000000000:ℝ)]]
theorem admission08_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (9829638391216775583016511945150625523959974347/737026893283229787312492544000000000000000000000:ℝ) admission08_08_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission08_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission08_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_08_coefficients]

def admission08_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(683434799508774118315299855776790030851/4498455159199400557327225000000000:ℝ), (52584093748524495298962946464158776457/140576723724981267416475781250000:ℝ), (2576007911763389518337691921204973882/8786045232811329213529736328125:ℝ), (124885656808875709176268396700221776/1757209046562265842705947265625:ℝ)],
![(1362659704717501875440803598124934845623/17993820636797602229308900000000000:ℝ), (84734911880584345009149578926479093221/562306894899925069665903125000000:ℝ), (188150457747881917931158631227381319/2510298637946094061008496093750:ℝ), (0:ℝ)]]
theorem admission08_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (395869483908687932134021347077858789/7370268932832297873124925440000000000:ℝ) admission08_09_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission08_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission08_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_09_coefficients]

def admission08_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(159271787309713849885502587/53260618606347656250:ℝ), (877676424988982989814161567/124274776748144531250:ℝ), (322298600105932429060991648/62137388374072265625:ℝ), (207859755918321277060991648/186412165122216796875:ℝ)],
![(720811112255630800217125349/149129732097773437500:ℝ), (8022511365117300865831877497/745648660488867187500:ℝ), (1320368971129145582279844032/186412165122216796875:ℝ), (215811213919358866093281344/186412165122216796875:ℝ)],
![(1531214116129549168590387571/852169897701562500000:ℝ), (21246571669233878388132712997/5965189283910937500000:ℝ), (168434380501232547328/95443028542575:ℝ), (0:ℝ)]]
theorem admission08_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (90641596512630666867287003/11119918788562124800000000000:ℝ) admission08_10_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission08_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission08_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_10_coefficients]

def admission08_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8655461955053804953753670750771181593/899691031839880111465445000000000:ℝ), (25624811459913091805976416147191659/2008238910356875248806796875000:ℝ), (56765496756984165406277003120896139/17572090465622658427059472656250:ℝ)],
![(15940612186900652956677350430816735439/2570545805256800318472700000000000:ℝ), (1718656942761094252730638770100844229/281153447449962534832951562500000:ℝ), (0:ℝ)]]
theorem admission08_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (5610815003482559257669267987789352251/18425672332080744682812313600000000000:ℝ) admission08_11_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission08_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission08_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_11_coefficients]

def admission08_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission08_12_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission08_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission08_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_12_coefficients]

def admission08_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission08_13_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission08_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission08_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_13_coefficients]

def admission08_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission08_14_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission08_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission08_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_14_coefficients]

theorem admission08_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission08_00_pos hδ hp
  · exact admission08_01_pos hδ hp
  · exact admission08_02_pos hδ hp
  · exact admission08_03_pos hδ hp
  · exact admission08_04_pos hδ hp
  · exact admission08_05_pos hδ hp
  · exact admission08_06_pos hδ hp
  · exact admission08_07_pos hδ hp
  · exact admission08_08_pos hδ hp
  · exact admission08_09_pos hδ hp
  · exact admission08_10_pos hδ hp
  · exact admission08_11_pos hδ hp
  · exact admission08_12_pos hδ hp
  · exact admission08_13_pos hδ hp
  · exact admission08_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
