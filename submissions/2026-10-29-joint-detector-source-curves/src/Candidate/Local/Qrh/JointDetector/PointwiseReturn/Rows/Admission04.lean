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

def admission04_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission04_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission04_00_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission04_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission04_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_00_coefficients]

def admission04_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission04_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission04_01_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission04_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission04_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_01_coefficients]

def admission04_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission04_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission04_02_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission04_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission04_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_02_coefficients]

def admission04_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(106150077604096/424191237967:ℝ), (130872436448928/424191237967:ℝ), (27922358844832/424191237967:ℝ)],
![(76021248663000/424191237967:ℝ), (10288749809000/60598748281:ℝ), (0:ℝ)]]
theorem admission04_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (22136892687085/27148239229888:ℝ) admission04_03_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission04_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission04_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_03_coefficients]

def admission04_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(378257960804809593637883/10604780949175000000000:ℝ), (32:ℝ), (0:ℝ)],
![(2626222238619094469983287/42419123796700000000000:ℝ), (98957181908065406362117/1325597618646875000000:ℝ), (45933277162190406362117/2651195237293750000000:ℝ)]]
theorem admission04_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (137799831486571219086351/1357411961494400000000000:ℝ) admission04_04_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission04_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission04_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_04_coefficients]

def admission04_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(93729551535108358362117/2120956189835000000000:ℝ), (105717346704825116362117/1325597618646875000000:ℝ), (89544511382962386362117/2651195237293750000000:ℝ)],
![(1696240012864406362117/8483824759340000000000:ℝ), (1472086460291/605987482810:ℝ), (0:ℝ)]]
theorem admission04_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (83480547813530440913649/1085929569195520000000000:ℝ) admission04_05_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission04_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission04_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_05_coefficients]

def admission04_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2113414227583289311527777618944133107/2972193587328175368234059375000000:ℝ), (26640732483677261295851668257417338101/20805355111297227577638415625000000:ℝ), (751138728994351007197326557800525397/1300334694456076723602400976562500:ℝ), (0:ℝ)],
![(15694456282899095857932810601048925401/16644284089037782062110732500000000:ℝ), (30611364460898469626946690986522576201/16644284089037782062110732500000000:ℝ), (534641419554676032356498799782630159/520133877782430689440960390625000:ℝ), (126264404652179954149630075473157143/1040267755564861378881920781250000:ℝ)]]
theorem admission04_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (642645249339319250922351056598423809/4260936726793672207900347520000000000:ℝ) admission04_06_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission04_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission04_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_06_coefficients]

def admission04_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(827070603636822379864147664239303003/4498455159199400557327225000000000:ℝ), (126445382694284771839341374642290133/562306894899925069665903125000000:ℝ), (12135169357360412102178483120896139/224922757959970027866361250000000:ℝ)],
![(7589184629735248543124389634043899/73444165864480009099220000000000:ℝ), (2989524359431032333111316319900429/32131822565710003980908750000000:ℝ), (0:ℝ)]]
theorem admission04_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (4045056452453470700726161040298713/13161194522914817630580224000000000:ℝ) admission04_07_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission04_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission04_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_07_coefficients]

def admission04_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(12325645890726916292261821839120845677826413457/449845515919940055732722500000000000000000000:ℝ), (17299090323394241491647138979104067187110134361/449845515919940055732722500000000000000000000:ℝ), (751490118746968134001873992000652688660465113/56230689489992506966590312500000000000000000:ℝ), (0:ℝ)],
![(14410489100789247742438070450258013240589801577/71975282547190408917235600000000000000000000:ℝ), (167967876508789805435488065582357533214725240021/359876412735952044586178000000000000000000000:ℝ), (16437251816871053576956987153371154185392532539/44984551591994005573272250000000000000000000:ℝ), (2159006688301027626233031818742485404460251761/22492275795997002786636125000000000000000000:ℝ)]]
theorem admission04_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (419077290789211588039677061115396163822402383/92128361660403723414061568000000000000000000000:ℝ) admission04_08_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission04_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission04_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_08_coefficients]

def admission04_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1587909167649056790486438418772867791/4498455159199400557327225000000000:ℝ), (930386185573465035166509599744771789/1124613789799850139331806250000000:ℝ), (21506201107922329609969804428345503/35144180931245316854118945312500:ℝ), (7805353550554731823516774793763861/56230689489992506966590312500000:ℝ)],
![(443604543130401674222111965445112287/3598764127359520445861780000000000:ℝ), (43481222183459677368554865119346677/179938206367976022293089000000000:ℝ), (26296861478979260447761146253919837/224922757959970027866361250000000:ℝ), (0:ℝ)]]
theorem admission04_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (8140532548842383643059259348349601/184256723320807446828123136000000000:ℝ) admission04_09_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission04_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission04_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_09_coefficients]

def admission04_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(83866905919341364545961/99419821398515625000:ℝ), (699745093070352968637883/372824330244433593750:ℝ), (3857445355721972219086351/2982594641955468750000:ℝ), (780891788739389406362117/2982594641955468750000:ℝ)],
![(334821945537219593637883/238607571356437500000:ℝ), (1202714547516896406362117/397679285594062500000:ℝ), (27861712563968058051731/14202831628359375000:ℝ), (102937485127181406362117/298259464195546875000:ℝ)],
![(789604185513893155465181/1908860570851500000000:ℝ), (1490502263704369155465181/1908860570851500000000:ℝ), (1390996156380952/3817721141703:ℝ), (0:ℝ)]]
theorem admission04_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (6086870325437406362117/992849891835904000000000:ℝ) admission04_10_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission04_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission04_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_10_coefficients]

def admission04_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(779409104805227960559249466582547533/4498455159199400557327225000000000:ℝ), (1853885090820710000614003819900429/8786045232811329213529736328125:ℝ), (56765496756984165406277003120896139/1124613789799850139331806250000000:ℝ)],
![(49779034859175982609234196805041803/514109161051360063694540000000000:ℝ), (5577480880540565469339473564960391/64263645131420007961817500000000:ℝ), (0:ℝ)]]
theorem admission04_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (728560790381385967001824994243041/2632238904582963526116044800000000:ℝ) admission04_11_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission04_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission04_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_11_coefficients]

def admission04_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission04_12_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission04_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission04_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_12_coefficients]

def admission04_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission04_13_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission04_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission04_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_13_coefficients]

def admission04_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission04_14_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission04_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission04_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_14_coefficients]

theorem admission04_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission04_00_pos hδ hp
  · exact admission04_01_pos hδ hp
  · exact admission04_02_pos hδ hp
  · exact admission04_03_pos hδ hp
  · exact admission04_04_pos hδ hp
  · exact admission04_05_pos hδ hp
  · exact admission04_06_pos hδ hp
  · exact admission04_07_pos hδ hp
  · exact admission04_08_pos hδ hp
  · exact admission04_09_pos hδ hp
  · exact admission04_10_pos hδ hp
  · exact admission04_11_pos hδ hp
  · exact admission04_12_pos hδ hp
  · exact admission04_13_pos hδ hp
  · exact admission04_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
