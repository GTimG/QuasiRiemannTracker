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

def admission13_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1224191237967/424191237967:ℝ), (0:ℝ)]]
theorem admission13_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (1320956189835/848382475934:ℝ) admission13_00_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission13_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission13_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_00_coefficients]

def admission13_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(800000000000/424191237967:ℝ), (0:ℝ)]]
theorem admission13_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (448382475934/424191237967:ℝ) admission13_01_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission13_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission13_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_01_coefficients]

def admission13_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38904970431209593637883/42419123796700000000000:ℝ), (0:ℝ)]]
theorem admission13_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (45933277162190406362117/84838247593400000000000:ℝ) admission13_02_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission13_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission13_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_02_coefficients]

def admission13_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(103328917475744000/424191237967:ℝ), (18828658990407424/60598748281:ℝ), (28592495457107968/424191237967:ℝ)],
![(74641014975555584/424191237967:ℝ), (74519414975555584/424191237967:ℝ), (0:ℝ)]]
theorem admission13_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (13023613127149/15513279559936:ℝ) admission13_03_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission13_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission13_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_03_coefficients]

def admission13_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1645628300020347848639320333/42419123796700000000000:ℝ), (38656:ℝ), (0:ℝ)],
![(301137164213507734508735393/5302390474587500000000:ℝ), (1540895786732346501793872/20712462791357421875:ℝ), (367466217297523250896936/20712462791357421875:ℝ)]]
theorem admission13_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (20807774554472254082039001/173748731071283200000000000:ℝ) admission13_04_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission13_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission13_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_04_coefficients]

def admission13_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(337826432144764465839520919/8483824759340000000000:ℝ), (1542522116092475935543872/20712462791357421875:ℝ), (716356091063699090896936/20712462791357421875:ℝ)],
![(26094057944549973240880223/5302390474587500000000:ℝ), (188952888448163968/37874217675625:ℝ), (0:ℝ)]]
theorem admission13_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (1938244490419495977359331/21718591383910400000000000:ℝ) admission13_05_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission13_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission13_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_05_coefficients]

def admission13_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(54877907045529872985567101420545918538351/2600669388912153447204801953125000:ℝ), (625017808548655721543793523798567156801/14860967936640876841170296875000:ℝ), (6812627272727682529246470655525416737728/325083673614019180900600244140625:ℝ), (0:ℝ)],
![(1168797707257571007155360776279807537117/46440524802002740128657177734375:ℝ), (3521733927067403016065083759156809145807/65016734722803836180120048828125:ℝ), (10720134949068996767605105334670522113536/325083673614019180900600244140625:ℝ), (258589500727664546098442394569025828864/65016734722803836180120048828125:ℝ)]]
theorem admission13_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (90970835836433280954385410452246090419/545399901029590042611244482560000000000:ℝ) admission13_06_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission13_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission13_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_06_coefficients]

def admission13_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2838763051752777430617586767416624719357/17993820636797602229308900000000000:ℝ), (1067667564290285957823400785555311387/5020597275892188122016992187500:ℝ), (97081354858883296817427864967169112/1757209046562265842705947265625:ℝ)],
![(228853327828204877776737459694229091473/2249227579599700278663612500000000:ℝ), (890878259110447635267172263330327842/8786045232811329213529736328125:ℝ), (0:ℝ)]]
theorem admission13_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (602713411415567134408197995004508237/1842567233208074468281231360000000000:ℝ) admission13_07_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission13_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission13_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_07_coefficients]

def admission13_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(110655773630762105425847027723877983886551402749811/56230689489992506966590312500000000000000000:ℝ), (220122358321258412050345288488786427626843536116339/56230689489992506966590312500000000000000000:ℝ), (427622988287352952073329031417391299034344270963/219651130820283230338243408203125000000000:ℝ), (0:ℝ)],
![(36404067364414044482590211823109475292116641513759/7028836186249063370823789062500000000000000:ℝ), (94764966505313002989867026134472475019294038231071/7028836186249063370823789062500000000000000:ℝ), (314334938377084504977353257830844485669337401367/27456391352535403792280426025390625000000:ℝ), (2159006688301027626233031818742485404460251761/686409783813385094807010650634765625000:ℝ)]]
theorem admission13_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (202613354713789989479157859316002201877024876533/11792430292531676596999880704000000000000000000000:ℝ) admission13_08_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission13_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission13_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_08_coefficients]

def admission13_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(164020284948626077034941523365469056087421/17993820636797602229308900000000000:ℝ), (3200632180173710020188864455066399355671/140576723724981267416475781250000:ℝ), (159914503111438206364935877679667314392/8786045232811329213529736328125:ℝ), (7992682035768045387281177388814193664/1757209046562265842705947265625:ℝ)],
![(10090007887812722497214699685200660253649/2249227579599700278663612500000000:ℝ), (157463227415940247422125850409152215059/17572090465622658427059472656250:ℝ), (39317129254714850868764444664961407424/8786045232811329213529736328125:ℝ), (0:ℝ)]]
theorem admission13_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (26603815946930266904533644478326229/526447780916592705223208960000000000:ℝ) admission13_09_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission13_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission13_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_09_coefficients]

def admission13_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1123402260761332423216590182909/1491297320977734375000:ℝ), (387762361842609027715160444123/213042474425390625000:ℝ), (257676227006343305955037423616/186412165122216796875:ℝ), (58809923947820709606345807872/186412165122216796875:ℝ)],
![(6329231355601000197968398006/5326061860634765625:ℝ), (167211128825007268533906209014/62137388374072265625:ℝ), (37714237555708212664137449472/20712462791357421875:ℝ), (59318817259887115304412348416/186412165122216796875:ℝ)],
![(80578544478057455596710774184/186412165122216796875:ℝ), (22970562361231513597244396312/26630309303173828125:ℝ), (5867147315241189638144/13634718363225:ℝ), (0:ℝ)]]
theorem admission13_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (20912253253779569411153227/2779979697140531200000000000:ℝ) admission13_10_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission13_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission13_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_10_coefficients]

def admission13_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2655983555927038709001033329214261317379/17993820636797602229308900000000000:ℝ), (1997664151389802037372917901138021137/10041194551784376244033984375000:ℝ), (454123974055873323250216024967169112/8786045232811329213529736328125:ℝ)],
![(214061873123695912627261135534403289327/2249227579599700278663612500000000:ℝ), (833168088678924472812721689731766323/8786045232811329213529736328125:ℝ), (0:ℝ)]]
theorem admission13_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (2720259256605803380725218489213331917/9212836166040372341406156800000000000:ℝ) admission13_11_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission13_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission13_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_11_coefficients]

def admission13_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission13_12_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission13_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission13_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_12_coefficients]

def admission13_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (1759806519582834297883/40000000000000000000000:ℝ) admission13_13_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission13_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission13_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_13_coefficients]

def admission13_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission13_14_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission13_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission13_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_14_coefficients]

theorem admission13_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission13_00_pos hδ hp
  · exact admission13_01_pos hδ hp
  · exact admission13_02_pos hδ hp
  · exact admission13_03_pos hδ hp
  · exact admission13_04_pos hδ hp
  · exact admission13_05_pos hδ hp
  · exact admission13_06_pos hδ hp
  · exact admission13_07_pos hδ hp
  · exact admission13_08_pos hδ hp
  · exact admission13_09_pos hδ hp
  · exact admission13_10_pos hδ hp
  · exact admission13_11_pos hδ hp
  · exact admission13_12_pos hδ hp
  · exact admission13_13_pos hδ hp
  · exact admission13_14_pos hδ hp

end
end Qrh.JointDetector.PointwiseReturn
