import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w4_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-39793/19793)*δ^0*p^1
def w4_dn_minimum : ℝ := 78965/39586
def w4_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(10147313/5067008:ℝ), (15201073/7600512:ℝ), (30362353/15201024:ℝ), (78965/39586:ℝ)],
  ![(10147313/5067008:ℝ), (15201073/7600512:ℝ), (30362353/15201024:ℝ), (78965/39586:ℝ)],
  ![(10147313/5067008:ℝ), (15201073/7600512:ℝ), (30362353/15201024:ℝ), (78965/39586:ℝ)]]
theorem w4_dn_lower (i : Fin 3) (j : Fin 4) :
    w4_dn_minimum ≤ w4_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_dn_minimum,w4_dn_table]
theorem w4_dn_identity (δ p : ℝ) :
    w4_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_dn_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_dn_table,Fin.sum_univ_succ]
  ring
theorem w4_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_dn_power δ p := by
  rw [w4_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_dn_lower
theorem w4_dn_binding (δ p : ℝ) :
    w4_dn_power δ p=guardD Plane.PR62 δ p := by
  norm_num [w4_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-20000/19793)*δ^0*p^1
def w4_aa_minimum : ℝ := 29586/19793
def w4_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(237313/158344:ℝ), (355657/237516:ℝ), (710689/475032:ℝ), (29586/19793:ℝ)],
  ![(237313/158344:ℝ), (355657/237516:ℝ), (710689/475032:ℝ), (29586/19793:ℝ)],
  ![(237313/158344:ℝ), (355657/237516:ℝ), (710689/475032:ℝ), (29586/19793:ℝ)]]
theorem w4_aa_lower (i : Fin 3) (j : Fin 4) :
    w4_aa_minimum ≤ w4_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_aa_minimum,w4_aa_table]
theorem w4_aa_identity (δ p : ℝ) :
    w4_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_aa_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_aa_table,Fin.sum_univ_succ]
  ring
theorem w4_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_aa_power δ p := by
  rw [w4_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_aa_lower
theorem w4_aa_binding (δ p : ℝ) :
    w4_aa_power δ p=guardA Plane.PR62 δ p := by
  norm_num [w4_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-987047/1979300)*δ^0*p^1
def w4_cc_minimum : ℝ := 2971553/3958600
def w4_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(381345831/506700800:ℝ), (571525223/760051200:ℝ), (1142063399/1520102400:ℝ), (2971553/3958600:ℝ)],
  ![(381345831/506700800:ℝ), (571525223/760051200:ℝ), (1142063399/1520102400:ℝ), (2971553/3958600:ℝ)],
  ![(381345831/506700800:ℝ), (571525223/760051200:ℝ), (1142063399/1520102400:ℝ), (2971553/3958600:ℝ)]]
theorem w4_cc_lower (i : Fin 3) (j : Fin 4) :
    w4_cc_minimum ≤ w4_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_cc_minimum,w4_cc_table]
theorem w4_cc_identity (δ p : ℝ) :
    w4_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_cc_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_cc_table,Fin.sum_univ_succ]
  ring
theorem w4_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_cc_power δ p := by
  rw [w4_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_cc_lower
theorem w4_cc_binding (δ p : ℝ) :
    w4_cc_power δ p=guardC Plane.PR62 δ p := by
  norm_num [w4_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-198965/118758)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (20000/19793)*δ^1*p^2
def w4_j_minimum : ℝ := 133266695/121608192
def w4_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(68866852109/62263394304:ℝ), (206193357365/186790182912:ℝ), (25723323941/23348772864:ℝ), (66855553/60804096:ℝ)],
  ![(275012322293/249053577216:ℝ), (823408174685/747160731648:ℝ), (102722640077/93395091456:ℝ), (266977801/243216384:ℝ)],
  ![(137278618075/124526788608:ℝ), (411021459955/373580365824:ℝ), (51275992195/46697545728:ℝ), (133266695/121608192:ℝ)]]
theorem w4_j_lower (i : Fin 3) (j : Fin 4) :
    w4_j_minimum ≤ w4_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_j_minimum,w4_j_table]
theorem w4_j_identity (δ p : ℝ) :
    w4_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_j_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_j_table,Fin.sum_univ_succ]
  ring
theorem w4_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_j_power δ p := by
  rw [w4_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_j_lower
theorem w4_j_binding (δ p : ℝ) :
    w4_j_power δ p=guardJ Plane.PR62 δ p := by
  norm_num [w4_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-2966347/1979300)*δ^1*p^1 +
  (987047/1979300)*δ^1*p^2
def w4_tlo_minimum : ℝ := 686428743/4053606400
def w4_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(11363724417969/66414287257600:ℝ), (11324556451131/66414287257600:ℝ), (11020961413/64857702400:ℝ), (686428743/4053606400:ℝ)],
  ![(45602478508473/265657149030400:ℝ), (45445297966227/265657149030400:ℝ), (44226975021/259430809600:ℝ), (2754629631/16214425600:ℝ)],
  ![(4575005934507/26565714903040:ℝ), (4559237012793/26565714903040:ℝ), (4437010439/25943080960:ℝ), (276354429/1621442560:ℝ)]]
theorem w4_tlo_lower (i : Fin 3) (j : Fin 4) :
    w4_tlo_minimum ≤ w4_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_tlo_minimum,w4_tlo_table]
theorem w4_tlo_identity (δ p : ℝ) :
    w4_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_tlo_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_tlo_table,Fin.sum_univ_succ]
  ring
theorem w4_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_tlo_power δ p := by
  rw [w4_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_tlo_lower
theorem w4_tlo_binding (δ p : ℝ) :
    w4_tlo_power δ p=guardTLo Plane.PR62 δ p := by
  norm_num [w4_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-33147569/79172000)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (247171993/197930000)*δ^1*p^1 +
  (-487247/1979300)*δ^1*p^2
def w4_thi_minimum : ℝ := 13717958761537/132828574515200
def w4_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(174835592005151/1660357181440000:ℝ), (104946159929107/996214308864000:ℝ), (8202375147253/77829242880000:ℝ), (21369238499/202680320000:ℝ)],
  ![(692620153048727/6641428725760000:ℝ), (415758945726763/3984857235456000:ℝ), (32495589158941/311316971520000:ℝ), (84661026683/810721280000:ℝ)],
  ![(13717958761537/132828574515200:ℝ), (205866625868549/1992428617728000:ℝ), (3218167772887/31131697152000:ℝ), (8384509937/81072128000:ℝ)]]
theorem w4_thi_lower (i : Fin 3) (j : Fin 4) :
    w4_thi_minimum ≤ w4_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_thi_minimum,w4_thi_table]
theorem w4_thi_identity (δ p : ℝ) :
    w4_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_thi_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_thi_table,Fin.sum_univ_succ]
  ring
theorem w4_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_thi_power δ p := by
  rw [w4_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_thi_lower
theorem w4_thi_binding (δ p : ℝ) :
    w4_thi_power δ p=guardTHi Plane.PR62 δ p := by
  norm_num [w4_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-77464883/87880920)*δ^0*p^1 +
  (254535407191/579809016520)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-284216717/73234100)*δ^1*p^1 +
  (4218553755627/1449522541300)*δ^1*p^2 +
  (-11142040000/14495225413)*δ^1*p^3
def w4_rlo_minimum : ℝ := 458922700267249/1781173298749440
def w4_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(19123874768046510209/72956858316777062400:ℝ), (22817539597410144443/87548229980132474880:ℝ), (221552537252023021/854963183399731200:ℝ), (458922700267249/1781173298749440:ℝ)],
  ![(76735727000023912073/291827433267108249600:ℝ), (91557389319037764371/350192919920529899520:ℝ), (889005002073889237/3419852733598924800:ℝ), (1841492387240953/7124693194997760:ℝ)],
  ![(7697595492786178331/29182743326710824960:ℝ), (9184462024843495097/35019291992052989952:ℝ), (89179985513968639/341985273359892480:ℝ), (184729397341291/712469319499776:ℝ)]]
theorem w4_rlo_lower (i : Fin 3) (j : Fin 4) :
    w4_rlo_minimum ≤ w4_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_rlo_minimum,w4_rlo_table]
theorem w4_rlo_identity (δ p : ℝ) :
    w4_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_rlo_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_rlo_table,Fin.sum_univ_succ]
  ring
theorem w4_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_rlo_power δ p := by
  rw [w4_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_rlo_lower
theorem w4_rlo_binding (δ p : ℝ) :
    w4_rlo_power δ p=guardRLo Plane.PR62 δ p := by
  norm_num [w4_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-6940441/2375160)*δ^0*p^1 +
  (39277561271/47011541880)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (6940441/1979300)*δ^1*p^1 +
  (-39277561271/39176284900)*δ^1*p^2
def w4_rhi_minimum : ℝ := 10934628611257/19255927554048
def w4_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(757158681144011487/1314537987689676800:ℝ), (1359928229719017401/2366168377841418240:ℝ), (1472412591758363/2567457007206400:ℝ), (27547755342523/48139818885120:ℝ)],
  ![(3017025818050839639/5258151950758707200:ℝ), (5418862230515812097/9464673511365672960:ℝ), (5867075046205811/10269828028825600:ℝ), (109768653741331/192559275540480:ℝ)],
  ![(300541691152563333/525815195075870720:ℝ), (539801154215555459/946467351136567296:ℝ), (584449972537817/1026982802882560:ℝ), (10934628611257/19255927554048:ℝ)]]
theorem w4_rhi_lower (i : Fin 3) (j : Fin 4) :
    w4_rhi_minimum ≤ w4_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_rhi_minimum,w4_rhi_table]
theorem w4_rhi_identity (δ p : ℝ) :
    w4_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_rhi_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_rhi_table,Fin.sum_univ_succ]
  ring
theorem w4_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_rhi_power δ p := by
  rw [w4_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_rhi_lower
theorem w4_rhi_binding (δ p : ℝ) :
    w4_rhi_power δ p=guardRHi Plane.PR62 δ p := by
  norm_num [w4_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_mlo_power (δ p : ℝ) : ℝ := (-486169/800000)*δ^0*p^0 +
  (29527713017/23751600000)*δ^0*p^1 +
  (-526717431651827/940230837600000)*δ^0*p^2 +
  (2486169/2000000)*δ^1*p^0 +
  (-51263315661/19793000000)*δ^1*p^1 +
  (56108065661/39586000000)*δ^1*p^2 +
  (-1575046733/9794071225)*δ^1*p^3
def w4_mlo_minimum : ℝ := 43497684056576001857/52581519507587072000000
def w4_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(43497684056576001857/52581519507587072000000:ℝ), (226473450747795252977/236616837784141824000000:ℝ), (334860385888380923/308094840864768000000:ℝ), (1171209846231533/962796377702400000:ℝ)],
  ![(262539931848103455689/210326078030348288000000:ℝ), (1302014018603434461689/946467351136567296000000:ℝ), (1852172478563793491/1232379363459072000000:ℝ), (6277624193013461/3851185510809600000:ℝ)],
  ![(7021782549398058079/4206521560606965760000:ℝ), (169813423421568791147/94646735113656729600000:ℝ), (236490341357406329/123237936345907200000:ℝ), (787040900110079/385118551080960000:ℝ)]]
theorem w4_mlo_lower (i : Fin 3) (j : Fin 4) :
    w4_mlo_minimum ≤ w4_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_mlo_minimum,w4_mlo_table]
theorem w4_mlo_identity (δ p : ℝ) :
    w4_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_mlo_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_mlo_table,Fin.sum_univ_succ]
  ring
theorem w4_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_mlo_power δ p := by
  rw [w4_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_mlo_lower
theorem w4_mlo_binding (δ p : ℝ) :
    w4_mlo_power δ p=guardMLo Plane.PR62 δ p := by
  norm_num [w4_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-991174715239/742237500000)*δ^0*p^1 +
  (5789215642577003/9794071225000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (1596364804087/618531250000)*δ^1*p^1 +
  (-1696170989087/1237062500000)*δ^1*p^2 +
  (696278455223/4897035612500)*δ^1*p^3
def w4_mhi_minimum : ℝ := 216705481102635007/12034954721280000000
def w4_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1537125150892758612431213/78872279261380608000000000:ℝ), (142652601762995281714441/7394276180754432000000000:ℝ), (551571391562248889027/28883891331072000000000:ℝ), (568662657062705389/30087386803200000000:ℝ)],
  ![(6005088012715534402767701/315489117045522432000000000:ℝ), (557240250846799171709137/29577104723017728000000000:ℝ), (2154349482120657165659/115535565324288000000000:ℝ), (2220852719638585813/120349547212800000000:ℝ)],
  ![(117233508437200687116211/6309782340910448640000000:ℝ), (54387009464161721656051/2957710472301772800000000:ℝ), (210241339799231877521/11553556532428800000000:ℝ), (216705481102635007/12034954721280000000:ℝ)]]
theorem w4_mhi_lower (i : Fin 3) (j : Fin 4) :
    w4_mhi_minimum ≤ w4_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_mhi_minimum,w4_mhi_table]
theorem w4_mhi_identity (δ p : ℝ) :
    w4_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_mhi_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_mhi_table,Fin.sum_univ_succ]
  ring
theorem w4_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_mhi_power δ p := by
  rw [w4_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_mhi_lower
theorem w4_mhi_binding (δ p : ℝ) :
    w4_mhi_power δ p=guardMHi Plane.PR62 δ p := by
  norm_num [w4_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_widthlo_power (δ p : ℝ) : ℝ := (278592521/400000000)*δ^0*p^0 +
  (-16176827188153/11875800000000)*δ^0*p^1 +
  (94033609970352481/156705139600000000)*δ^0*p^2 +
  (-1278592521/1000000000)*δ^1*p^0 +
  (25515747813949/9896500000000)*δ^1*p^1 +
  (-26872882183949/19793000000000)*δ^1*p^2 +
  (2679103239449/19588142450000)*δ^1*p^3
def w4_widthlo_minimum : ℝ := 4588683156438612289/192559275540480000000
def w4_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(8010175416849210884801819/315489117045522432000000000:ℝ), (2978281132184830506292207/118308418892070912000000000:ℝ), (11534352469998524983079/462142261297152000000000:ℝ), (11911440091421717203/481398188851200000000:ℝ)],
  ![(31454748978772668333230963/1261956468182089728000000000:ℝ), (11694594700346227552077799/473233675568283648000000000:ℝ), (45288458833509351531743/1848569045188608000000000:ℝ), (46766295965036495851/1925592755404800000000:ℝ)],
  ![(617375925802969862545093/25239129363641794560000000:ℝ), (1147606487195313307898677/47323367556828364800000000:ℝ), (4443950778702460313117/184856904518860800000000:ℝ), (4588683156438612289/192559275540480000000:ℝ)]]
theorem w4_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w4_widthlo_minimum ≤ w4_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_widthlo_minimum,w4_widthlo_table]
theorem w4_widthlo_identity (δ p : ℝ) :
    w4_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_widthlo_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w4_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_widthlo_power δ p := by
  rw [w4_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_widthlo_lower
theorem w4_widthlo_binding (δ p : ℝ) :
    w4_widthlo_power δ p=guardWidth Plane.PR62 δ p := by
  norm_num [w4_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-610625988413/742237500000)*δ^1*p^1 +
  (1194091/3958600)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (979517206587/618531250000)*δ^2*p^1 +
  (-178438197/247412500)*δ^2*p^2 +
  (1360/19793)*δ^2*p^3
def w4_tail_minimum : ℝ := 282773603087319/51886161920000000
def w4_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(62763708545994362291/10626285961216000000000:ℝ), (9312609432774510863/1593942894182400000000:ℝ), (719589412345987337/124526788608000000000:ℝ), (1853223215021871/324288512000000000:ℝ)],
  ![(24539337319646095329/4250514384486400000000:ℝ), (6067489253281599011/1062628596121600000000:ℝ), (93753074050676689/16603571814400000000:ℝ), (724237997976693/129715404800000000:ℝ)],
  ![(1917182406857476031/340041150758912000000:ℝ), (7109376414406735763/1275154315345920000000:ℝ), (109834053177483169/19924286177280000000:ℝ), (282773603087319/51886161920000000:ℝ)]]
theorem w4_tail_lower (i : Fin 3) (j : Fin 4) :
    w4_tail_minimum ≤ w4_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_tail_minimum,w4_tail_table]
theorem w4_tail_identity (δ p : ℝ) :
    w4_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_tail_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_tail_table,Fin.sum_univ_succ]
  ring
theorem w4_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_tail_power δ p := by
  rw [w4_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_tail_lower
theorem w4_tail_binding (δ p : ℝ) :
    w4_tail_power δ p=guardTail Plane.PR62 δ p := by
  norm_num [w4_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w4_monotone_power (δ p : ℝ) : ℝ := (4919741/2375160)*δ^0*p^0 +
  (-987047/395860)*δ^0*p^1 +
  (39277561271/47011541880)*δ^0*p^2 +
  (-4945647/1979300)*δ^1*p^0 +
  (2987047/989650)*δ^1*p^1 +
  (-39790318729/39176284900)*δ^1*p^2
def w4_monotone_minimum : ℝ := 15046351832987/32093212590080
def w4_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(624968786341496417/1314537987689676800:ℝ), (5613052117950982691/11830841889207091200:ℝ), (21880499450843927/46214226129715200:ℝ), (37908164479361/80233031475200:ℝ)],
  ![(2490237181112134889/5258151950758707200:ℝ), (22365648269889476027/47323367556828364800:ℝ), (87184579507840079/184856904518860800:ℝ), (151048088123657/320932125900800:ℝ)],
  ![(248059921685828411/525815195075870720:ℝ), (2227908806797502129/4732336755682836480:ℝ), (1736943224246089/3697138090377216:ℝ), (15046351832987/32093212590080:ℝ)]]
theorem w4_monotone_lower (i : Fin 3) (j : Fin 4) :
    w4_monotone_minimum ≤ w4_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w4_monotone_minimum,w4_monotone_table]
theorem w4_monotone_identity (δ p : ℝ) :
    w4_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w4_monotone_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w4_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w4_monotone_table,Fin.sum_univ_succ]
  ring
theorem w4_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w4_monotone_power δ p := by
  rw [w4_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w4_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w4_monotone_lower
theorem w4_monotone_binding (δ p : ℝ) :
    w4_monotone_power δ p=guardMonotone Plane.PR62 δ p := by
  norm_num [w4_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window4_admissible (δ p : ℝ) (ha : window4.Available δ p) :
    Admissible window4.plane δ p := by
  have hd : δ ∈ Set.Icc (231/512:ℝ) (465/1024) := ha.1
  have hp : p ∈ Set.Icc (127/256:ℝ) (1/2) := ha.2
  change Admissible Plane.PR62 δ p
  constructor
  · rw [←w4_dn_binding]
    exact w4_dn_positive hd hp
  · rw [←w4_aa_binding]
    exact w4_aa_positive hd hp
  · rw [←w4_cc_binding]
    exact w4_cc_positive hd hp
  · rw [←w4_j_binding]
    exact w4_j_positive hd hp
  · rw [←w4_tlo_binding]
    exact w4_tlo_positive hd hp
  · rw [←w4_thi_binding]
    exact w4_thi_positive hd hp
  · rw [←w4_rlo_binding]
    exact w4_rlo_positive hd hp
  · rw [←w4_rhi_binding]
    exact w4_rhi_positive hd hp
  · rw [←w4_mlo_binding]
    exact w4_mlo_positive hd hp
  · rw [←w4_mhi_binding]
    exact w4_mhi_positive hd hp
  · rw [←w4_widthlo_binding]
    exact w4_widthlo_positive hd hp
  · rw [←w4_tail_binding]
    exact w4_tail_positive hd hp
  · rw [←w4_monotone_binding]
    exact w4_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window4_admissible
