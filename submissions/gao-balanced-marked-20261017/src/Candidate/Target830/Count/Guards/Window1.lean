import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w1_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-84999/44999)*δ^0*p^1
def w1_dn_minimum : ℝ := 184995/89998
def w1_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(23764359/11519744:ℝ), (11868013/5759872:ℝ), (23707693/11519744:ℝ), (184995/89998:ℝ)],
  ![(23764359/11519744:ℝ), (11868013/5759872:ℝ), (23707693/11519744:ℝ), (184995/89998:ℝ)],
  ![(23764359/11519744:ℝ), (11868013/5759872:ℝ), (23707693/11519744:ℝ), (184995/89998:ℝ)]]
theorem w1_dn_lower (i : Fin 3) (j : Fin 4) :
    w1_dn_minimum ≤ w1_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_dn_minimum,w1_dn_table]
theorem w1_dn_identity (δ p : ℝ) :
    w1_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_dn_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_dn_table,Fin.sum_univ_succ]
  ring
theorem w1_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_dn_power δ p := by
  rw [w1_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_dn_lower
theorem w1_dn_binding (δ p : ℝ) :
    w1_dn_power δ p=guardD Plane.oldWeak δ p := by
  norm_num [w1_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-40000/44999)*δ^0*p^1
def w1_aa_minimum : ℝ := 69998/44999
def w1_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(280617/179996:ℝ), (420613/269994:ℝ), (840601/539988:ℝ), (69998/44999:ℝ)],
  ![(280617/179996:ℝ), (420613/269994:ℝ), (840601/539988:ℝ), (69998/44999:ℝ)],
  ![(280617/179996:ℝ), (420613/269994:ℝ), (840601/539988:ℝ), (69998/44999:ℝ)]]
theorem w1_aa_lower (i : Fin 3) (j : Fin 4) :
    w1_aa_minimum ≤ w1_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_aa_minimum,w1_aa_table]
theorem w1_aa_identity (δ p : ℝ) :
    w1_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_aa_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_aa_table,Fin.sum_univ_succ]
  ring
theorem w1_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_aa_power δ p := by
  rw [w1_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_aa_lower
theorem w1_aa_binding (δ p : ℝ) :
    w1_aa_power δ p=guardA Plane.oldWeak δ p := by
  norm_num [w1_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-1005451199/2249950000)*δ^0*p^1
def w1_cc_minimum : ℝ := 3494448801/4499900000
def w1_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(448294897727/575987200000:ℝ), (671939620991/863980800000:ℝ), (1342873790783/1727961600000:ℝ), (3494448801/4499900000:ℝ)],
  ![(448294897727/575987200000:ℝ), (671939620991/863980800000:ℝ), (1342873790783/1727961600000:ℝ), (3494448801/4499900000:ℝ)],
  ![(448294897727/575987200000:ℝ), (671939620991/863980800000:ℝ), (1342873790783/1727961600000:ℝ), (3494448801/4499900000:ℝ)]]
theorem w1_cc_lower (i : Fin 3) (j : Fin 4) :
    w1_cc_minimum ≤ w1_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_cc_minimum,w1_cc_table]
theorem w1_cc_identity (δ p : ℝ) :
    w1_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_cc_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_cc_table,Fin.sum_univ_succ]
  ring
theorem w1_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_cc_power δ p := by
  rw [w1_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_cc_lower
theorem w1_cc_binding (δ p : ℝ) :
    w1_cc_power δ p=guardC Plane.oldWeak δ p := by
  norm_num [w1_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-141665/89998)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (40000/44999)*δ^1*p^2
def w1_j_minimum : ℝ := 105078777/92157952
def w1_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(6784562789/5898108928:ℝ), (20316211105/17694326784:ℝ), (5069692367/4423581696:ℝ), (13177971/11519744:ℝ)],
  ![(108376431095/94369742848:ℝ), (324529593355/283109228544:ℝ), (80982616325/70777307136:ℝ), (210502545/184315904:ℝ)],
  ![(54099928783/47184871424:ℝ), (161999904515/141554614272:ℝ), (40425077389/35388653568:ℝ), (105078777/92157952:ℝ)]]
theorem w1_j_lower (i : Fin 3) (j : Fin 4) :
    w1_j_minimum ≤ w1_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_j_minimum,w1_j_table]
theorem w1_j_identity (δ p : ℝ) :
    w1_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_j_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_j_table,Fin.sum_univ_succ]
  ring
theorem w1_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_j_power δ p := by
  rw [w1_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_j_lower
theorem w1_j_binding (δ p : ℝ) :
    w1_j_power δ p=guardJ Plane.oldWeak δ p := by
  norm_num [w1_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-3255401199/2249950000)*δ^1*p^1 +
  (1005451199/2249950000)*δ^1*p^2
def w1_tlo_minimum : ℝ := 199183581657/1151974400000
def w1_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(3296312382986631/18873948569600000:ℝ), (3285330419041069/18873948569600000:ℝ), (799406142253/4607897600000:ℝ), (199183581657/1151974400000:ℝ)],
  ![(10582897650641289/60396635422720000:ℝ), (10547639766395011/60396635422720000:ℝ), (2566514456707/14745272320000:ℝ), (639484130583/3686318080000:ℝ)],
  ![(1561411128783141/8881858150400000:ℝ), (1556209145861559/8881858150400000:ℝ), (378666067383/2168422400000:ℝ), (94350117627/542105600000:ℝ)]]
theorem w1_tlo_lower (i : Fin 3) (j : Fin 4) :
    w1_tlo_minimum ≤ w1_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_tlo_minimum,w1_tlo_table]
theorem w1_tlo_identity (δ p : ℝ) :
    w1_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_tlo_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_tlo_table,Fin.sum_univ_succ]
  ring
theorem w1_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_tlo_power δ p := by
  rw [w1_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_tlo_lower
theorem w1_tlo_binding (δ p : ℝ) :
    w1_tlo_power δ p=guardTLo Plane.oldWeak δ p := by
  norm_num [w1_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-4164951/10588000)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (1346569347/1124975000)*δ^1*p^1 +
  (-505651199/2249950000)*δ^1*p^2
def w1_thi_minimum : ℝ := 983449521169179/8881858150400000
def w1_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(2129166788120889/18873948569600000:ℝ), (2130158813107731/18873948569600000:ℝ), (8324770432507/73726361600000:ℝ), (130133913633/1151974400000:ℝ)],
  ![(6750395232968631/60396635422720000:ℝ), (6753681914546749/60396635422720000:ℝ), (26394288091413/235924357120000:ℝ), (412607589327/3686318080000:ℝ)],
  ![(983449521169179/8881858150400000:ℝ), (983949356933641/8881858150400000:ℝ), (3845486882177/34694758400000:ℝ), (60115684563/542105600000:ℝ)]]
theorem w1_thi_lower (i : Fin 3) (j : Fin 4) :
    w1_thi_minimum ≤ w1_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_thi_minimum,w1_thi_table]
theorem w1_thi_identity (δ p : ℝ) :
    w1_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_thi_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_thi_table,Fin.sum_univ_succ]
  ring
theorem w1_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_thi_power δ p := by
  rw [w1_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_thi_lower
theorem w1_thi_binding (δ p : ℝ) :
    w1_thi_power δ p=guardTHi Plane.oldWeak δ p := by
  norm_num [w1_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-29380855637/33299260000)*δ^0*p^1 +
  (37162238853713/88143141220000)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-303851833089/83248150000)*δ^1*p^1 +
  (9619431819860637/3746083501850000)*δ^1*p^2 +
  (-47599440000/74921670037)*δ^1*p^3
def w1_rlo_minimum : ℝ := 103706258993452971/383598950589440000
def w1_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(8637914306595918519197/31424426032286924800000:ℝ), (5154179461503425383537/18854655619372154880000:ℝ), (16685286632539398703/61375832094310400000:ℝ), (103706258993452971/383598950589440000:ℝ)],
  ![(1109238667326061503307/4022326532132726374400:ℝ), (661879120070722401047/2413395919279635824640:ℝ), (2142672891825867593/7856106508071731200:ℝ), (13317731454646701/49100665675448320:ℝ)],
  ![(4091265821352372927047/14787965191664435200000:ℝ), (2441262018636052768387/8872779114998661120000:ℝ), (7903048142230485853/28882744514969600000:ℝ), (49121550581365521/180517153218560000:ℝ)]]
theorem w1_rlo_lower (i : Fin 3) (j : Fin 4) :
    w1_rlo_minimum ≤ w1_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_rlo_minimum,w1_rlo_table]
theorem w1_rlo_identity (δ p : ℝ) :
    w1_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_rlo_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_rlo_table,Fin.sum_univ_succ]
  ring
theorem w1_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_rlo_power δ p := by
  rw [w1_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_rlo_lower
theorem w1_rlo_binding (δ p : ℝ) :
    w1_rlo_power δ p=guardRLo Plane.oldWeak δ p := by
  norm_num [w1_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-2422101199/899980000)*δ^0*p^1 +
  (28487448821267/40498200020000)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (7266303597/2249950000)*δ^1*p^1 +
  (-85462346463801/101245500050000)*δ^1*p^2
def w1_rhi_minimum : ℝ := 50983794845213139/82940313640960000
def w1_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(529120897410151362319/849308811683430400000:ℝ), (316856686468222474499/509585287010058240000:ℝ), (1029432563204195981/1658806272819200000:ℝ), (6421458522347217/10367539205120000:ℝ)],
  ![(67471792287200509289/108711527895479091200:ℝ), (40404543912055214869/65226916737287454720:ℝ), (131269924166978011/212327202920857600:ℝ), (818843704191927/1327045018255360:ℝ)],
  ![(4201006856618852762573/6794470493467443200000:ℝ), (2515714497261122062633/4076682296080465920000:ℝ), (8173280015238683527/13270450182553600000:ℝ), (50983794845213139/82940313640960000:ℝ)]]
theorem w1_rhi_lower (i : Fin 3) (j : Fin 4) :
    w1_rhi_minimum ≤ w1_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_rhi_minimum,w1_rhi_table]
theorem w1_rhi_identity (δ p : ℝ) :
    w1_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_rhi_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_rhi_table,Fin.sum_univ_succ]
  ring
theorem w1_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_rhi_power δ p := by
  rw [w1_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_rhi_lower
theorem w1_rhi_binding (δ p : ℝ) :
    w1_rhi_power δ p=guardRHi Plane.oldWeak δ p := by
  norm_num [w1_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_mlo_power (δ p : ℝ) : ℝ := (-476425597/800000000)*δ^0*p^0 +
  (21722542459801/17999600000000)*δ^0*p^1 +
  (-848474708088201733/1619928000800000000)*δ^0*p^2 +
  (2476425597/2000000000)*δ^1*p^0 +
  (-114360945500199/44999000000000)*δ^1*p^1 +
  (121430553560199/89998000000000)*δ^1*p^2 +
  (-7648890012/50622750025)*δ^1*p^3
def w1_mlo_minimum : ℝ := 131636972697115840758169/33972352467337216000000000
def w1_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(131636972697115840758169/33972352467337216000000000:ℝ), (408433624620483529186921/101917057402011648000000000:ℝ), (549406734402668756899/132704501825536000000000:ℝ), (1771821091943708229/414701568204800000000:ℝ)],
  ![(467586947777138917522199/108711527895479091200000000:ℝ), (1445215970843349667789127/326134583686437273600000000:ℝ), (1937025470415372871661/424654405841715200000000:ℝ), (6225660410057349291/1327045018255360000000:ℝ)],
  ![(1284838957308767861545643/271778819738697728000000000:ℝ), (3958610857252880105450267/815336459216093184000000000:ℝ), (5289873476855514303113/1061636014604288000000000:ℝ), (16953733314737080623/3317612545638400000000:ℝ)]]
theorem w1_mlo_lower (i : Fin 3) (j : Fin 4) :
    w1_mlo_minimum ≤ w1_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_mlo_minimum,w1_mlo_table]
theorem w1_mlo_identity (δ p : ℝ) :
    w1_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_mlo_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_mlo_table,Fin.sum_univ_succ]
  ring
theorem w1_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_mlo_power δ p := by
  rw [w1_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_mlo_lower
theorem w1_mlo_binding (δ p : ℝ) :
    w1_mlo_power δ p=guardMLo Plane.oldWeak δ p := by
  norm_num [w1_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-46011360299/35155468750)*δ^0*p^1 +
  (28139797709583197/50622750025000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (3556911695841/1406218750000)*δ^1*p^1 +
  (-3656383562091/2812437500000)*δ^1*p^2 +
  (13462506010713/101245500050000)*δ^1*p^3
def w1_mhi_minimum : ℝ := 523365135026113917/25918848012800000000
def w1_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(2954700962447896895268287/135889409869348864000000000:ℝ), (34290353323824109042943/1592454021906432000000000:ℝ), (176853290032373109593/8294031364096000000000:ℝ), (68403813906238191/3239856001600000000:ℝ)],
  ![(9251528096871177942848977/434846111581916364800000000:ℝ), (107357191010607078437041/5095852870100582400000000:ℝ), (553644174503301922327/26540900365107200000000:ℝ), (214119129255203889/10367539205120000000:ℝ)],
  ![(22620032784772714552098589/1087115278954790912000000000:ℝ), (262463128462442519841661/12739632175251456000000000:ℝ), (1353394552257524734891/66352250912768000000000:ℝ), (523365135026113917/25918848012800000000:ℝ)]]
theorem w1_mhi_lower (i : Fin 3) (j : Fin 4) :
    w1_mhi_minimum ≤ w1_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_mhi_minimum,w1_mhi_table]
theorem w1_mhi_identity (δ p : ℝ) :
    w1_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_mhi_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_mhi_table,Fin.sum_univ_succ]
  ring
theorem w1_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_mhi_power δ p := by
  rw [w1_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_mhi_lower
theorem w1_mhi_binding (δ p : ℝ) :
    w1_mhi_power δ p=guardMHi Plane.oldWeak δ p := by
  norm_num [w1_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_widthlo_power (δ p : ℝ) : ℝ := (696461/1000000)*δ^0*p^0 +
  (-15006399769/11249750000)*δ^0*p^1 +
  (1141615040028479/2024910001000000)*δ^0*p^2 +
  (-3196461/2500000)*δ^1*p^0 +
  (142110140487/56248750000)*δ^1*p^1 +
  (-144891410337/112497500000)*δ^1*p^2 +
  (13010082853401/101245500050000)*δ^1*p^3
def w1_widthlo_minimum : ℝ := 54802709475826563/2073507841024000000
def w1_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(152515285245100660844759/5435576394773954560000000:ℝ), (886333121459975572963/31849080438128640000000:ℝ), (9156606343592766101/331761254563840000000:ℝ), (7094300298558849/259188480128000000:ℝ)],
  ![(479729634801125310360889/17393844463276654592000000:ℝ), (2787781373103841297181/101917057402011648000000:ℝ), (28798803898677210139/1061636014604288000000:ℝ), (22311422372859471/829403136409600000:ℝ)],
  ![(1178525892044821265046373/43484611158191636480000000:ℝ), (6848241893839401902201/254792643505029120000000:ℝ), (70741168744643921887/2654090036510720000000:ℝ), (54802709475826563/2073507841024000000:ℝ)]]
theorem w1_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w1_widthlo_minimum ≤ w1_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_widthlo_minimum,w1_widthlo_table]
theorem w1_widthlo_identity (δ p : ℝ) :
    w1_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_widthlo_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w1_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_widthlo_power δ p := by
  rw [w1_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_widthlo_lower
theorem w1_widthlo_binding (δ p : ℝ) :
    w1_widthlo_power δ p=guardWidth Plane.oldWeak δ p := by
  norm_num [w1_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-223588898089/281243750000)*δ^1*p^1 +
  (716454599/2699940000)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (269257531277/175777343750)*δ^2*p^1 +
  (-58572559/89998000)*δ^2*p^2 +
  (160/2647)*δ^2*p^3
def w1_tail_minimum : ℝ := 2164105698868053/346947584000000000
def w1_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(10129958812196747127/1509915885568000000000:ℝ), (6016378321078172053/905949531340800000000:ℝ), (116304948594896879/17694326784000000000:ℝ), (599495552116029/92157952000000000:ℝ)],
  ![(79415653734182958309/12079327084544000000000:ℝ), (9432144963431028659/1449519250145280000000:ℝ), (911568376081606733/141554614272000000000:ℝ), (4698092200453623/737263616000000000:ℝ)],
  ![(36596122694447786559/5684389216256000000000:ℝ), (7243227090805555023/1136877843251200000000:ℝ), (139985660576857341/22204645376000000000:ℝ), (2164105698868053/346947584000000000:ℝ)]]
theorem w1_tail_lower (i : Fin 3) (j : Fin 4) :
    w1_tail_minimum ≤ w1_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_tail_minimum,w1_tail_table]
theorem w1_tail_identity (δ p : ℝ) :
    w1_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_tail_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_tail_table,Fin.sum_univ_succ]
  ring
theorem w1_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_tail_power δ p := by
  rw [w1_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_tail_lower
theorem w1_tail_binding (δ p : ℝ) :
    w1_tail_power δ p=guardTail Plane.oldWeak δ p := by
  norm_num [w1_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w1_monotone_power (δ p : ℝ) : ℝ := (1838751199/899980000)*δ^0*p^0 +
  (-1005451199/449990000)*δ^0*p^1 +
  (28487448821267/40498200020000)*δ^0*p^2 +
  (-5505351199/2249950000)*δ^1*p^0 +
  (176791247/66175000)*δ^1*p^1 +
  (-84971749456199/101245500050000)*δ^1*p^2
def w1_monotone_minimum : ℝ := 211364794806448179/414701568204800000
def w1_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(438538197344580649969/849308811683430400000:ℝ), (1313233916257979855089/2547926435050291200000:ℝ), (1706845720151199951/3317612545638400000:ℝ), (26621203257002097/51837696025600000:ℝ)],
  ![(1398034974707638132031/2717788197386977280000:ℝ), (837303071675991787123/1630672918432186368000:ℝ), (5441327361919851521/10616360146042880000:ℝ), (84866884172492991/165880627281920000:ℝ)],
  ![(3481869294781545460403/6794470493467443200000:ℝ), (10426705461835955837363/20383411480402329600000:ℝ), (13551871048389657997/26540900365107200000:ℝ), (211364794806448179/414701568204800000:ℝ)]]
theorem w1_monotone_lower (i : Fin 3) (j : Fin 4) :
    w1_monotone_minimum ≤ w1_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w1_monotone_minimum,w1_monotone_table]
theorem w1_monotone_identity (δ p : ℝ) :
    w1_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w1_monotone_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w1_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w1_monotone_table,Fin.sum_univ_succ]
  ring
theorem w1_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w1_monotone_power δ p := by
  rw [w1_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w1_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w1_monotone_lower
theorem w1_monotone_binding (δ p : ℝ) :
    w1_monotone_power δ p=guardMonotone Plane.oldWeak δ p := by
  norm_num [w1_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window1_admissible (δ p : ℝ) (ha : window1.Available δ p) :
    Admissible window1.plane δ p := by
  have hd : δ ∈ Set.Icc (57/128:ℝ) (459/1024) := ha.1
  have hp : p ∈ Set.Icc (127/256:ℝ) (1/2) := ha.2
  change Admissible Plane.oldWeak δ p
  constructor
  · rw [←w1_dn_binding]
    exact w1_dn_positive hd hp
  · rw [←w1_aa_binding]
    exact w1_aa_positive hd hp
  · rw [←w1_cc_binding]
    exact w1_cc_positive hd hp
  · rw [←w1_j_binding]
    exact w1_j_positive hd hp
  · rw [←w1_tlo_binding]
    exact w1_tlo_positive hd hp
  · rw [←w1_thi_binding]
    exact w1_thi_positive hd hp
  · rw [←w1_rlo_binding]
    exact w1_rlo_positive hd hp
  · rw [←w1_rhi_binding]
    exact w1_rhi_positive hd hp
  · rw [←w1_mlo_binding]
    exact w1_mlo_positive hd hp
  · rw [←w1_mhi_binding]
    exact w1_mhi_positive hd hp
  · rw [←w1_widthlo_binding]
    exact w1_widthlo_positive hd hp
  · rw [←w1_tail_binding]
    exact w1_tail_positive hd hp
  · rw [←w1_monotone_binding]
    exact w1_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window1_admissible
