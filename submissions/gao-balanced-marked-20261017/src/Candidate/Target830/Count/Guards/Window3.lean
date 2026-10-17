import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w3_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-9615/4828)*δ^0*p^1
def w3_dn_minimum : ℝ := 19353/9656
def w3_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(2486799/1235968:ℝ), (1241797/617984:ℝ), (2480389/1235968:ℝ), (19353/9656:ℝ)],
  ![(2486799/1235968:ℝ), (1241797/617984:ℝ), (2480389/1235968:ℝ), (19353/9656:ℝ)],
  ![(2486799/1235968:ℝ), (1241797/617984:ℝ), (2480389/1235968:ℝ), (19353/9656:ℝ)]]
theorem w3_dn_lower (i : Fin 3) (j : Fin 4) :
    w3_dn_minimum ≤ w3_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_dn_minimum,w3_dn_table]
theorem w3_dn_identity (δ p : ℝ) :
    w3_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_dn_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_dn_table,Fin.sum_univ_succ]
  ring
theorem w3_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_dn_power δ p := by
  rw [w3_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_dn_lower
theorem w3_dn_binding (δ p : ℝ) :
    w3_dn_power δ p=guardD Plane.PR60 δ p := by
  norm_num [w3_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-4787/4828)*δ^0*p^1
def w3_aa_minimum : ℝ := 14525/9656
def w3_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1863987/1235968:ℝ), (2793587/1853952:ℝ), (5582387/3707904:ℝ), (14525/9656:ℝ)],
  ![(1863987/1235968:ℝ), (2793587/1853952:ℝ), (5582387/3707904:ℝ), (14525/9656:ℝ)],
  ![(1863987/1235968:ℝ), (2793587/1853952:ℝ), (5582387/3707904:ℝ), (14525/9656:ℝ)]]
theorem w3_aa_lower (i : Fin 3) (j : Fin 4) :
    w3_aa_minimum ≤ w3_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_aa_minimum,w3_aa_table]
theorem w3_aa_identity (δ p : ℝ) :
    w3_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_aa_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_aa_table,Fin.sum_univ_succ]
  ring
theorem w3_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_aa_power δ p := by
  rw [w3_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_aa_lower
theorem w3_aa_binding (δ p : ℝ) :
    w3_aa_power δ p=guardA Plane.PR60 δ p := by
  norm_num [w3_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-142100527/289680000)*δ^0*p^1
def w3_cc_minimum : ℝ := 437259473/579360000
def w3_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(56111313071/74158080000:ℝ), (84095919343/111237120000:ℝ), (168049738159/222474240000:ℝ), (437259473/579360000:ℝ)],
  ![(56111313071/74158080000:ℝ), (84095919343/111237120000:ℝ), (168049738159/222474240000:ℝ), (437259473/579360000:ℝ)],
  ![(56111313071/74158080000:ℝ), (84095919343/111237120000:ℝ), (168049738159/222474240000:ℝ), (437259473/579360000:ℝ)]]
theorem w3_cc_lower (i : Fin 3) (j : Fin 4) :
    w3_cc_minimum ≤ w3_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_cc_minimum,w3_cc_table]
theorem w3_cc_identity (δ p : ℝ) :
    w3_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_cc_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_cc_table,Fin.sum_univ_succ]
  ring
theorem w3_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_cc_power δ p := by
  rw [w3_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_cc_lower
theorem w3_cc_binding (δ p : ℝ) :
    w3_cc_power δ p=guardC Plane.PR60 δ p := by
  norm_num [w3_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-16025/9656)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (4787/4828)*δ^1*p^2
def w3_j_minimum : ℝ := 10928749/9887744
def w3_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(361409235441/324001595392:ℝ), (1082118065393/972004786176:ℝ), (4218791491/3796893696:ℝ), (21930041/19775488:ℝ)],
  ![(721629972219/648003190784:ℝ), (2160670574587/1944009572352:ℝ), (8423654849/7593787392:ℝ), (43787539/39550976:ℝ)],
  ![(180110368389/162000797696:ℝ), (539276254597/486002393088:ℝ), (2102431679/1898446848:ℝ), (10928749/9887744:ℝ)]]
theorem w3_j_lower (i : Fin 3) (j : Fin 4) :
    w3_j_minimum ≤ w3_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_j_minimum,w3_j_table]
theorem w3_j_identity (δ p : ℝ) :
    w3_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_j_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_j_table,Fin.sum_univ_succ]
  ring
theorem w3_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_j_power δ p := by
  rw [w3_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_j_lower
theorem w3_j_binding (δ p : ℝ) :
    w3_j_power δ p=guardJ Plane.PR60 δ p := by
  norm_num [w3_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-431780527/289680000)*δ^1*p^1 +
  (142100527/289680000)*δ^1*p^2
def w3_tlo_minimum : ℝ := 3935335257/23265280000
def w3_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(65145234475431/381178347520000:ℝ), (64921907632269/381178347520000:ℝ), (3948914007/23265280000:ℝ), (3935335257/23265280000:ℝ)],
  ![(2222176331550813/12960063815680000:ℝ), (6643675214368861/38880191447040000:ℝ), (134701844461/791019520000:ℝ), (134238658211/791019520000:ℝ)],
  ![(557353672734243/3240015953920000:ℝ), (1666328962561571/9720047861760000:ℝ), (33785153171/197754880000:ℝ), (33668979421/197754880000:ℝ)]]
theorem w3_tlo_lower (i : Fin 3) (j : Fin 4) :
    w3_tlo_minimum ≤ w3_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_tlo_minimum,w3_tlo_table]
theorem w3_tlo_identity (δ p : ℝ) :
    w3_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_tlo_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_tlo_table,Fin.sum_univ_succ]
  ring
theorem w3_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_tlo_power δ p := by
  rw [w3_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_tlo_lower
theorem w3_tlo_binding (δ p : ℝ) :
    w3_tlo_power δ p=guardTLo Plane.PR60 δ p := by
  norm_num [w3_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-94227/227200)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (71877899/57936000)*δ^1*p^1 +
  (-70324249/289680000)*δ^1*p^2
def w3_thi_minimum : ℝ := 342837948473979/3240015953920000
def w3_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(41109080744223/381178347520000:ℝ), (8225132555249/76235669504000:ℝ), (16071106967/148897792000:ℝ), (2512096797/23265280000:ℝ)],
  ![(1384530269599749/12960063815680000:ℝ), (831071263483393/7776038289408000:ℝ), (541289093293/5062524928000:ℝ), (84611461711/791019520000:ℝ)],
  ![(342837948473979/3240015953920000:ℝ), (205794751582847/1944009572352000:ℝ), (134040137427/1265631232000:ℝ), (20952908081/197754880000:ℝ)]]
theorem w3_thi_lower (i : Fin 3) (j : Fin 4) :
    w3_thi_minimum ≤ w3_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_thi_minimum,w3_thi_table]
theorem w3_thi_identity (δ p : ℝ) :
    w3_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_thi_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_thi_table,Fin.sum_univ_succ]
  ring
theorem w3_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_thi_power δ p := by
  rw [w3_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_thi_lower
theorem w3_thi_binding (δ p : ℝ) :
    w3_thi_power δ p=guardTHi Plane.PR60 δ p := by
  norm_num [w3_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-3780380501/4287264000)*δ^0*p^1 +
  (1806902401141/4139782118400)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-13736139499/3572720000)*δ^1*p^1 +
  (266284901807/93238336000)*δ^1*p^2 +
  (-322189035/431227304)*δ^1*p^3
def w3_rlo_minimum : ℝ := 54785551441461967/211956844462080000
def w3_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1217507918046444789821/4630267919555624960000:ℝ), (2723803869404637199607/10418102819000156160000:ℝ), (3526405566416277391/13565238045573120000:ℝ), (54785551441461967/211956844462080000:ℝ)],
  ![(2442736831434377140159/9260535839111249920000:ℝ), (5464917872914489517053/20836205638000312320000:ℝ), (7075269856053389189/27130476091146240000:ℝ), (2970831564438689/11457126727680000:ℝ)],
  ![(612614456693966175169/2315133959777812480000:ℝ), (1370557001754926158723/5209051409500078080000:ℝ), (1774432144818555899/6782619022786560000:ℝ), (27567608221384763/105978422231040000:ℝ)]]
theorem w3_rlo_lower (i : Fin 3) (j : Fin 4) :
    w3_rlo_minimum ≤ w3_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_rlo_minimum,w3_rlo_table]
theorem w3_rlo_identity (δ p : ℝ) :
    w3_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_rlo_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_rlo_table,Fin.sum_univ_succ]
  ring
theorem w3_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_rlo_power δ p := by
  rw [w3_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_rlo_lower
theorem w3_rlo_binding (δ p : ℝ) :
    w3_rlo_power δ p=guardRLo Plane.PR60 δ p := by
  norm_num [w3_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-334400527/115872000)*δ^0*p^1 +
  (91086437807/111886003200)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (334400527/96560000)*δ^1*p^1 +
  (-91086437807/93238336000)*δ^1*p^2
def w3_rhi_minimum : ℝ := 1655786625009601/2864281681920000
def w3_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(18341436689711958823/31285594051051520000:ℝ), (164720835603726518389/281570346459463680000:ℝ), (214022499708756557/366628055285760000:ℝ), (3336960097762109/5728563363840000:ℝ)],
  ![(36543335822190267917/62571188102103040000:ℝ), (328188511849521051431/563140692918927360000:ℝ), (426416764001301103/733256110571520000:ℝ), (6648533347781311/11457126727680000:ℝ)],
  ![(9100949566239154547/15642797025525760000:ℝ), (81733838122897266521/140785173229731840000:ℝ), (106197132146272273/183314027642880000:ℝ), (1655786625009601/2864281681920000:ℝ)]]
theorem w3_rhi_lower (i : Fin 3) (j : Fin 4) :
    w3_rhi_minimum ≤ w3_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_rhi_minimum,w3_rhi_table]
theorem w3_rhi_identity (δ p : ℝ) :
    w3_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_rhi_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_rhi_table,Fin.sum_univ_succ]
  ring
theorem w3_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_rhi_power δ p := by
  rw [w3_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_rhi_lower
theorem w3_rhi_binding (δ p : ℝ) :
    w3_rhi_power δ p=guardRHi Plane.PR60 δ p := by
  norm_num [w3_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_mlo_power (δ p : ℝ) : ℝ := (-28986249/47870000)*δ^0*p^0 +
  (686229331867/554679264000)*δ^0*p^1 +
  (-296954214022319/535598297318400)*δ^0*p^2 +
  (148661249/119675000)*δ^1*p^0 +
  (-1492095492873/577790900000)*δ^1*p^1 +
  (3251473805713/2311163600000)*δ^1*p^2 +
  (-74264746599/466191680000)*δ^1*p^3
def w3_mlo_minimum : ℝ := 156687180985717081739347/191698097564651041587200000
def w3_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(156687180985717081739347/191698097564651041587200000:ℝ), (12815624156233194025421/13478772485014526361600000:ℝ), (12684130012372120611/11700323337686220800000:ℝ), (333790911869700607/274226328227020800000:ℝ)],
  ![(475051553690768138588273/383396195129302083174400000:ℝ), (36932118994325747033839/26957544970029052723200000:ℝ), (35120038469847135329/23400646675372441600000:ℝ), (894784408141178453/548452656454041600000:ℝ)],
  ![(159182186352525528424463/95849048782325520793600000:ℝ), (12058247419046276504209/6739386242507263180800000:ℝ), (11217954228737507359/5850161668843110400000:ℝ), (280496748135738923/137113164113510400000:ℝ)]]
theorem w3_mlo_lower (i : Fin 3) (j : Fin 4) :
    w3_mlo_minimum ≤ w3_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_mlo_minimum,w3_mlo_table]
theorem w3_mlo_identity (δ p : ℝ) :
    w3_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_mlo_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_mlo_table,Fin.sum_univ_succ]
  ring
theorem w3_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_mlo_power δ p := by
  rw [w3_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_mlo_lower
theorem w3_mlo_binding (δ p : ℝ) :
    w3_mlo_power δ p=guardMLo Plane.PR60 δ p := by
  norm_num [w3_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-96420234083/72420000000)*δ^0*p^1 +
  (20479133479457/34964376000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (776363475171/301750000000)*δ^1*p^1 +
  (-5779391029/4250000000)*δ^1*p^2 +
  (20485205967317/145684900000000)*δ^1*p^3
def w3_mhi_minimum : ℝ := 169347962630542753/8950880256000000000
def w3_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(255580178910890760358397/12514237620420608000000000:ℝ), (17792616892722205283911/879907332685824000000000:ℝ), (45872566714410431863/2291425345536000000000:ℝ), (354773576093470877/17901760512000000000:ℝ)],
  ![(499731798334685583405823/25028475240841216000000000:ℝ), (34786118907102869885549/1759814665371648000000000:ℝ), (89675669226210546557/4582850691072000000000:ℝ), (693469501354556383/35803521024000000000:ℝ)],
  ![(122075809711897411523713/6257118810210304000000000:ℝ), (8496751007190332300819/439953666342912000000000:ℝ), (21901551255900057347/1145712672768000000000:ℝ), (169347962630542753/8950880256000000000:ℝ)]]
theorem w3_mhi_lower (i : Fin 3) (j : Fin 4) :
    w3_mhi_minimum ≤ w3_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_mhi_minimum,w3_mhi_table]
theorem w3_mhi_identity (δ p : ℝ) :
    w3_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_mhi_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_mhi_table,Fin.sum_univ_succ]
  ring
theorem w3_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_mhi_power δ p := by
  rw [w3_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_mhi_lower
theorem w3_mhi_binding (δ p : ℝ) :
    w3_mhi_power δ p=guardMHi Plane.PR60 δ p := by
  norm_num [w3_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_widthlo_power (δ p : ℝ) : ℝ := (66634053/95740000)*δ^0*p^0 +
  (-752854012927/554679264000)*δ^0*p^1 +
  (318307424302049/535598297318400)*δ^0*p^2 +
  (-305984053/239350000)*δ^1*p^0 +
  (2970133281981/1155581800000)*δ^1*p^1 +
  (-183119265329/135950800000)*δ^1*p^2 +
  (63160633089/466191680000)*δ^1*p^3
def w3_widthlo_minimum : ℝ := 3383411684707225747/137113164113510400000
def w3_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(5033040128698788487169483/191698097564651041587200000:ℝ), (350906777660355347816869/13478772485014526361600000:ℝ), (302025580803568383579/11700323337686220800000:ℝ), (7018346295462260423/274226328227020800000:ℝ)],
  ![(9887336584348931357388697/383396195129302083174400000:ℝ), (689314223956077389833271/26957544970029052723200000:ℝ), (593260381872572635081/23400646675372441600000:ℝ), (13785169664876711917/548452656454041600000:ℝ)],
  ![(2427148227825071435109607/95849048782325520793600000:ℝ), (169203723147861021008201/6739386242507263180800000:ℝ), (145617400534502125751/5850161668843110400000:ℝ), (3383411684707225747/137113164113510400000:ℝ)]]
theorem w3_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w3_widthlo_minimum ≤ w3_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_widthlo_minimum,w3_widthlo_table]
theorem w3_widthlo_identity (δ p : ℝ) :
    w3_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_widthlo_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w3_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_widthlo_power δ p := by
  rw [w3_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_widthlo_lower
theorem w3_widthlo_binding (δ p : ℝ) :
    w3_widthlo_power δ p=guardWidth Plane.PR60 δ p := by
  norm_num [w3_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-177786692833/217260000000)*δ^1*p^1 +
  (102871327/347616000)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (1426199824787/905250000000)*δ^2*p^1 +
  (-642888151673/905250000000)*δ^2*p^2 +
  (4787/71000)*δ^2*p^3
def w3_tail_minimum : ℝ := 5464385530583749/949223424000000000
def w3_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(121299948340122489309/19516331393024000000000:ℝ), (7501492482686727359/1219770712064000000000:ℝ), (14495705056831629/2382364672000000000:ℝ), (448130693077599/74448896000000000:ℝ)],
  ![(1009145263813303171057/165888816840704000000000:ℝ), (561596514899674354163/93312459472896000000000:ℝ), (361688442952685731/60750299136000000000:ℝ), (11179913068820401/1898446848000000000:ℝ)],
  ![(493455295524075494533/82944408420352000000000:ℝ), (274571989311766300847/46656229736448000000000:ℝ), (176808334122409759/30375149568000000000:ℝ), (5464385530583749/949223424000000000:ℝ)]]
theorem w3_tail_lower (i : Fin 3) (j : Fin 4) :
    w3_tail_minimum ≤ w3_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_tail_minimum,w3_tail_table]
theorem w3_tail_identity (δ p : ℝ) :
    w3_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_tail_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_tail_table,Fin.sum_univ_succ]
  ring
theorem w3_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_tail_power δ p := by
  rw [w3_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_tail_lower
theorem w3_tail_binding (δ p : ℝ) :
    w3_tail_power δ p=guardTail Plane.PR60 δ p := by
  norm_num [w3_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w3_monotone_power (δ p : ℝ) : ℝ := (239480527/115872000)*δ^0*p^0 +
  (-142100527/57936000)*δ^0*p^1 +
  (91086437807/111886003200)*δ^0*p^2 +
  (-721460527/289680000)*δ^1*p^0 +
  (429320527/144840000)*δ^1*p^1 +
  (-1380872038393/1398575040000)*δ^1*p^2
def w3_monotone_minimum : ℝ := 1367885463816017/2864281681920000
def w3_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(15148162308749319983/31285594051051520000:ℝ), (45352163799399770159/93856782153154560000:ℝ), (106078167268588319/219976833171456000:ℝ), (2756838966787213/5728563363840000:ℝ)],
  ![(30180555902496048997/62571188102103040000:ℝ), (90357731965160245861/187713564306309120000:ℝ), (211345663045435573/439953666342912000:ℝ), (5492609894419247/11457126727680000:ℝ)],
  ![(7516196796873364507/15642797025525760000:ℝ), (22502784082880237851/46928391076577280000:ℝ), (52633747888423627/109988416585728000:ℝ), (1367885463816017/2864281681920000:ℝ)]]
theorem w3_monotone_lower (i : Fin 3) (j : Fin 4) :
    w3_monotone_minimum ≤ w3_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w3_monotone_minimum,w3_monotone_table]
theorem w3_monotone_identity (δ p : ℝ) :
    w3_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w3_monotone_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [w3_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w3_monotone_table,Fin.sum_univ_succ]
  ring
theorem w3_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    0 < w3_monotone_power δ p := by
  rw [w3_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w3_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w3_monotone_lower
theorem w3_monotone_binding (δ p : ℝ) :
    w3_monotone_power δ p=guardMonotone Plane.PR60 δ p := by
  norm_num [w3_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window3_admissible (δ p : ℝ) (ha : window3.Available δ p) :
    Admissible window3.plane δ p := by
  have hd : δ ∈ Set.Icc (459/1024:ℝ) (231/512) := ha.1
  have hp : p ∈ Set.Icc (127/256:ℝ) (1/2) := ha.2
  change Admissible Plane.PR60 δ p
  constructor
  · rw [←w3_dn_binding]
    exact w3_dn_positive hd hp
  · rw [←w3_aa_binding]
    exact w3_aa_positive hd hp
  · rw [←w3_cc_binding]
    exact w3_cc_positive hd hp
  · rw [←w3_j_binding]
    exact w3_j_positive hd hp
  · rw [←w3_tlo_binding]
    exact w3_tlo_positive hd hp
  · rw [←w3_thi_binding]
    exact w3_thi_positive hd hp
  · rw [←w3_rlo_binding]
    exact w3_rlo_positive hd hp
  · rw [←w3_rhi_binding]
    exact w3_rhi_positive hd hp
  · rw [←w3_mlo_binding]
    exact w3_mlo_positive hd hp
  · rw [←w3_mhi_binding]
    exact w3_mhi_positive hd hp
  · rw [←w3_widthlo_binding]
    exact w3_widthlo_positive hd hp
  · rw [←w3_tail_binding]
    exact w3_tail_positive hd hp
  · rw [←w3_monotone_binding]
    exact w3_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window3_admissible
