import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w2_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-9615/4828)*δ^0*p^1
def w2_dn_minimum : ℝ := 19353/9656
def w2_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(291999/145408:ℝ), (2480389/1235968:ℝ), (4957573/2471936:ℝ), (19353/9656:ℝ)],
  ![(291999/145408:ℝ), (2480389/1235968:ℝ), (4957573/2471936:ℝ), (19353/9656:ℝ)],
  ![(291999/145408:ℝ), (2480389/1235968:ℝ), (4957573/2471936:ℝ), (19353/9656:ℝ)]]
theorem w2_dn_lower (i : Fin 3) (j : Fin 4) :
    w2_dn_minimum ≤ w2_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_dn_minimum,w2_dn_table]
theorem w2_dn_identity (δ p : ℝ) :
    w2_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_dn_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_dn_table,Fin.sum_univ_succ]
  ring
theorem w2_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_dn_power δ p := by
  rw [w2_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_dn_lower
theorem w2_dn_binding (δ p : ℝ) :
    w2_dn_power δ p=guardD Plane.PR60 δ p := by
  norm_num [w2_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-4787/4828)*δ^0*p^1
def w2_aa_minimum : ℝ := 14525/9656
def w2_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(219011/145408:ℝ), (5582387/3707904:ℝ), (11159987/7415808:ℝ), (14525/9656:ℝ)],
  ![(219011/145408:ℝ), (5582387/3707904:ℝ), (11159987/7415808:ℝ), (14525/9656:ℝ)],
  ![(219011/145408:ℝ), (5582387/3707904:ℝ), (11159987/7415808:ℝ), (14525/9656:ℝ)]]
theorem w2_aa_lower (i : Fin 3) (j : Fin 4) :
    w2_aa_minimum ≤ w2_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_aa_minimum,w2_aa_table]
theorem w2_aa_identity (δ p : ℝ) :
    w2_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_aa_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_aa_table,Fin.sum_univ_succ]
  ring
theorem w2_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_aa_power δ p := by
  rw [w2_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_aa_lower
theorem w2_aa_binding (δ p : ℝ) :
    w2_aa_power δ p=guardA Plane.PR60 δ p := by
  norm_num [w2_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-142100527/289680000)*δ^0*p^1
def w2_cc_minimum : ℝ := 437259473/579360000
def w2_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(439531473/581632000:ℝ), (168049738159/222474240000:ℝ), (335957375791/444948480000:ℝ), (437259473/579360000:ℝ)],
  ![(439531473/581632000:ℝ), (168049738159/222474240000:ℝ), (335957375791/444948480000:ℝ), (437259473/579360000:ℝ)],
  ![(439531473/581632000:ℝ), (168049738159/222474240000:ℝ), (335957375791/444948480000:ℝ), (437259473/579360000:ℝ)]]
theorem w2_cc_lower (i : Fin 3) (j : Fin 4) :
    w2_cc_minimum ≤ w2_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_cc_minimum,w2_cc_table]
theorem w2_cc_identity (δ p : ℝ) :
    w2_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_cc_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_cc_table,Fin.sum_univ_succ]
  ring
theorem w2_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_cc_power δ p := by
  rw [w2_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_cc_lower
theorem w2_cc_binding (δ p : ℝ) :
    w2_cc_power δ p=guardC Plane.PR60 δ p := by
  norm_num [w2_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-16025/9656)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (4787/4828)*δ^1*p^2
def w2_j_minimum : ℝ := 21930041/19775488
def w2_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(10633632043/9529458688:ℝ), (541788384731/486002393088:ℝ), (1057151969/949223424:ℝ), (2750323/2471936:ℝ)],
  ![(169858459705/152471339008:ℝ), (8654351761865/7776038289408:ℝ), (16886575115/15187574784:ℝ), (43932625/39550976:ℝ)],
  ![(84789403361/76235669504:ℝ), (4320044684017/3888019144704:ℝ), (8429359363/7593787392:ℝ), (21930041/19775488:ℝ)]]
theorem w2_j_lower (i : Fin 3) (j : Fin 4) :
    w2_j_minimum ≤ w2_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_j_minimum,w2_j_table]
theorem w2_j_identity (δ p : ℝ) :
    w2_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_j_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_j_table,Fin.sum_univ_succ]
  ring
theorem w2_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_j_power δ p := by
  rw [w2_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_j_lower
theorem w2_j_binding (δ p : ℝ) :
    w2_j_power δ p=guardJ Plane.PR60 δ p := by
  norm_num [w2_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-431780527/289680000)*δ^1*p^1 +
  (142100527/289680000)*δ^1*p^2
def w2_tlo_minimum : ℝ := 8307929987/49438720000
def w2_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(6438696547977/38117834752000:ℝ), (1639044212874109/9720047861760000:ℝ), (1040282889/6179840000:ℝ), (8307929987/49438720000:ℝ)],
  ![(20671604706663/121977071206400:ℝ), (5262194578174771/31104153157632000:ℝ), (3339855591/19775488000:ℝ), (26672827853/158203904000:ℝ)],
  ![(51848451149499/304942678016000:ℝ), (258796454664333/1524713390080000:ℝ), (492765579/2908160000:ℝ), (3935335257/23265280000:ℝ)]]
theorem w2_tlo_lower (i : Fin 3) (j : Fin 4) :
    w2_tlo_minimum ≤ w2_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_tlo_minimum,w2_tlo_table]
theorem w2_tlo_identity (δ p : ℝ) :
    w2_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_tlo_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_tlo_table,Fin.sum_univ_succ]
  ring
theorem w2_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_tlo_power δ p := by
  rw [w2_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_tlo_lower
theorem w2_tlo_binding (δ p : ℝ) :
    w2_tlo_power δ p=guardTLo Plane.PR60 δ p := by
  norm_num [w2_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-94227/227200)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (71877899/57936000)*δ^1*p^1 +
  (-70324249/289680000)*δ^1*p^2
def w2_thi_minimum : ℝ := 164535182250783/1524713390080000
def w2_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(20953410211029/190589173760000:ℝ), (1068814134011429/9720047861760000:ℝ), (347982751009/3164078080000:ℝ), (5438184367/49438720000:ℝ)],
  ![(66432492787803/609885356032000:ℝ), (3388695442985483/31104153157632000:ℝ), (1103297351567/10125049856000:ℝ), (17242224097/158203904000:ℝ)],
  ![(164535182250783/1524713390080000:ℝ), (164567924369333/1524713390080000:ℝ), (160742632339/1488977920000:ℝ), (2512096797/23265280000:ℝ)]]
theorem w2_thi_lower (i : Fin 3) (j : Fin 4) :
    w2_thi_minimum ≤ w2_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_thi_minimum,w2_thi_table]
theorem w2_thi_identity (δ p : ℝ) :
    w2_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_thi_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_thi_table,Fin.sum_univ_succ]
  ring
theorem w2_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_thi_power δ p := by
  rw [w2_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_thi_lower
theorem w2_thi_binding (δ p : ℝ) :
    w2_thi_power δ p=guardTHi Plane.PR60 δ p := by
  norm_num [w2_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-3780380501/4287264000)*δ^0*p^1 +
  (1806902401141/4139782118400)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-13736139499/3572720000)*δ^1*p^1 +
  (266284901807/93238336000)*δ^1*p^2 +
  (-322189035/431227304)*δ^1*p^3
def w2_rlo_minimum : ℝ := 6804485805019301/26494605557760000
def w2_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(830074125298469439/3204337660592128000:ℝ), (79148446887897735053/306414788794122240000:ℝ), (873480446920665637/3391309511393280000:ℝ), (6804485805019301/26494605557760000:ℝ)],
  ![(106589626198675449/410155220555792384:ℝ), (10163468715588174043/39221092965647646720:ℝ), (112164195472281347/434087617458339840:ℝ), (873771503052931/3391309511393280:ℝ)],
  ![(6683110272446675613/25634701284737024000:ℝ), (637246014345339874951/2451318310352977920000:ℝ), (7032680858669843279/27130476091146240000:ℝ), (54785551441461967/211956844462080000:ℝ)]]
theorem w2_rlo_lower (i : Fin 3) (j : Fin 4) :
    w2_rlo_minimum ≤ w2_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_rlo_minimum,w2_rlo_table]
theorem w2_rlo_identity (δ p : ℝ) :
    w2_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_rlo_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_rlo_table,Fin.sum_univ_succ]
  ring
theorem w2_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_rlo_power δ p := by
  rw [w2_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_rlo_lower
theorem w2_rlo_binding (δ p : ℝ) :
    w2_rlo_power δ p=guardRLo Plane.PR60 δ p := by
  norm_num [w2_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-334400527/115872000)*δ^0*p^1 +
  (91086437807/111886003200)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (334400527/96560000)*δ^1*p^1 +
  (-91086437807/93238336000)*δ^1*p^2
def w2_rhi_minimum : ℝ := 3336960097762109/5728563363840000
def w2_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(6374356612364841/10825465069568000:ℝ), (4871173538081417431/8281480778219520000:ℝ), (53855117454661199/91657013821440000:ℝ), (420293368188127/716070420480000:ℝ)],
  ![(812837420368671/1385659528904704:ℝ), (621156357205012961/1060029539612098560:ℝ), (6867431084822569/11732097769144320:ℝ), (53594456346137/91657013821440:ℝ)],
  ![(50609824647165147/86603720556544000:ℝ), (38675156345975280677/66251846225756160000:ℝ), (427587945965531533/733256110571520000:ℝ), (3336960097762109/5728563363840000:ℝ)]]
theorem w2_rhi_lower (i : Fin 3) (j : Fin 4) :
    w2_rhi_minimum ≤ w2_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_rhi_minimum,w2_rhi_table]
theorem w2_rhi_identity (δ p : ℝ) :
    w2_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_rhi_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_rhi_table,Fin.sum_univ_succ]
  ring
theorem w2_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_rhi_power δ p := by
  rw [w2_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_rhi_lower
theorem w2_rhi_binding (δ p : ℝ) :
    w2_rhi_power δ p=guardRHi Plane.PR60 δ p := by
  norm_num [w2_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_mlo_power (δ p : ℝ) : ℝ := (-28986249/47870000)*δ^0*p^0 +
  (686229331867/554679264000)*δ^0*p^1 +
  (-296954214022319/535598297318400)*δ^0*p^2 +
  (148661249/119675000)*δ^1*p^0 +
  (-1492095492873/577790900000)*δ^1*p^1 +
  (3251473805713/2311163600000)*δ^1*p^2 +
  (-74264746599/466191680000)*δ^1*p^3
def w2_mlo_minimum : ℝ := 120363778741098860401/663315216486681804800000
def w2_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(120363778741098860401/663315216486681804800000:ℝ), (99337654096069869791/396434484853368422400000:ℝ), (2805045077212733827/8775242503264665600000:ℝ), (13323540933490421/34278291028377600000:ℝ)],
  ![(1272356622333788133887/2122608692757381775360000:ℝ), (846544371317924546353/1268590351530778951680000:ℝ), (20643597474827982029/28080776010446929920000:ℝ), (17615169573504959/21938106258161664000:ℝ)],
  ![(5398872881740149786227/5306521731893454438400000:ℝ), (3438020623821063773437/3171475878826947379200000:ℝ), (80777626756438039529/70201940026117324800000:ℝ), (333790911869700607/274226328227020800000:ℝ)]]
theorem w2_mlo_lower (i : Fin 3) (j : Fin 4) :
    w2_mlo_minimum ≤ w2_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_mlo_minimum,w2_mlo_table]
theorem w2_mlo_identity (δ p : ℝ) :
    w2_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_mlo_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_mlo_table,Fin.sum_univ_succ]
  ring
theorem w2_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_mlo_power δ p := by
  rw [w2_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_mlo_lower
theorem w2_mlo_binding (δ p : ℝ) :
    w2_mlo_power δ p=guardMLo Plane.PR60 δ p := by
  norm_num [w2_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-96420234083/72420000000)*δ^0*p^1 +
  (20479133479457/34964376000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (776363475171/301750000000)*δ^1*p^1 +
  (-5779391029/4250000000)*δ^1*p^2 +
  (20485205967317/145684900000000)*δ^1*p^3
def w2_mhi_minimum : ℝ := 354773576093470877/17901760512000000000
def w2_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(910459339356046239231/43301860278272000000000:ℝ), (541465375155848290621/25879627431936000000000:ℝ), (11926373495441293597/572856336384000000000:ℝ), (46356403365732031/2237720064000000000:ℝ)],
  ![(2850722950535854084497/138565952890470400000000:ℝ), (1695292587796836059123/82814807782195200000000:ℝ), (37338914483581010579/1833140276428800000000:ℝ), (5804998424154617/286428168192000000:ℝ)],
  ![(6969940037830900508637/346414882226176000000000:ℝ), (4144739937737393970647/207037019455488000000000:ℝ), (91283584454374704119/4582850691072000000000:ℝ), (354773576093470877/17901760512000000000:ℝ)]]
theorem w2_mhi_lower (i : Fin 3) (j : Fin 4) :
    w2_mhi_minimum ≤ w2_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_mhi_minimum,w2_mhi_table]
theorem w2_mhi_identity (δ p : ℝ) :
    w2_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_mhi_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_mhi_table,Fin.sum_univ_succ]
  ring
theorem w2_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_mhi_power δ p := by
  rw [w2_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_mhi_lower
theorem w2_mhi_binding (δ p : ℝ) :
    w2_mhi_power δ p=guardMHi Plane.PR60 δ p := by
  norm_num [w2_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_widthlo_power (δ p : ℝ) : ℝ := (66634053/95740000)*δ^0*p^0 +
  (-752854012927/554679264000)*δ^0*p^1 +
  (318307424302049/535598297318400)*δ^0*p^2 +
  (-305984053/239350000)*δ^1*p^0 +
  (2970133281981/1155581800000)*δ^1*p^1 +
  (-183119265329/135950800000)*δ^1*p^2 +
  (63160633089/466191680000)*δ^1*p^3
def w2_widthlo_minimum : ℝ := 7018346295462260423/274226328227020800000
def w2_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(17809112369893310721689/663315216486681804800000:ℝ), (10598997174121388959399/396434484853368422400000:ℝ), (233624042745960803003/8775242503264665600000:ℝ), (908733652688758669/34278291028377600000:ℝ)],
  ![(56007661900206252153943/2122608692757381775360000:ℝ), (33331801042668786192617/1268590351530778951680000:ℝ), (734683482039512181781/28080776010446929920000:ℝ), (571528620678893191/21938106258161664000:ℝ)],
  ![(137565410541884774996203/5306521731893454438400000:ℝ), (81867027820372819287893/3171475878826947379200000:ℝ), (1804425068229874484881/70201940026117324800000:ℝ), (7018346295462260423/274226328227020800000:ℝ)]]
theorem w2_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w2_widthlo_minimum ≤ w2_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_widthlo_minimum,w2_widthlo_table]
theorem w2_widthlo_identity (δ p : ℝ) :
    w2_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_widthlo_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w2_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_widthlo_power δ p := by
  rw [w2_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_widthlo_lower
theorem w2_widthlo_binding (δ p : ℝ) :
    w2_widthlo_power δ p=guardWidth Plane.PR60 δ p := by
  norm_num [w2_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-177786692833/217260000000)*δ^1*p^1 +
  (102871327/347616000)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (1426199824787/905250000000)*δ^2*p^1 +
  (-642888151673/905250000000)*δ^2*p^2 +
  (4787/71000)*δ^2*p^3
def w2_tail_minimum : ℝ := 448130693077599/74448896000000000
def w2_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(15558558482554231749/2439541424128000000000:ℝ), (74001727210358917807/11664057434112000000000:ℝ), (7987658287338901/1265631232000000000:ℝ), (372451546243781/59326464000000000:ℝ)],
  ![(121946817851151157743/19516331393024000000000:ℝ), (579983366209916610829/93312459472896000000000:ℝ), (62598715653843007/10125049856000000000:ℝ), (41108282669497/6684672000000000:ℝ)],
  ![(955092807391913629101/156130651144192000000000:ℝ), (29687267736265697471/4879082848256000000000:ℝ), (28835887235314797/4764729344000000000:ℝ), (448130693077599/74448896000000000:ℝ)]]
theorem w2_tail_lower (i : Fin 3) (j : Fin 4) :
    w2_tail_minimum ≤ w2_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_tail_minimum,w2_tail_table]
theorem w2_tail_identity (δ p : ℝ) :
    w2_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_tail_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_tail_table,Fin.sum_univ_succ]
  ring
theorem w2_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_tail_power δ p := by
  rw [w2_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_tail_lower
theorem w2_tail_binding (δ p : ℝ) :
    w2_tail_power δ p=guardTail Plane.PR60 δ p := by
  norm_num [w2_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w2_monotone_power (δ p : ℝ) : ℝ := (239480527/115872000)*δ^0*p^0 +
  (-142100527/57936000)*δ^0*p^1 +
  (91086437807/111886003200)*δ^0*p^2 +
  (-721460527/289680000)*δ^1*p^0 +
  (429320527/144840000)*δ^1*p^1 +
  (-1380872038393/1398575040000)*δ^1*p^2
def w2_monotone_minimum : ℝ := 2756838966787213/5728563363840000
def w2_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1342716960915274591/2760493592739840000:ℝ), (4024054343247359327/8281480778219520000:ℝ), (133475292367823273/274971041464320000:ℝ), (347238375742799/716070420480000:ℝ)],
  ![(4280400561347274737/8833579496767488000:ℝ), (12828142813917074929/26500738490302464000:ℝ), (85100250276346907/175981466537164800:ℝ), (1106949194545921/2291425345536000:ℝ)],
  ![(10660267119414176957/22083948741918720000:ℝ), (31948279323606500029/66251846225756160000:ℝ), (1059703917966086491/2199768331714560000:ℝ), (2756838966787213/5728563363840000:ℝ)]]
theorem w2_monotone_lower (i : Fin 3) (j : Fin 4) :
    w2_monotone_minimum ≤ w2_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w2_monotone_minimum,w2_monotone_table]
theorem w2_monotone_identity (δ p : ℝ) :
    w2_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w2_monotone_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [w2_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w2_monotone_table,Fin.sum_univ_succ]
  ring
theorem w2_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    0 < w2_monotone_power δ p := by
  rw [w2_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w2_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w2_monotone_lower
theorem w2_monotone_binding (δ p : ℝ) :
    w2_monotone_power δ p=guardMonotone Plane.PR60 δ p := by
  norm_num [w2_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window2_admissible (δ p : ℝ) (ha : window2.Available δ p) :
    Admissible window2.plane δ p := by
  have hd : δ ∈ Set.Icc (57/128:ℝ) (459/1024) := ha.1
  have hp : p ∈ Set.Icc (255/512:ℝ) (1/2) := ha.2
  change Admissible Plane.PR60 δ p
  constructor
  · rw [←w2_dn_binding]
    exact w2_dn_positive hd hp
  · rw [←w2_aa_binding]
    exact w2_aa_positive hd hp
  · rw [←w2_cc_binding]
    exact w2_cc_positive hd hp
  · rw [←w2_j_binding]
    exact w2_j_positive hd hp
  · rw [←w2_tlo_binding]
    exact w2_tlo_positive hd hp
  · rw [←w2_thi_binding]
    exact w2_thi_positive hd hp
  · rw [←w2_rlo_binding]
    exact w2_rlo_positive hd hp
  · rw [←w2_rhi_binding]
    exact w2_rhi_positive hd hp
  · rw [←w2_mlo_binding]
    exact w2_mlo_positive hd hp
  · rw [←w2_mhi_binding]
    exact w2_mhi_positive hd hp
  · rw [←w2_widthlo_binding]
    exact w2_widthlo_positive hd hp
  · rw [←w2_tail_binding]
    exact w2_tail_positive hd hp
  · rw [←w2_monotone_binding]
    exact w2_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window2_admissible
