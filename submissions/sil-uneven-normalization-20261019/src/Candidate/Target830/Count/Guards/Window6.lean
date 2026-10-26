import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w6_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-772765011/372765011)*δ^0*p^1
def w6_dn_minimum : ℝ := 1463825055/745530022
def w6_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)],
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)],
  ![(94457568531/47713921408:ℝ), (47099990097/23856960704:ℝ), (93942391857/47713921408:ℝ), (1463825055/745530022:ℝ)]]
theorem w6_dn_lower (i : Fin 3) (j : Fin 4) :
    w6_dn_minimum ≤ w6_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_dn_minimum,w6_dn_table]
theorem w6_dn_identity (δ p : ℝ) :
    w6_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_dn_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_dn_table,Fin.sum_univ_succ]
  ring
theorem w6_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_dn_power δ p := by
  rw [w6_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_dn_lower
theorem w6_dn_binding (δ p : ℝ) :
    w6_dn_power δ p=guardD Plane.C δ p := by
  norm_num [w6_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-400000000/372765011)*δ^0*p^1
def w6_aa_minimum : ℝ := 545530022/372765011
def w6_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)],
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)],
  ![(548655022/372765011:ℝ), (1642840066/1118295033:ℝ), (1639715066/1118295033:ℝ), (545530022/372765011:ℝ)]]
theorem w6_aa_lower (i : Fin 3) (j : Fin 4) :
    w6_aa_minimum ≤ w6_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_aa_minimum,w6_aa_table]
theorem w6_aa_identity (δ p : ℝ) :
    w6_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_aa_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_aa_table,Fin.sum_univ_succ]
  ring
theorem w6_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_aa_power δ p := by
  rw [w6_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_aa_lower
theorem w6_aa_binding (δ p : ℝ) :
    w6_aa_power δ p=guardA Plane.C δ p := by
  norm_num [w6_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-195798850/372765011)*δ^0*p^1
def w6_cc_minimum : ℝ := 274865586/372765011
def w6_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)],
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)],
  ![(17689296929/23856960704:ℝ), (26484995681/35785441056:ℝ), (52872091937/71570882112:ℝ), (274865586/372765011:ℝ)]]
theorem w6_cc_lower (i : Fin 3) (j : Fin 4) :
    w6_cc_minimum ≤ w6_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_cc_minimum,w6_cc_table]
theorem w6_cc_identity (δ p : ℝ) :
    w6_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_cc_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_cc_table,Fin.sum_univ_succ]
  ring
theorem w6_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_cc_power δ p := by
  rw [w6_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_cc_lower
theorem w6_cc_binding (δ p : ℝ) :
    w6_cc_power δ p=guardC Plane.C δ p := by
  norm_num [w6_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-1287941685/745530022)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (400000000/372765011)*δ^1*p^2
def w6_j_minimum : ℝ := 406929433979/381711371264
def w6_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(13271933877463/12214763880448:ℝ), (6608900056737/6107381940224:ℝ), (13163788224485/12214763880448:ℝ), (204842159539/190855685632:ℝ)],
  ![(52911350533549/48859055521792:ℝ), (26347418231291/24429527760896:ℝ), (52478813016615/48859055521792:ℝ), (816613753057/763422742528:ℝ)],
  ![(26367482778623/24429527760896:ℝ), (13129618117817/12214763880448:ℝ), (26151236567645/24429527760896:ℝ), (406929433979/381711371264:ℝ)]]
theorem w6_j_lower (i : Fin 3) (j : Fin 4) :
    w6_j_minimum ≤ w6_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_j_minimum,w6_j_table]
theorem w6_j_identity (δ p : ℝ) :
    w6_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_j_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_j_table,Fin.sum_univ_succ]
  ring
theorem w6_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_j_power δ p := by
  rw [w6_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_j_lower
theorem w6_j_binding (δ p : ℝ) :
    w6_j_power δ p=guardJ Plane.C δ p := by
  norm_num [w6_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-568563861/372765011)*δ^1*p^1 +
  (195798850/372765011)*δ^1*p^2
def w6_tlo_minimum : ℝ := 16079636781/95427842816
def w6_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(134527103145045/781744888348672:ℝ), (133589045522439/781744888348672:ℝ), (2072731343397/12214763880448:ℝ), (16079636781/95427842816:ℝ)],
  ![(541557825481335/3126979553394688:ℝ), (537781542231357/3126979553394688:ℝ), (8344072331111/48859055521792:ℝ), (64730845503/381711371264:ℝ)],
  ![(272503619191245/1563489776697344:ℝ), (270603451186479/1563489776697344:ℝ), (4198609644317/24429527760896:ℝ), (32571571941/190855685632:ℝ)]]
theorem w6_tlo_lower (i : Fin 3) (j : Fin 4) :
    w6_tlo_minimum ≤ w6_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_tlo_minimum,w6_tlo_table]
theorem w6_tlo_identity (δ p : ℝ) :
    w6_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_tlo_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_tlo_table,Fin.sum_univ_succ]
  ring
theorem w6_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_tlo_power δ p := by
  rw [w6_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_tlo_lower
theorem w6_tlo_binding (δ p : ℝ) :
    w6_tlo_power δ p=guardTLo Plane.C δ p := by
  norm_num [w6_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-643713254163/1491060044000)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (4754098847511/3727650110000)*δ^1*p^1 +
  (-95838850/372765011)*δ^1*p^2
def w6_thi_minimum : ℝ := 93254595860587383/977181110435840000
def w6_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(48586811573467023/488590555217920000:ℝ), (48631976482761729/488590555217920000:ℝ), (2433798667803603/24429527760896000:ℝ), (190307821067961/1908556856320000:ℝ)],
  ![(190428219007521429/1954362220871680000:ℝ), (190624121385371547/1954362220871680000:ℝ), (9540766083482177/97718111043584000:ℝ), (746100858829443/7634227425280000:ℝ)],
  ![(93254595860587383/977181110435840000:ℝ), (93360168419848089/977181110435840000:ℝ), (4673168747874971/48859055521792000:ℝ), (365485216693521/3817113712640000:ℝ)]]
theorem w6_thi_lower (i : Fin 3) (j : Fin 4) :
    w6_thi_minimum ≤ w6_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_thi_minimum,w6_thi_table]
theorem w6_thi_identity (δ p : ℝ) :
    w6_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_thi_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_thi_table,Fin.sum_univ_succ]
  ring
theorem w6_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_thi_power δ p := by
  rw [w6_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_thi_lower
theorem w6_thi_binding (δ p : ℝ) :
    w6_thi_power δ p=guardTHi Plane.C δ p := by
  norm_num [w6_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-24310471945/27584610814)*δ^0*p^1 +
  (2301650128018533120/5141288876755714477)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-55163398065/13792305407)*δ^1*p^1 +
  (15893629311901003644/5141288876755714477)*δ^1*p^2 +
  (-4327484061600000000/5141288876755714477)*δ^1*p^3
def w6_rlo_minimum : ℝ := 664843790974266827385/2632339904898925812224
def w6_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1409920256962923647123951/5391032125233000063434752:ℝ), (4181016294143332138131115/16173096375699000190304256:ℝ), (129146784687294748986067/505409261740593755947008:ℝ), (664843790974266827385/2632339904898925812224:ℝ)],
  ![(5674102174617227077614773/21564128500932000253739008:ℝ), (16826554600227644572456585/64692385502796000761217024:ℝ), (519765967964288526212161/2021637046962375023788032:ℝ), (2675807894677521173955/10529359619595703248896:ℝ)],
  ![(2854261660691379783366871/10782064250466000126869504:ℝ), (8464522011940980296194355/32346192751398000380608512:ℝ), (261472398589699028240027/1010818523481187511894016:ℝ), (1346120312728987519185/5264679809797851624448:ℝ)]]
theorem w6_rlo_lower (i : Fin 3) (j : Fin 4) :
    w6_rlo_minimum ≤ w6_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_rlo_minimum,w6_rlo_table]
theorem w6_rlo_identity (δ p : ℝ) :
    w6_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_rlo_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_rlo_table,Fin.sum_univ_succ]
  ring
theorem w6_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_rlo_power δ p := by
  rw [w6_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_rlo_lower
theorem w6_rlo_binding (δ p : ℝ) :
    w6_rlo_power δ p=guardRLo Plane.C δ p := by
  norm_num [w6_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-2266935935/745530022)*δ^0*p^1 +
  (126088750395031125/138953753425830121)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (1360161561/372765011)*δ^1*p^1 +
  (-151306500474037350/138953753425830121)*δ^1*p^2
def w6_rhi_minimum : ℝ := 38156678308094760645/71144321754025021952
def w6_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(160962208444856374545137/291407141904486489915392:ℝ), (480678953238102743514289/874221425713459469746176:ℝ), (7476227641740768690503/13659709776772804214784:ℝ), (19380105502705423245/35572160877012510976:ℝ)],
  ![(638836169848616822156651/1165628567617945959661568:ℝ), (1907746572194130957823147/3496885702853837878984704:ℝ), (29672086868777376083069/54638839107091216859136:ℝ), (76916889313505607135/142288643508050043904:ℝ)],
  ![(316911752958904073066377/582814283808972979830784:ℝ), (946388665717925470794569/1748442851426918939492352:ℝ), (14719631585295838702063/27319419553545608429568:ℝ), (38156678308094760645/71144321754025021952:ℝ)]]
theorem w6_rhi_lower (i : Fin 3) (j : Fin 4) :
    w6_rhi_minimum ≤ w6_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_rhi_minimum,w6_rhi_table]
theorem w6_rhi_identity (δ p : ℝ) :
    w6_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_rhi_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_rhi_table,Fin.sum_univ_succ]
  ring
theorem w6_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_rhi_power δ p := by
  rw [w6_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_rhi_lower
theorem w6_rhi_binding (δ p : ℝ) :
    w6_rhi_power δ p=guardRHi Plane.C δ p := by
  norm_num [w6_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_mlo_power (δ p : ℝ) : ℝ := (-612155921/1000000000)*δ^0*p^0 +
  (234921084425093377/186382505500000000)*δ^0*p^1 +
  (-80408245463812802801144049/138953753425830121000000000)*δ^0*p^2 +
  (3112155921/2500000000)*δ^1*p^0 +
  (-1218644907274906623/465956263750000000)*δ^1*p^1 +
  (1353886465924906623/931912527500000000)*δ^1*p^2 +
  (-576042239150560242/3473843835645753025)*δ^1*p^3
def w6_mlo_minimum : ℝ := 680137388116297481541709058629/1457035709522432449576960000000000
def w6_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(680137388116297481541709058629/1457035709522432449576960000000000:ℝ), (3110643739468085192035636047377/4371107128567297348730880000000000:ℝ), (32644610888043848495076344561/34149274441932010536960000000000:ℝ), (85349179123872194383726797/71144321754025021952000000000:ℝ)],
  ![(7668465608588441419365488516167/5828142838089729798307840000000000:ℝ), (27112139141764262637511538009291/17484428514269189394923520000000000:ℝ), (243833436327281294614971956843/136597097767728042147840000000000:ℝ), (574550505428393411125796511/284577287016100087808000000000:ℝ)],
  ![(6308190832355846456282070398909/2914071419044864899153920000000000:ℝ), (20890851662828092253440265914537/8742214257134594697461760000000000:ℝ), (178544214551193597624819267721/68298548883864021073920000000000:ℝ), (403852147180649022358342917/142288643508050043904000000000:ℝ)]]
theorem w6_mlo_lower (i : Fin 3) (j : Fin 4) :
    w6_mlo_minimum ≤ w6_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_mlo_minimum,w6_mlo_table]
theorem w6_mlo_identity (δ p : ℝ) :
    w6_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_mlo_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_mlo_table,Fin.sum_univ_succ]
  ring
theorem w6_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_mlo_power δ p := by
  rw [w6_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_mlo_lower
theorem w6_mlo_binding (δ p : ℝ) :
    w6_mlo_power δ p=guardMLo Plane.C δ p := by
  norm_num [w6_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-6287390142794251/4659562637500000)*δ^0*p^1 +
  (2116941220965473617000587/3473843835645753025000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (30373484644705749/11648906593750000)*δ^1*p^1 +
  (-32789348625955749/23297813187500000)*δ^1*p^2 +
  (101948830800770718/694768767129150605)*δ^1*p^3
def w6_mhi_minimum : ℝ := 53784714372192022071504729/3557216087701251097600000000
def w6_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1310411752692601564748631669871/72851785476121622478848000000000:ℝ), (1925136988480039814154375353749/109277678214182433718272000000000:ℝ), (14725010059004698051462773157/853731861048300263424000000000:ℝ), (30023014661323327230260289/1778608043850625548800000000:ℝ)],
  ![(4976383785703888756619220289333/291407141904486489915392000000000:ℝ), (7307083991947945098577840010167/437110712856729734873088000000000:ℝ), (55860476880611856253957740391/3414927444193201053696000000000:ℝ), (113830743694838676532025307/7114432175402502195200000000:ℝ)],
  ![(2355560280318685627121956949591/145703570952243244957696000000000:ℝ), (3456810014987865470269089302669/218555356428364867436544000000000:ℝ), (26410456762602460151032194077/1707463722096600526848000000000:ℝ), (53784714372192022071504729/3557216087701251097600000000:ℝ)]]
theorem w6_mhi_lower (i : Fin 3) (j : Fin 4) :
    w6_mhi_minimum ≤ w6_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_mhi_minimum,w6_mhi_table]
theorem w6_mhi_identity (δ p : ℝ) :
    w6_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_mhi_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_mhi_table,Fin.sum_univ_succ]
  ring
theorem w6_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_mhi_power δ p := by
  rw [w6_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_mhi_lower
theorem w6_mhi_binding (δ p : ℝ) :
    w6_mhi_power δ p=guardMHi Plane.C δ p := by
  norm_num [w6_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_widthlo_power (δ p : ℝ) : ℝ := (5565906092767/8000000000000)*δ^0*p^0 +
  (-2051607364334019258479/1491060044000000000000)*δ^0*p^1 +
  (687632641159884323317578759423/1111630027406640968000000000000)*δ^0*p^2 +
  (-25565906092767/20000000000000)*δ^1*p^0 +
  (9710652314219380741521/3727650110000000000000)*δ^1*p^1 +
  (-10391389548559180741521/7455300220000000000000)*δ^1*p^2 +
  (979845789367848241521/6947687671291506050000)*δ^1*p^3
def w6_widthlo_minimum : ℝ := 23322668396327491368161886457941/1138309148064400351232000000000000
def w6_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(273976806055137901928294990932567417/11656285676179459596615680000000000000:ℝ), (807663543181461360879473698480383521/34968857028538378789847040000000000000:ℝ), (6198837957503968750843270585677953/273194195535456084295680000000000000:ℝ), (12683832016127992127747716481181/569154574032200175616000000000000:ℝ)],
  ![(1052610411283522497149478623400042691/46625142704717838386462720000000000000:ℝ), (3102188911516977498422350663760453243/139875428114153515159388160000000000000:ℝ), (23802773954377526220654245729424539/1092776782141824337182720000000000000:ℝ), (48690332428583475623657319420303/2276618296128800702464000000000000:ℝ)],
  ![(504656799173246693292888641534907857/23312571352358919193231360000000000000:ℝ), (1486861825154054776663403266799686201/69937714057076757579694080000000000000:ℝ), (11405098039369588718967704558068633/546388391070912168591360000000000000:ℝ), (23322668396327491368161886457941/1138309148064400351232000000000000:ℝ)]]
theorem w6_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w6_widthlo_minimum ≤ w6_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_widthlo_minimum,w6_widthlo_table]
theorem w6_widthlo_identity (δ p : ℝ) :
    w6_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_widthlo_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w6_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_widthlo_power δ p := by
  rw [w6_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_widthlo_lower
theorem w6_widthlo_binding (δ p : ℝ) :
    w6_widthlo_power δ p=guardWidth Plane.C δ p := by
  norm_num [w6_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-3899358951306417/4659562637500000)*δ^1*p^1 +
  (35812707313/111829503300)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (18756998265080749/11648906593750000)*δ^2*p^1 +
  (-70580026487/93191252750)*δ^2*p^2 +
  (27200000/372765011)*δ^2*p^3
def w6_tail_minimum : ℝ := 27665789854316889843/6107381940224000000000
def w6_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(8492574869480215439601/1563489776697344000000000:ℝ), (8302400409431411850723/1563489776697344000000000:ℝ), (101407066639911310109/19543622208716800000000:ℝ), (7737383786820456483/1526845485056000000000:ℝ)],
  ![(16133887060967890666441/3126979553394688000000000:ℝ), (15761105921958862764523/3126979553394688000000000:ℝ), (577085721030847732543/117261733252300800000000:ℝ), (14665478510542430763/3053690970112000000000:ℝ)],
  ![(30516010722720655968481/6253959106789376000000000:ℝ), (29786097130735746873523/6253959106789376000000000:ℝ), (1089650035695610959079/234523466504601600000000:ℝ), (27665789854316889843/6107381940224000000000:ℝ)]]
theorem w6_tail_lower (i : Fin 3) (j : Fin 4) :
    w6_tail_minimum ≤ w6_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_tail_minimum,w6_tail_table]
theorem w6_tail_identity (δ p : ℝ) :
    w6_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_tail_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_tail_table,Fin.sum_univ_succ]
  ring
theorem w6_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_tail_power δ p := by
  rw [w6_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_tail_lower
theorem w6_tail_binding (δ p : ℝ) :
    w6_tail_power δ p=guardTail Plane.C δ p := by
  norm_num [w6_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w6_monotone_power (δ p : ℝ) : ℝ := (777438810/372765011)*δ^0*p^0 +
  (-978994250/372765011)*δ^0*p^1 +
  (126088750395031125/138953753425830121)*δ^0*p^2 +
  (-941328872/372765011)*δ^1*p^0 +
  (1191597700/372765011)*δ^1*p^1 +
  (-154438583925962650/138953753425830121)*δ^1*p^2
def w6_monotone_minimum : ℝ := 62836451169231179107/142288643508050043904
def w6_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(132496930479467883024207/291407141904486489915392:ℝ), (395732956442576884005071/874221425713459469746176:ℝ), (3077986141794070422707/6829854888386402107392:ℝ), (31920459029915042267/71144321754025021952:ℝ)],
  ![(525817562385704681010261/1165628567617945959661568:ℝ), (1570477441979956606162133/3496885702853837878984704:ℝ), (12215081124660053601761/27319419553545608429568:ℝ), (126677369229061263641/284577287016100087808:ℝ)],
  ![(260823701426768914961847/582814283808972979830784:ℝ), (779011529094802838151991/1748442851426918939492352:ℝ), (6059108841071912756347/13659709776772804214784:ℝ), (62836451169231179107/142288643508050043904:ℝ)]]
theorem w6_monotone_lower (i : Fin 3) (j : Fin 4) :
    w6_monotone_minimum ≤ w6_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w6_monotone_minimum,w6_monotone_table]
theorem w6_monotone_identity (δ p : ℝ) :
    w6_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w6_monotone_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w6_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w6_monotone_table,Fin.sum_univ_succ]
  ring
theorem w6_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w6_monotone_power δ p := by
  rw [w6_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w6_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w6_monotone_lower
theorem w6_monotone_binding (δ p : ℝ) :
    w6_monotone_power δ p=guardMonotone Plane.C δ p := by
  norm_num [w6_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window6_admissible (δ p : ℝ) (ha : window6.Available δ p) :
    Admissible window6.plane δ p := by
  have hd : δ ∈ Set.Icc (117/256:ℝ) (237/512) := ha.1
  have hp : p ∈ Set.Icc (63/128:ℝ) (1/2) := ha.2
  change Admissible Plane.C δ p
  constructor
  · rw [←w6_dn_binding]
    exact w6_dn_positive hd hp
  · rw [←w6_aa_binding]
    exact w6_aa_positive hd hp
  · rw [←w6_cc_binding]
    exact w6_cc_positive hd hp
  · rw [←w6_j_binding]
    exact w6_j_positive hd hp
  · rw [←w6_tlo_binding]
    exact w6_tlo_positive hd hp
  · rw [←w6_thi_binding]
    exact w6_thi_positive hd hp
  · rw [←w6_rlo_binding]
    exact w6_rlo_positive hd hp
  · rw [←w6_rhi_binding]
    exact w6_rhi_positive hd hp
  · rw [←w6_mlo_binding]
    exact w6_mlo_positive hd hp
  · rw [←w6_mhi_binding]
    exact w6_mhi_positive hd hp
  · rw [←w6_widthlo_binding]
    exact w6_widthlo_positive hd hp
  · rw [←w6_tail_binding]
    exact w6_tail_positive hd hp
  · rw [←w6_monotone_binding]
    exact w6_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window6_admissible
